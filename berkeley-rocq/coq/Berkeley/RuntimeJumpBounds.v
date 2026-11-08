(** Checked lower bounds discharge the PC guards of every control jump. *)
From Stdlib Require Import Lists.List Streams.Streams Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From Berkeley Require Import FiniteMachine Data Machine RuntimeTape RuntimeRegisters
  RuntimeControl RuntimeCalls RuntimeProgramData RuntimeProgram RuntimeSimulation RuntimeJumps.
Import ListNotations.

Definition bit_rank (b : bool) q := nth q (if b then node_min_ones else node_min_zeros) 0.
Definition bit_count (b : bool) w := if b then ones w else zeros w.
Definition rank_edge b q a := match lookup new_table q a with
  | Some (_,R,t) => Nat.leb (bit_rank b t) ((if Bool.eqb a b then 1 else 0)+bit_rank b q)
  | _ => true end.
Definition rank_node q := if node q then
  andb (andb (rank_edge false q false) (rank_edge false q true))
       (andb (rank_edge true q false) (rank_edge true q true)) else true.
Lemma rank_certificate : forallb rank_node (seq 0 new_count) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rank_edge_sound b q a t : node q = true -> lookup new_table q a = Some(a,R,t) ->
  bit_rank b t <= (if Bool.eqb a b then 1 else 0)+bit_rank b q.
Proof.
  intros N E. pose proof rank_certificate as C. rewrite forallb_forall in C.
  assert (I : In q (seq 0 new_count)) by (apply in_seq; pose proof (node_in_range q N); lia).
  specialize (C q I). unfold rank_node in C. rewrite N in C.
  repeat rewrite andb_true_iff in C. destruct C as [[C00 C01] [C10 C11]].
  assert (H : rank_edge b q a = true) by (destruct b,a; assumption).
  unfold rank_edge in H. rewrite E in H. now apply Nat.leb_le.
Qed.
Lemma read_path_rank b q w out : ReadPath q w out ->
  bit_rank b out <= bit_count b w + bit_rank b q.
Proof.
  intro P. induction P.
  - destruct b; cbn [bit_count ones zeros]; lia.
  - pose proof (rank_edge_sound b q b0 t H H0) as E.
    destruct b,b0; cbn [bit_count ones zeros Bool.eqb] in *; lia.
Qed.
Lemma root_path_rank b w out : ReadPath 72 w out -> bit_rank b out <= bit_count b w.
Proof.
  intro P. pose proof (read_path_rank b _ _ _ P) as H.
  assert (E : bit_rank b 72 = 0) by (destruct b; reflexivity).
  rewrite E in H. lia.
Qed.

Definition jump_guard q a := match lookup new_table q a with
  | Some (w,L,t) => andb a (andb (negb w)
      (orb (existsb (fun k => andb (Nat.eqb t (continue_state k))
                                   (Nat.leb k (bit_rank true q))) [0;1;2;3])
           (existsb (fun k => andb (Nat.eqb t (break_state k))
                                   (Nat.leb k (bit_rank false q))) [0;1;2])))
  | _ => true end.
Definition jump_node q := if node q then andb (jump_guard q false) (jump_guard q true) else true.
Lemma jump_certificate : forallb jump_node (seq 0 new_count) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma jump_guard_sound q a w t : node q = true -> lookup new_table q a = Some(w,L,t) ->
  a=true /\ w=false /\
  ((exists k, k<=3 /\ t=continue_state k /\ k<=bit_rank true q) \/
   (exists k, k<=2 /\ t=break_state k /\ k<=bit_rank false q)).
Proof.
  intros N E. pose proof jump_certificate as C. rewrite forallb_forall in C.
  assert (I : In q (seq 0 new_count)) by (apply in_seq; pose proof (node_in_range q N); lia).
  specialize (C q I). unfold jump_node in C. rewrite N in C.
  apply andb_true_iff in C as [C0 C1].
  assert (H : jump_guard q a = true) by (destruct a; assumption).
  unfold jump_guard in H. rewrite E in H.
  apply andb_true_iff in H as [A H]. apply andb_true_iff in H as [W H].
  apply negb_true_iff in W. split; [exact A|]. split; [exact W|].
  apply orb_true_iff in H as [H|H].
  - left. apply existsb_exists in H as [k [K H]]. apply andb_true_iff in H as [T B].
    apply Nat.eqb_eq in T. apply Nat.leb_le in B.
    exists k. split; [simpl in K; lia|auto].
  - right. apply existsb_exists in H as [k [K H]]. apply andb_true_iff in H as [T B].
    apply Nat.eqb_eq in T. apply Nat.leb_le in B.
    exists k. split; [simpl in K; lia|auto].
Qed.

Theorem control_jump_total width w q a written target rs :
  length (w++[a]) <= width -> ReadPath 72 w q -> node q=true ->
  lookup new_table q a = Some(written,L,target) ->
  exists w', length w' <= width /\
    Runs (normal width (w++[a]) rs) (normal width w' rs) /\
    (New.halts new_tm (normal width (w++[a]) rs) <->
     New.halts new_tm (normal width w' rs)).
Proof.
  intros HW P N E. destruct (jump_guard_sound _ _ _ _ N E) as [A [W [C|C]]];
    subst a written; destruct C as [k [HK [T B]]]; subst target.
  - pose proof (root_path_rank true _ _ P) as HP.
    change (bit_rank true q <= ones w) in HP.
    assert (O : ones (rev w) = ones w).
    { pose proof (ones_zeros (rev w)). pose proof (ones_zeros w).
      rewrite zeros_rev,rev_length in H. lia. }
    destruct (continue_pc_total k (rev w) ltac:(rewrite O; lia)) as [out [n F]].
    exists (rev out). pose proof (continue_jump_simulation width w q k out n rs HW P E HK F) as R.
    split.
    + pose proof (continue_pc_bounds _ _ _ _ F) as [_ HL].
      rewrite rev_length in *. rewrite app_length in HW. simpl in HW. lia.
    + split; [exact R|apply runs_preserve_halting,R].
  - pose proof (root_path_rank false _ _ P) as HP.
    change (bit_rank false q <= zeros w) in HP.
    destruct (break_pc_total k (rev w++[false])
      ltac:(rewrite zeros_app,zeros_rev; simpl; lia)) as [out [n F]].
    exists (return_word out). pose proof (break_jump_simulation width w q k out n rs HW P E HK F) as R.
    split.
    + pose proof (return_word_bound _ _ _ _ F) as [_ HL].
      rewrite app_length in HW. simpl in HW. lia.
    + split; [exact R|apply runs_preserve_halting,R].
Qed.

Print Assumptions rank_certificate.
Print Assumptions jump_certificate.
Print Assumptions control_jump_total.
