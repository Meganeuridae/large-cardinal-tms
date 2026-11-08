(** Read-only decision traversal and bounds for the actual compiled program. *)
From Stdlib Require Import Lists.List Streams.Streams Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From Berkeley Require Import FiniteMachine Data Machine RuntimeTape RuntimeRegisters
  RuntimeControl RuntimeProgramData.
Import ListNotations.

Definition node q := nth q node_flags false.
Definition height q := nth q node_heights 0.
Definition zero_bound q := nth q node_zeros 0.
Definition terminal q := existsb (Nat.eqb q)
  [4;87;195;171;131;143;149;156;103;138;329;
   32;84;166;169;81;89;100;107;95;117;363;1385].
Definition admissible q := orb (node q) (terminal q).
Definition control q := existsb (Nat.eqb q) [11;94;128;130;20;46;399].
Definition checked_edge q b :=
  match lookup new_table q b with
  | None => false
  | Some (w,R,t) => andb (Bool.eqb w b)
      (andb (Nat.leb (S (height t)) (height q))
       (andb (Nat.leb ((if b then 0 else 1) + zero_bound t) (zero_bound q)) (admissible t)))
  | Some (_,L,t) => control t
  end.
Definition checked_node q := if node q then andb (checked_edge q false) (checked_edge q true) else true.
Lemma node_flags_size : length node_flags = new_count.
Proof. vm_compute. reflexivity. Qed.
Lemma program_certificate : forallb checked_node (seq 0 new_count) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma node_in_range q : node q = true -> q < new_count.
Proof.
  unfold node. destruct (lt_dec q (length node_flags)).
  - rewrite node_flags_size in l. auto.
  - rewrite nth_overflow by lia. discriminate.
Qed.
Lemma checked_node_sound q b : node q = true -> checked_edge q b = true.
Proof.
  intro H. pose proof program_certificate as C. rewrite forallb_forall in C.
  assert (I : In q (seq 0 new_count)) by (apply in_seq; pose proof (node_in_range q H); lia).
  specialize (C q I). unfold checked_node in C. rewrite H in C.
  apply andb_true_iff in C as [C0 C1]. destruct b; assumption.
Qed.
Lemma right_edge_sound q b w t : node q = true -> lookup new_table q b = Some(w,R,t) ->
  w=b /\ S (height t) <= height q /\
  (if b then 0 else 1) + zero_bound t <= zero_bound q /\ admissible t = true.
Proof.
  intros N E. pose proof (checked_node_sound q b N) as H.
  unfold checked_edge in H. rewrite E in H.
  apply andb_true_iff in H as [W H]. apply andb_true_iff in H as [A H].
  apply andb_true_iff in H as [B C].
  apply (proj1 (Bool.eqb_true_iff w b)) in W.
  apply Nat.leb_le in A. apply Nat.leb_le in B. auto.
Qed.
Lemma lookup_new_edge q b w d t : lookup new_table q b = Some(w,d,t) -> edge q b w d t.
Proof.
  intro E. assert (Hq : q < new_count).
  { unfold lookup in E. destruct (nth_error new_table q) eqn:F; [|discriminate].
    rewrite <- new_table_size. apply nth_error_Some. rewrite F. discriminate. }
  unfold edge, new_tm, st. rewrite val_mk by lia. rewrite E. reflexivity.
Qed.

Inductive ReadPath : nat -> list bool -> nat -> Prop :=
| read_nil q : ReadPath q [] q
| read_cons q b t bits out : node q = true ->
    lookup new_table q b = Some(b,R,t) -> ReadPath t bits out ->
    ReadPath q (b::bits) out.

Theorem read_path_semantics q bits out : ReadPath q bits out -> forall l r,
  Runs (CR q l (Str_app bits r)) (CR out (Str_app (rev bits) l) r).
Proof.
  intro P. induction P; intros l r; cbn [Str_app rev].
  - apply runs_refl.
  - eapply runs_trans; [apply step_RR, lookup_new_edge; exact H0|].
    rewrite Str_app_assoc. cbn [Str_app]. apply IHP.
Qed.
Theorem read_path_bounds q bits out : ReadPath q bits out ->
  length bits <= height q /\ zeros bits <= zero_bound q.
Proof.
  intro P. induction P.
  - cbn [length zeros]. lia.
  - pose proof (right_edge_sound q b b t H H0) as [_ [A [B _]]].
    destruct IHP. destruct b; cbn [length zeros] in *; lia.
Qed.

(** The register return uses a zero in the PC (plus the root's zero).
    Check this lower bound independently of the upper-bound certificate. *)
Definition zero_potential q := nth q node_potential 0.
Definition potential_edge q b :=
  match lookup new_table q b with
  | Some (_,R,t) => Nat.leb (zero_potential t)
      ((if b then 0 else 1) + zero_potential q)
  | _ => true
  end.
Definition potential_node q := if node q then
  andb (potential_edge q false) (potential_edge q true) else true.
Lemma potential_certificate : forallb potential_node (seq 0 new_count) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma potential_edge_sound q b t : node q = true ->
  lookup new_table q b = Some(b,R,t) ->
  zero_potential t <= (if b then 0 else 1) + zero_potential q.
Proof.
  intros N E. pose proof potential_certificate as C. rewrite forallb_forall in C.
  assert (I : In q (seq 0 new_count)) by (apply in_seq; pose proof (node_in_range q N); lia).
  specialize (C q I). unfold potential_node in C. rewrite N in C.
  apply andb_true_iff in C as [C0 C1].
  assert (H : potential_edge q b = true) by (destruct b; assumption).
  unfold potential_edge in H. rewrite E in H. now apply Nat.leb_le.
Qed.
Lemma read_path_potential q bits out : ReadPath q bits out ->
  zero_potential out <= zeros bits + zero_potential q.
Proof.
  intro P. induction P; [simpl; lia|].
  pose proof (potential_edge_sound q b t H H0).
  destruct b; cbn [zeros] in *; lia.
Qed.
Lemma inc_entry_potential i : i < 11 -> zero_potential (inc_entry i) = 1.
Proof. intro H. do 11 (destruct i as [|i]; [reflexivity|]); lia. Qed.
Lemma dec_entry_potential i : i < 11 -> zero_potential (dec_entry i) = 1.
Proof. intro H. do 11 (destruct i as [|i]; [reflexivity|]); lia. Qed.
Theorem register_path_has_zero w i : i < 11 ->
  (ReadPath 72 w (inc_entry i) \/ ReadPath 72 w (dec_entry i)) -> 1 <= zeros w.
Proof.
  intros Hi [P|P]; pose proof (read_path_potential _ _ _ P) as H;
    rewrite ?inc_entry_potential, ?dec_entry_potential in H by exact Hi;
    change (1 <= zeros w + 0) in H; lia.
Qed.

Definition Boundary q r := terminal q = true \/
  exists w t, node q = true /\ lookup new_table q (hd r) = Some(w,L,t) /\ control t = true.

(** Every traversal terminates at a register, halt, or left-jump boundary.
    There is no finite-run cutoff assumption in this theorem. *)
Lemma walk_terminates fuel : forall q r, height q <= fuel -> admissible q = true ->
  exists bits out tail, ReadPath q bits out /\ r = Str_app bits tail /\ Boundary out tail.
Proof.
  induction fuel as [|fuel IH]; intros q r Hfuel Hq;
    unfold admissible in Hq; destruct (node q) eqn:N.
  - destruct r as [b r]. pose proof (checked_node_sound q b N) as C.
    unfold checked_edge in C. destruct (lookup new_table q b) as [[[w d] t]|] eqn:E; [|discriminate].
    destruct d.
    + exists ([] : list bool),q,(Cons b r). split; [constructor|]. split; [reflexivity|].
      right. exists w,t. auto.
    + pose proof (right_edge_sound q b w t N E) as [_ [A _]]. lia.
  - exists ([] : list bool),q,r. split; [constructor|]. split; [reflexivity|]. left. exact Hq.
  - destruct r as [b r]. pose proof (checked_node_sound q b N) as C.
    unfold checked_edge in C. destruct (lookup new_table q b) as [[[w d] t]|] eqn:E; [|discriminate].
    destruct d.
    + exists ([] : list bool),q,(Cons b r). split; [constructor|]. split; [reflexivity|].
      right. exists w,t. auto.
    + destruct (right_edge_sound q b w t N E) as [W [A [Z T]]]. subst w.
      destruct (IH t r ltac:(lia) T) as [bits [out [tail [P [F B]]]]].
      exists (b::bits),out,tail. split; [econstructor; eassumption|].
      split; [simpl; now rewrite F|exact B].
  - exists ([] : list bool),q,r. split; [constructor|]. split; [reflexivity|]. left. exact Hq.
Qed.

Theorem main_dispatch_total l r : exists bits out tail,
  ReadPath 72 bits out /\ r = Str_app bits tail /\ Boundary out tail /\
  length bits <= 404 /\ zeros bits <= 32 /\
  Runs (CR 72 l r) (CR out (Str_app (rev bits) l) tail).
Proof.
  destruct (walk_terminates 404 72 r ltac:(vm_compute; lia) ltac:(reflexivity))
    as [bits [out [tail [P [E B]]]]].
  exists bits,out,tail. pose proof (read_path_bounds _ _ _ P) as [Hl Hz].
  change (length bits <= 404) in Hl. change (zeros bits <= 32) in Hz.
  repeat split; try assumption. rewrite E. now apply read_path_semantics.
Qed.

Print Assumptions read_path_semantics.
Print Assumptions read_path_bounds.
Print Assumptions main_dispatch_total.
Print Assumptions register_path_has_zero.
