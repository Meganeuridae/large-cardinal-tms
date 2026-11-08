(** Control jumps erase a finite suffix of the PC and restore its capacity. *)
From Stdlib Require Import Lists.List Streams.Streams Arith.Arith Lia.
From BusyCoq Require Import TM.
From Berkeley Require Import FiniteMachine.
From Repair Require Import Data Machine RuntimeTape RuntimeRegisters RuntimeControl RuntimeCalls RuntimeProgram RuntimeSimulation.
Import ListNotations.

Definition continue_state k := nth k [11;95;129;131] 11.
Lemma continue_zero k : k <= 3 -> edge (continue_state k) false false L (continue_state k).
Proof. intro H. destruct k as [|[|[|[|k]]]]; try reflexivity; lia. Qed.
Lemma continue_one k : k < 3 -> edge (continue_state (S k)) true false L (continue_state k).
Proof. intro H. destruct k as [|[|[|k]]]; try reflexivity; lia. Qed.
Fixpoint continue_pc k bits : option (list bool * nat) :=
  match k with
  | 0 => Some(bits,0)
  | S k' => match bits with
    | [] => None
    | b::bits => option_map (fun '(out,n) => (out,S n))
        (continue_pc (if b then k' else k) bits)
    end
  end.
Lemma continue_pc_correct k bits out n l r : k <= 3 ->
  continue_pc k bits = Some(out,n) ->
  Runs (CL (continue_state k) (Str_app bits l) r)
       (CL 11 (Str_app out l) (copies n false r)).
Proof.
  revert k out n r. induction bits as [|b bits IH]; intros k out n r H E.
  - destruct k; [inversion E; subst; apply runs_refl|discriminate].
  - destruct k as [|k]; [inversion E; subst; apply runs_refl|].
    cbn [continue_pc] in E. cbn [Str_app].
    destruct (continue_pc (if b then k else S k) bits) as [[o z]|] eqn:F; [|discriminate].
    inversion E; subst. destruct b.
    + eapply runs_trans; [apply step_LL,continue_one; lia|].
      cbn [copies]. rewrite <- copies_snoc. apply IH; [lia|exact F].
    + eapply runs_trans; [apply step_LL,continue_zero; lia|].
      cbn [copies]. rewrite <- copies_snoc. apply IH; [lia|exact F].
Qed.
Lemma continue_pc_bounds k bits out n : continue_pc k bits = Some(out,n) ->
  zeros out <= zeros bits /\ length out+n = length bits.
Proof.
  revert k out n. induction bits as [|b bits IH]; intros k out n E.
  - destruct k; [inversion E; subst; simpl; lia|discriminate].
  - destruct k as [|k]; [inversion E; subst; simpl; lia|].
    cbn [continue_pc] in E.
    destruct (continue_pc (if b then k else S k) bits) as [[o z]|] eqn:F; [|discriminate].
    pose proof (IH _ _ _ F) as [HZ HL]. inversion E; subst.
    destruct b; cbn [zeros length] in *; lia.
Qed.
Fixpoint ones (bits : list bool) :=
  match bits with [] => 0 | true::bits => S(ones bits) | false::bits => ones bits end.
Lemma ones_zeros bits : ones bits+zeros bits=length bits.
Proof. induction bits as [|[] bits IH]; simpl; lia. Qed.
Lemma continue_pc_total k bits : k <= ones bits -> exists out n, continue_pc k bits = Some(out,n).
Proof.
  revert k. induction bits as [|b bits IH]; intros k H.
  - destruct k; [exists ([] : list bool),0; reflexivity|simpl in H; lia].
  - destruct k as [|k]; [exists (b::bits),0; reflexivity|].
    destruct b; cbn [ones] in H; cbn [continue_pc].
    + destruct (IH k ltac:(lia)) as [out [n E]].
      exists out,(S n); rewrite E; reflexivity.
    + destruct (IH (S k) ltac:(lia)) as [out [n E]].
      exists out,(S n); rewrite E; reflexivity.
Qed.

Theorem continue_return_to_root k w out n r :
  k <= 3 -> zeros w <= 34 -> continue_pc k (rev w) = Some(out,n) ->
  Runs (CL (continue_state k) (left_of w) r)
       (root_cfg (rev out) (copies n false r)).
Proof.
  intros Hk Hw E. eapply runs_trans; [apply continue_pc_correct; eassumption|].
  pose proof (continue_pc_bounds _ _ _ _ E) as [HZ HL].
  rewrite zeros_rev in HZ.
  pose proof (continue_to_root (rev out) (copies n false r)
    ltac:(rewrite zeros_rev; lia)) as H.
  unfold left_of in H. rewrite rev_involutive in H. exact H.
Qed.

(** A jump's triggering 1 is itself erased by the left transition. *)
Theorem continue_jump_simulation width w q k out n rs :
  length (w++[true]) <= width -> ReadPath 73 w q ->
  lookup new_table q true = Some(false,L,continue_state k) ->
  k <= 3 -> continue_pc k (rev w) = Some(out,n) ->
  Runs (normal width (w++[true]) rs) (normal width (rev out) rs).
Proof.
  intros HW P E Hk F. pose proof (read_path_bounds _ _ _ P) as [_ HZ].
  change (zeros w <= 33) in HZ.
  unfold normal at 1. unfold root_cfg at 1. rewrite Str_app_assoc. cbn [Str_app].
  eapply runs_trans; [apply read_path_semantics,P|].
  eapply runs_trans; [apply step_RL,lookup_new_edge,E|].
  eapply runs_trans; [apply continue_return_to_root; [exact Hk|lia|exact F]|].
  change (Runs (root_cfg (rev out)
    (copies n false (copies (S(S(S(width-length(w++[true]))))) false
      (Cons true (Cons false (regs rs blank)))))) (normal width (rev out) rs)).
  unfold normal. rewrite <- copies_add.
  pose proof (continue_pc_bounds _ _ _ _ F) as [_ HL].
  rewrite rev_length in HL. rewrite app_length in HW. simpl in HW.
  replace (n + S (S (S (width-length(w++[true])))))
    with (S(S(width-length(rev out)))) by (rewrite app_length,rev_length; simpl; lia).
  apply runs_refl.
Qed.

Theorem break_jump_simulation width w q k out n rs :
  length (w++[true]) <= width -> ReadPath 73 w q ->
  lookup new_table q true = Some(false,L,break_state k) ->
  k <= 2 -> break_pc k (rev w++[false]) = Some(out,n) ->
  Runs (normal width (w++[true]) rs) (normal width (return_word out) rs).
Proof.
  intros HW P E Hk F. pose proof (read_path_bounds _ _ _ P) as [_ HZ].
  change (zeros w <= 33) in HZ.
  unfold normal at 1. unfold root_cfg at 1. rewrite Str_app_assoc. cbn [Str_app].
  eapply runs_trans; [apply read_path_semantics,P|].
  eapply runs_trans; [apply step_RL,lookup_new_edge,E|].
  eapply runs_trans; [apply (break_return_to_root k w out n
    (S(S(S(width-length(w++[true]))))) 0); [exact Hk|lia|exact F]|].
  unfold normal. cbn [reg copies].
  pose proof (return_word_bound _ _ _ _ F) as [_ HL].
  rewrite app_length in HW. simpl in HW.
  replace (n + S(S(S(width-length(w++[true])))) + 0)
    with (S(S(width-length(return_word out)))) by (rewrite app_length; simpl; lia).
  apply runs_refl.
Qed.

Print Assumptions continue_return_to_root.
Print Assumptions continue_jump_simulation.
Print Assumptions break_jump_simulation.
