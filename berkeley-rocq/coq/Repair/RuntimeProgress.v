(** Each intermediate instruction makes strictly positive literal TM progress.
    This is the progress half needed when reflecting a finite halting run. *)
From Stdlib Require Import Lists.List Streams.Streams Arith.Arith Lia.
From BusyCoq Require Import TM.
From Berkeley Require Import FiniteMachine.
From Repair Require Import Data Machine RuntimeTape RuntimeRegisters RuntimeControl RuntimeCalls RuntimeProgram RuntimeSimulation RuntimeJumps RuntimeTraces.
Import ListNotations.

Definition Progress := New.progress new_tm.
Lemma progress_then_runs a b c : Progress a b -> Runs b c -> Progress a c.
Proof.
  intros P R. induction P.
  - eapply New.progress_intro; eassumption.
  - eapply New.progress_step; [exact H|apply IHP; exact R].
Qed.
Lemma progress_counter a b : Progress a b ->
  exists n, 0 < n /\ New.multistep new_tm n a b.
Proof.
  intro P. destruct (New.progress_multistep _ _ _ P) as [n H].
  exists (S n). split; [lia|exact H].
Qed.

Lemma read_path_progress q w out : ReadPath q w out -> w <> [] -> forall l r,
  Progress (CR q l (Str_app w r)) (CR out (Str_app (rev w) l) r).
Proof.
  intros P N. induction P; intros l r; [contradiction|].
  cbn [Str_app rev]. eapply (New.progress_intro new_tm _
    (CR t (Cons b l) (Str_app bits r)) _).
  - apply New.step_right, lookup_new_edge. exact H0.
  - rewrite Str_app_assoc. cbn [Str_app]. apply read_path_semantics. exact P.
Qed.
Lemma register_path_nonempty w i : i < 11 ->
  (ReadPath 73 w (inc_entry i) \/ ReadPath 73 w (dec_entry i)) -> w <> [].
Proof.
  intros Hi P Z. subst w. pose proof (register_path_has_zero [] i Hi P) as H.
  cbn [zeros] in H. lia.
Qed.
Lemma jump_path_nonempty w q target : ReadPath 73 w q ->
  lookup new_table q true = Some (false,L,target) -> w <> [].
Proof.
  intros P E Z. subst w. inversion P; subst q. vm_compute in E. discriminate.
Qed.

Lemma register_prepared_progress width w q rs :
  ReadPath 73 w q -> w <> [] -> edge q false true R 6 ->
  Progress (normal width w rs)
    (CR q (left_of w)
      (Cons true (Cons false (reg (width-length w) (regs rs blank))))).
Proof.
  intros P N E. pose proof (read_path_bounds _ _ _ P) as [_ Hz].
  change (zeros w <= 33) in Hz. unfold normal, root_cfg at 1.
  eapply progress_then_runs; [apply read_path_progress; eassumption|].
  eapply runs_trans; [apply preparation_to_root; eassumption|].
  apply root_read,P.
Qed.

Theorem increment_progress width w before v after out n :
  length before < 11 -> length w <= width ->
  ReadPath 73 w (inc_entry (length before)) ->
  break_pc 0 (rev w++[false]) = Some(out,n) ->
  Progress (normal width w (before++v::after))
       (normal width (return_word out) (before++S v::after)).
Proof.
  intros Hr Hw P E. pose proof (read_path_bounds _ _ _ P) as [_ Hz].
  change (zeros w <= 33) in Hz.
  eapply progress_then_runs; [apply register_prepared_progress;
    [exact P|eapply register_path_nonempty; [exact Hr|left; exact P]|apply inc_entry_prepares,Hr]|].
  pose proof (increment_call before v after (width-length w) w out n blank Hr ltac:(lia) E) as C.
  assert (B : Cons false blank = blank) by (symmetry; apply const_unfold).
  rewrite B in C. destruct (returned_capacity _ _ _ _ _ Hw E) as [_ H].
  rewrite H in C. exact C.
Qed.
Theorem decrement_zero_progress width w before after out n :
  length before < 11 -> length w <= width ->
  ReadPath 73 w (dec_entry (length before)) ->
  break_pc 1 (rev w++[false]) = Some(out,n) ->
  Progress (normal width w (before++0::after))
       (normal width (return_word out) (before++0::after)).
Proof.
  intros Hr Hw P E. pose proof (read_path_bounds _ _ _ P) as [_ Hz].
  change (zeros w <= 33) in Hz.
  eapply progress_then_runs; [apply register_prepared_progress;
    [exact P|eapply register_path_nonempty; [exact Hr|right; exact P]|apply dec_entry_prepares,Hr]|].
  pose proof (decrement_zero_call before after (width-length w) w out n blank Hr ltac:(lia) E) as C.
  assert (B : Cons false blank = blank) by (symmetry; apply const_unfold).
  rewrite B in C. destruct (returned_capacity _ _ _ _ _ Hw E) as [_ H].
  rewrite H in C. exact C.
Qed.
Theorem decrement_positive_progress width w before v after out n :
  length before < 11 -> length w <= width ->
  ReadPath 73 w (dec_entry (length before)) ->
  break_pc 0 (rev w++[false]) = Some(out,n) ->
  Progress (normal width w (before++S v::after))
       (normal width (return_word out) (before++v::(after++[0]))).
Proof.
  intros Hr Hw P E. pose proof (read_path_bounds _ _ _ P) as [_ Hz].
  change (zeros w <= 33) in Hz.
  eapply progress_then_runs; [apply register_prepared_progress;
    [exact P|eapply register_path_nonempty; [exact Hr|right; exact P]|apply dec_entry_prepares,Hr]|].
  pose proof (decrement_positive_call before v after (width-length w) w out n blank Hr ltac:(lia) E) as C.
  assert (B : Cons false blank = blank) by (symmetry; apply const_unfold).
  rewrite B in C. destruct (returned_capacity _ _ _ _ _ Hw E) as [_ H].
  rewrite H in C. exact C.
Qed.

Theorem continue_jump_progress width w q k out n rs :
  length (w++[true]) <= width -> ReadPath 73 w q ->
  lookup new_table q true = Some(false,L,continue_state k) ->
  k <= 3 -> continue_pc k (rev w) = Some(out,n) ->
  Progress (normal width (w++[true]) rs) (normal width (rev out) rs).
Proof.
  intros HW P E Hk F. pose proof (read_path_bounds _ _ _ P) as [_ HZ].
  change (zeros w <= 33) in HZ.
  pose proof (jump_path_nonempty w q _ P E) as HNE.
  unfold normal at 1. unfold root_cfg at 1. rewrite Str_app_assoc. cbn [Str_app].
  eapply progress_then_runs; [apply read_path_progress; eassumption|].
  eapply runs_trans; [apply step_RL,lookup_new_edge,E|].
  eapply runs_trans; [apply continue_return_to_root; [exact Hk|lia|exact F]|].
  change (Runs (root_cfg (rev out)
    (copies n false (copies (S(S(S(width-length(w++[true]))))) false
      (Cons true (Cons false (regs rs blank)))))) (normal width (rev out) rs)).
  unfold normal. rewrite <- copies_add.
  pose proof (continue_pc_bounds _ _ _ _ F) as [_ HL].
  rewrite length_rev in HL. rewrite length_app in HW. simpl in HW.
  replace (n + S (S (S (width-length(w++[true])))))
    with (S(S(width-length(rev out)))) by (rewrite length_app,length_rev; simpl; lia).
  apply runs_refl.
Qed.
Theorem break_jump_progress width w q k out n rs :
  length (w++[true]) <= width -> ReadPath 73 w q ->
  lookup new_table q true = Some(false,L,break_state k) ->
  k <= 2 -> break_pc k (rev w++[false]) = Some(out,n) ->
  Progress (normal width (w++[true]) rs) (normal width (return_word out) rs).
Proof.
  intros HW P E Hk F. pose proof (read_path_bounds _ _ _ P) as [_ HZ].
  change (zeros w <= 33) in HZ.
  pose proof (jump_path_nonempty w q _ P E) as HNE.
  unfold normal at 1. unfold root_cfg at 1. rewrite Str_app_assoc. cbn [Str_app].
  eapply progress_then_runs; [apply read_path_progress; eassumption|].
  eapply runs_trans; [apply step_RL,lookup_new_edge,E|].
  eapply runs_trans; [apply (break_return_to_root k w out n
    (S(S(S(width-length(w++[true]))))) 0); [exact Hk|lia|exact F]|].
  unfold normal. cbn [reg copies].
  pose proof (return_word_bound _ _ _ _ F) as [_ HL].
  rewrite length_app in HW. simpl in HW.
  replace (n + S(S(S(width-length(w++[true])))) + 0)
    with (S(S(width-length(return_word out)))) by (rewrite length_app; simpl; lia).
  apply runs_refl.
Qed.

Theorem ir_step_progress width a b : fits width a -> IRStep a b ->
  Progress (encode width a) (encode width b).
Proof.
  intros HW H. destruct H; unfold encode, fits in *; cbn [fst snd] in *.
  - eapply increment_progress; eassumption.
  - eapply decrement_zero_progress; eassumption.
  - eapply decrement_positive_progress; eassumption.
  - eapply continue_jump_progress; eassumption.
  - eapply break_jump_progress; eassumption.
Qed.
Print Assumptions progress_counter.
Print Assumptions ir_step_progress.
