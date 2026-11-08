(** Unbounded source-program execution of the literal Cantor pair loop. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerRegisters ConstructorArithmetic CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerExecution CompilerLoopBase ConstructorPairControl ConstructorPair SourceExecution.
Import ListNotations.

Definition outside_pair i j k (before after : list nat) :=
  forall r, r < 11 -> r<>i -> r<>j -> r<>k -> nth_error after r = nth_error before r.
Lemma outside_pair_refl i j k rs : outside_pair i j k rs rs.
Proof. firstorder. Qed.
Lemma outside_pair_trans i j k a b c :
  outside_pair i j k a b -> outside_pair i j k b c -> outside_pair i j k a c.
Proof. unfold outside_pair. intros A B r H I J K. now rewrite B, A by assumption. Qed.

Lemma pair_head_invariant i j k a b c rs :
  i < 11 -> j < 11 -> k < 11 -> i<>j -> i<>k -> j<>k -> 11 <= length rs ->
  11 <= length (pair_head_store i j k a b c rs) /\
  nth_error (pair_head_store i j k a b c rs) i = Some 0 /\
  nth_error (pair_head_store i j k a b c rs) j = Some (b+a) /\
  nth_error (pair_head_store i j k a b c rs) k = Some (c+a) /\
  outside_pair i j k rs (pair_head_store i j k a b c rs).
Proof.
  intros I J K IJ IK JK L. unfold pair_head_store. repeat split.
  - rewrite app_length, repeat_length, !set_register_length. lia.
  - rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. apply nth_error_set_same. lia.
  - rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite nth_error_set_other by lia. apply nth_error_set_same.
    rewrite set_register_length. lia.
  - rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    apply nth_error_set_same. rewrite !set_register_length. lia.
  - unfold outside_pair. intros r R RI RJ RK.
    rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. reflexivity.
Qed.

Lemma pair_tail_invariant i j k h c rs :
  i < 11 -> j < 11 -> k < 11 -> i<>j -> i<>k -> j<>k -> 11 <= length rs ->
  11 <= length (pair_tail_store i j k h c rs) /\
  nth_error (pair_tail_store i j k h c rs) i = Some h /\
  nth_error (pair_tail_store i j k h c rs) j = Some 0 /\
  nth_error (pair_tail_store i j k h c rs) k = Some (S c) /\
  outside_pair i j k rs (pair_tail_store i j k h c rs).
Proof.
  intros I J K IJ IK JK L. unfold pair_tail_store. cbn zeta. repeat split.
  - rewrite app_length, repeat_length, !set_register_length, app_length, set_register_length. simpl. lia.
  - rewrite nth_error_app1 by (rewrite !set_register_length, app_length, set_register_length; simpl; lia).
    apply nth_error_set_same. rewrite !set_register_length, app_length, set_register_length. simpl. lia.
  - rewrite nth_error_app1 by (rewrite !set_register_length, app_length, set_register_length; simpl; lia).
    rewrite nth_error_set_other by lia. apply nth_error_set_same.
    rewrite set_register_length, app_length, set_register_length. simpl. lia.
  - rewrite nth_error_app1 by (rewrite !set_register_length, app_length, set_register_length; simpl; lia).
    rewrite !nth_error_set_other by lia. apply nth_error_set_same.
    rewrite app_length, set_register_length. simpl. lia.
  - unfold outside_pair. intros r R RI RJ RK.
    rewrite nth_error_app1 by (rewrite !set_register_length, app_length, set_register_length; simpl; lia).
    rewrite !nth_error_set_other by lia.
    rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. reflexivity.
Qed.

Theorem source_pair_cantor_nonempty ctx root i j k first second a b c rs :
  pair_layout root i j k first second -> SourcePrefix source_graph source_root ctx root ->
  i < 11 -> j < 11 -> k < 11 -> i<>j -> i<>k -> j<>k -> 11 <= length rs ->
  nth_error rs i = Some a -> nth_error rs j = Some b -> nth_error rs k = Some c ->
  exists result mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (loop_return ctx,result) /\
    11 <= length result /\ nth_error result i = Some 0 /\ nth_error result j = Some 0 /\
    nth_error result k = Some (c+cantor a b) /\ outside_pair i j k rs result.
Proof.
  intros Layout P I J K IJ IK JK.
  remember (a+b) as measure eqn:Measure. revert a b c rs Measure.
  induction measure using lt_wf_ind; intros a b c rs Measure L A B C.
  set (head := pair_head_store i j k a b c rs).
  pose proof (pair_head_invariant i j k a b c rs I J K IJ IK JK L)
    as [HL [HA [HB [HC HF]]]]. fold head in HL,HA,HB,HC,HF.
  destruct (source_pair_head_nonempty _ _ _ _ _ _ _ _ _ _ _ Layout P I J K IJ IK JK L A B C)
    as [mid [First Head]].
  fold head in Head. destruct (b+a) as [|h] eqn:E.
  - assert (a=0 /\ b=0) by lia. destruct H0 as [-> ->].
    cbn [cantor triangle Nat.add] in *. rewrite Nat.add_0_r in HC.
    exists head,mid. repeat split; try assumption.
    + eapply source_program_runs_trans; [exact Head|].
      eapply source_program_next; [|constructor].
      eapply source_pair_test_zero with (root:=root) (i:=i) (j:=j) (k:=k);
        [exact P|exact (pair_layout_tree _ _ _ _ _ _ Layout)|exact J|exact HB].
    + now rewrite Nat.add_0_r.
  - assert (Hmeasure : h < measure) by lia.
    set (tail := pair_tail_store i j k h (c+a) head).
    pose proof (pair_tail_invariant i j k h (c+a) head I J K IJ IK JK HL)
      as [TL [TA [TB [TC TF]]]]. fold tail in TL,TA,TB,TC,TF.
    pose proof (source_pair_positive_tail _ _ _ _ _ _ _ _ _ _ Layout P I J K IJ IK JK HL HA HB HC) as Tail.
    fold tail in Tail.
    destruct (H h Hmeasure h 0 (S(c+a)) tail ltac:(lia) TL TA TB TC)
      as [result [mid' [Next [Run [Len [Ai [Bj [Ck Frame]]]]]]]].
    assert (Code : c+cantor a b = S(c+a)+cantor h 0).
    { unfold cantor. replace (a+b) with (S h) by lia.
      replace (h+0) with h by lia. simpl. lia. }
    exists result,mid. repeat split; try assumption.
    + eapply source_program_runs_trans; [exact Head|].
      eapply source_program_runs_trans; [exact Tail|].
      eapply source_program_next; eassumption.
    + now rewrite Code.
    + eapply outside_pair_trans; [exact HF|]. eapply outside_pair_trans; eassumption.
Qed.

Theorem source_pair_cantor ctx root i j k first second a b c rs :
  pair_layout root i j k first second -> SourcePrefix source_graph source_root ctx root ->
  i < 11 -> j < 11 -> k < 11 -> i<>j -> i<>k -> j<>k -> 11 <= length rs ->
  nth_error rs i = Some a -> nth_error rs j = Some b -> nth_error rs k = Some c ->
  exists result, SourceProgramRuns (ctx,rs) (loop_return ctx,result) /\
    11 <= length result /\ nth_error result i = Some 0 /\ nth_error result j = Some 0 /\
    nth_error result k = Some (c+cantor a b) /\ outside_pair i j k rs result.
Proof.
  intros Layout P I J K IJ IK JK L A B C.
  destruct (source_pair_cantor_nonempty _ _ _ _ _ _ _ _ _ _ _ Layout P I J K IJ IK JK L A B C)
    as [result [mid [Step [Run Facts]]]]. exists result. split; [|exact Facts].
  eapply source_program_next; eassumption.
Qed.

Print Assumptions source_pair_cantor_nonempty.
Print Assumptions source_pair_cantor.
