(** The actual MP if_eq test, through the equal-body entry or mismatch exit. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerReverse CompilerRegisters ConstructorPaths ConstructorUnpair ConstructorUnpairFull.
From Repair Require Import ConstructorGraph CompilerData SourceExecution CompilerLoopBase CompilerLoops ConstructorControl
  SearchPrimitivesDrain GuardEqControl.
Import ListNotations.

Definition eq_test_frame (before after : list nat) :=
  forall r, r<11 -> r<>9 -> r<>10 -> nth_error after r=nth_error before r.
Lemma eq_test_frame_refl rs : eq_test_frame rs rs. Proof. firstorder. Qed.
Lemma eq_test_frame_trans a b c : eq_test_frame a b -> eq_test_frame b c -> eq_test_frame a c.
Proof. unfold eq_test_frame. intros A B r R I J. now rewrite B,A by assumption. Qed.
Lemma eq_test_frame_write before rs i v pad : eq_test_frame before rs -> 11<=length rs ->
  (i=9 \/ i=10) -> eq_test_frame before (write_pad i v rs pad).
Proof.
  unfold eq_test_frame. intros F L D r R A B. rewrite write_pad_other by (destruct D; subst; lia).
  now apply F.
Qed.

Definition eq_test_exit ctx a b := if Nat.eqb a b then ctx++[true] else loop_return ctx.

Theorem source_mp_eq_loop_nonempty ctx a b rs :
  SourcePrefix source_graph source_root ctx 684 -> 11<=length rs ->
  nth_error rs 9=Some a -> nth_error rs 10=Some b ->
  exists result mid, SourceProgramStep (ctx++[false;false],rs) mid /\
    SourceProgramRuns mid (eq_test_exit ctx a b,result) /\ 11<=length result /\
    nth_error result 9=Some 0 /\ nth_error result 10=Some 0 /\ eq_test_frame rs result.
Proof.
  intros P. revert b rs. induction a as [|a IH]; intros b rs L A B.
  - destruct b as [|b].
    + exists rs,(ctx++[false;true],rs). repeat split; try assumption; try apply eq_test_frame_refl.
      * now apply source_mp_eq_loop_left_zero.
      * cbn [eq_test_exit]. eapply source_program_next; [now apply source_mp_eq_test_right_zero|constructor].
    + set (r1:=write_pad 10 b rs [0]).
      assert (L1 : 11<=length r1) by (unfold r1; rewrite write_pad_length; simpl; lia).
      assert (A1 : nth_error r1 9=Some 0) by (unfold r1; rewrite write_pad_other by lia; exact A).
      assert (B1 : nth_error r1 10=Some b) by (unfold r1; apply write_pad_same; lia).
      assert (F1 : eq_test_frame rs r1).
      { unfold r1. eapply eq_test_frame_write; [apply eq_test_frame_refl|exact L|now right]. }
      destruct source_mp_compare_prefixes as [_ [Sub _]].
      pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P Sub) as Prefix.
      destruct source_drain_roots as [_ [_ [_ [_ [_ [Tree _]]]]]].
      destruct (source_drain_nonempty (ctx++[false;true;true;false]) 662 10 r1 b
        Prefix Tree ltac:(lia) L1 B1) as [mid [DStep DRun]].
      set (result:=write_pad 10 0 r1 (repeat 0 b)). fold result in DRun.
      assert (Ret : loop_return (ctx++[false;true;true;false])=ctx++[false;true;true;true]).
      { replace (ctx++[false;true;true;false]) with ((ctx++[false;true;true])++[false])
          by (rewrite <- app_assoc; reflexivity).
        rewrite constructor_loop_return_false, <- app_assoc. reflexivity. }
      rewrite Ret in DRun.
      exists result,(ctx++[false;true],rs). repeat split.
      * now apply source_mp_eq_loop_left_zero.
      * cbn [eq_test_exit]. eapply source_program_next; [eapply source_mp_eq_test_right_positive; eassumption|].
        eapply source_program_next with (t:=mid).
        -- eapply constructor_unpad_first_step with (pad:=1).
           change (SourceProgramStep ((ctx++[false;true;true])++[false],r1) mid). rewrite <- app_assoc. exact DStep.
        -- eapply source_program_runs_trans; [exact DRun|].
           eapply source_program_next; [now apply source_mp_eq_break_right|constructor].
      * unfold result. rewrite write_pad_length,repeat_length. lia.
      * unfold result. rewrite write_pad_other by lia. exact A1.
      * unfold result. apply write_pad_same. lia.
      * unfold result. eapply eq_test_frame_write; [exact F1|exact L1|now right].
  - destruct b as [|b].
    + set (r1:=write_pad 9 a rs [0]).
      assert (L1 : 11<=length r1) by (unfold r1; rewrite write_pad_length; simpl; lia).
      assert (A1 : nth_error r1 9=Some a) by (unfold r1; apply write_pad_same; lia).
      assert (B1 : nth_error r1 10=Some 0) by (unfold r1; rewrite write_pad_other by lia; exact B).
      assert (F1 : eq_test_frame rs r1).
      { unfold r1. eapply eq_test_frame_write; [apply eq_test_frame_refl|exact L|now left]. }
      destruct source_mp_compare_prefixes as [Sub _].
      pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P Sub) as Prefix.
      destruct source_drain_roots as [_ [_ [_ [_ [Tree _]]]]].
      destruct (source_drain_nonempty (ctx++[false;false;true;true;false]) 661 9 r1 a
        Prefix Tree ltac:(lia) L1 A1) as [mid [DStep DRun]].
      set (result:=write_pad 9 0 r1 (repeat 0 a)). fold result in DRun.
      assert (Ret : loop_return (ctx++[false;false;true;true;false])=ctx++[false;false;true;true;true]).
      { replace (ctx++[false;false;true;true;false]) with ((ctx++[false;false;true;true])++[false])
          by (rewrite <- app_assoc; reflexivity).
        rewrite constructor_loop_return_false, <- app_assoc. reflexivity. }
      rewrite Ret in DRun.
      exists result,(ctx++[false;false;true],r1). repeat split.
      * unfold r1,write_pad. eapply source_mp_eq_loop_left_positive; eassumption.
      * cbn [eq_test_exit]. eapply source_program_next; [eapply source_mp_eq_loop_right_zero; eassumption|].
        eapply source_program_next with (t:=mid).
        -- eapply constructor_unpad_first_step with (pad:=1).
           change (SourceProgramStep ((ctx++[false;false;true;true])++[false],r1) mid). rewrite <- app_assoc. exact DStep.
        -- eapply source_program_runs_trans; [exact DRun|].
           eapply source_program_next; [now apply source_mp_eq_break_left|constructor].
      * unfold result. rewrite write_pad_length,repeat_length. lia.
      * unfold result. apply write_pad_same. lia.
      * unfold result. rewrite write_pad_other by lia. exact B1.
      * unfold result. eapply eq_test_frame_write; [exact F1|exact L1|now left].
    + set (r1:=write_pad 9 a rs [0]). set (r2:=write_pad 10 b r1 [0]).
      assert (L1 : 11<=length r1) by (unfold r1; rewrite write_pad_length; simpl; lia).
      assert (L2 : 11<=length r2) by (unfold r2; rewrite write_pad_length; simpl; lia).
      assert (B1 : nth_error r1 10=Some(S b)) by (unfold r1; rewrite write_pad_other by lia; exact B).
      assert (A2 : nth_error r2 9=Some a).
      { unfold r2. rewrite write_pad_other by lia. unfold r1. apply write_pad_same. lia. }
      assert (B2 : nth_error r2 10=Some b) by (unfold r2; apply write_pad_same; lia).
      assert (F1 : eq_test_frame rs r1).
      { unfold r1. eapply eq_test_frame_write; [apply eq_test_frame_refl|exact L|now left]. }
      assert (F2 : eq_test_frame rs r2).
      { unfold r2. eapply eq_test_frame_write; [exact F1|exact L1|now right]. }
      destruct (IH b r2 L2 A2 B2) as [result [mid [First [Run [Len [X [Y Frame]]]]]]].
      exists result,(ctx++[false;false;true],r1). repeat split; try assumption.
      * unfold r1,write_pad. eapply source_mp_eq_loop_left_positive; eassumption.
      * cbn [eq_test_exit]. eapply source_program_next; [unfold r2,write_pad; eapply source_mp_eq_loop_right_positive; eassumption|].
        eapply source_program_next; [now apply source_mp_eq_loop_continue|].
        eapply source_program_next; eassumption.
      * eapply eq_test_frame_trans; eassumption.
Qed.

Theorem source_mp_eq_test_nonempty ctx a b rs :
  SourcePrefix source_graph source_root ctx 684 -> 11<=length rs ->
  nth_error rs 9=Some a -> nth_error rs 10=Some b ->
  exists result mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (eq_test_exit ctx a b,result) /\ 11<=length result /\
    nth_error result 9=Some 0 /\ nth_error result 10=Some 0 /\ eq_test_frame rs result.
Proof.
  intros P L A B. destruct (source_mp_eq_loop_nonempty ctx a b rs P L A B)
    as [result [mid [Step [Run Facts]]]].
  exists result,mid. split; [|now split].
  eapply constructor_unpad_first_step with (pad:=2). exact Step.
Qed.

Print Assumptions source_mp_eq_loop_nonempty.
Print Assumptions source_mp_eq_test_nonempty.
