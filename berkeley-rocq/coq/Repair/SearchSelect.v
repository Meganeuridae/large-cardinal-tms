(** Concrete source execution of the proof-search select routine. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerRegisters ConstructorArithmetic CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerContexts CompilerExecution CompilerLoopBase CompilerLoops ConstructorPaths ConstructorControl ConstructorUnpair ConstructorUnpairGenericFull ConstructorUnpairGenericInstances ConstructorPairFull ConstructorPush ConstructorFrame ConstructorParam ConstructorTokensV SearchPrimitivesDrain SearchSelectControl SearchSelectBranch SourceExecution.
Import ListNotations.

Definition outside_select (before after : list nat) := forall i, i<11 ->
  i<>2 -> i<>3 -> i<>4 -> i<>8 -> i<>9 -> nth_error after i=nth_error before i.

Theorem source_select_nonempty ctx rs computed old rest code :
  SourcePrefix source_graph source_root ctx 680 -> 11<=length rs ->
  nth_error rs 2=Some computed -> nth_error rs 3=Some(cantor old rest) ->
  nth_error rs 4=Some code -> nth_error rs 8=Some 0 -> nth_error rs 9=Some 0 ->
  exists result mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (loop_return ctx,result) /\ 11<=length result /\
    nth_error result 2=Some(selected_top code old computed) /\
    nth_error result 3=Some rest /\ nth_error result 4=Some(pred code) /\
    nth_error result 8=Some 0 /\ nth_error result 9=Some 0 /\
    outside_select rs result /\
    exists pad, skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  intros P L Top Stack Code X Y.
  destruct select_source_prefixes as [TopPrefix [UnpairPrefix [StackPrefix [IfPrefix [FinalPrefix _]]]]].
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P TopPrefix) as Ptop.
  destruct (while1_transfer_nonempty (ctx++[false]) 35 rs 2 8 computed 0
    Ptop select_top_move_tree ltac:(lia) ltac:(lia) ltac:(lia) L Top X)
    as [mid [First TopRun]].
  rewrite constructor_loop_return_false in TopRun.
  set (r1 := set_register 8 computed (set_register 2 0 rs)++repeat 0 computed).
  change (SourceProgramRuns mid (ctx++[true],r1)) in TopRun.
  assert (L1 : 11<=length r1) by (unfold r1; rewrite length_app,repeat_length,!set_register_length; lia).
  assert (T1 : nth_error r1 2=Some 0).
  { unfold r1. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite nth_error_set_other by lia. apply nth_error_set_same. lia. }
  assert (S1 : nth_error r1 3=Some(cantor old rest)).
  { unfold r1. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact Stack. }
  assert (C1 : nth_error r1 4=Some code).
  { unfold r1. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact Code. }
  assert (X1 : nth_error r1 8=Some computed).
  { unfold r1. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    apply nth_error_set_same. rewrite set_register_length. lia. }
  assert (Y1 : nth_error r1 9=Some 0).
  { unfold r1. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact Y. }
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P UnpairPrefix) as Punpair.
  destruct (source_unpair_generic_cantor_nonempty (ctx++[true;false]) 674 3 2 9 old rest r1
    Punpair source_unpair_select_tree ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) ltac:(lia) L1 S1 T1 Y1)
    as [r2 [mid2 [First2 [UnpairRun [L2 [S2 [T2 [Y2 F2]]]]]]]].
  replace (ctx++[true;false]) with ((ctx++[true])++[false]) in UnpairRun by now rewrite <-app_assoc.
  rewrite constructor_loop_return_false in UnpairRun. rewrite <-app_assoc in UnpairRun. cbn [app] in UnpairRun.
  assert (C2 : nth_error r2 4=Some code) by (rewrite (F2 4) by lia; exact C1).
  assert (X2 : nth_error r2 8=Some computed) by (rewrite (F2 8) by lia; exact X1).
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P StackPrefix) as Pstack.
  destruct (while1_transfer_nonempty (ctx++[true;true;false]) 30 r2 9 3 rest 0
    Pstack select_stack_restore_tree ltac:(lia) ltac:(lia) ltac:(lia) L2 Y2 S2)
    as [mid3 [First3 StackRun]].
  replace (ctx++[true;true;false]) with ((ctx++[true;true])++[false]) in StackRun by now rewrite <-app_assoc.
  rewrite constructor_loop_return_false in StackRun. rewrite <-app_assoc in StackRun. cbn [app] in StackRun.
  set (r3 := set_register 3 rest (set_register 9 0 r2)++repeat 0 rest).
  change (SourceProgramRuns mid3 (ctx++[true;true;true],r3)) in StackRun.
  assert (L3 : 11<=length r3) by (unfold r3; rewrite length_app,repeat_length,!set_register_length; lia).
  assert (T3 : nth_error r3 2=Some old).
  { unfold r3. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact T2. }
  assert (S3 : nth_error r3 3=Some rest).
  { unfold r3. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    apply nth_error_set_same. rewrite set_register_length. lia. }
  assert (C3 : nth_error r3 4=Some code).
  { unfold r3. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact C2. }
  assert (X3 : nth_error r3 8=Some computed).
  { unfold r3. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact X2. }
  assert (Y3 : nth_error r3 9=Some 0).
  { unfold r3. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite nth_error_set_other by lia. apply nth_error_set_same. lia. }
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P IfPrefix) as Pif.
  destruct (source_select_if_nonempty (ctx++[true;true;true;false]) r3 old computed code
    Pif L3 T3 C3 X3) as [r4 [mid4 [First4 [IfRun [L4 [T4 [C4 [X4 [F4 [pad4 Tail4]]]]]]]]]].
  replace (ctx++[true;true;true;false]) with ((ctx++[true;true;true])++[false]) in IfRun by now rewrite <-app_assoc.
  rewrite constructor_loop_return_false in IfRun. rewrite <-app_assoc in IfRun. cbn [app] in IfRun.
  assert (S4 : nth_error r4 3=Some rest) by (rewrite (F4 3) by lia; exact S3).
  assert (Y4 : nth_error r4 9=Some 0) by (rewrite (F4 9) by lia; exact Y3).
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P FinalPrefix) as Pfinal.
  pose proof (source_drain (ctx++[true;true;true;true]) 679 8 r4 (selected_scratch code computed)
    Pfinal select_scratch_drain_tree ltac:(lia) L4 X4) as FinalRun.
  change (SourceProgramRuns (ctx++[true;true;true;true],r4)
    (loop_return (ctx++repeat true 4),
      set_register 8 0 r4++repeat 0 (selected_scratch code computed))) in FinalRun.
  rewrite loop_return_true_repeat in FinalRun.
  set (result := set_register 8 0 r4++repeat 0 (selected_scratch code computed)).
  change (SourceProgramRuns (ctx++[true;true;true;true],r4) (loop_return ctx,result)) in FinalRun.
  assert (AllTail : SourceProgramRuns mid (loop_return ctx,result)).
  { eapply source_program_runs_trans; [exact TopRun|].
    eapply source_program_next with (t:=mid2).
    - eapply constructor_unpad_first_step with (pad:=1).
      change (SourceProgramStep ((ctx++[true])++[false],r1) mid2).
      rewrite <-app_assoc. exact First2.
    - eapply source_program_runs_trans; [exact UnpairRun|].
      eapply source_program_next with (t:=mid3).
      + eapply constructor_unpad_first_step with (pad:=1).
        change (SourceProgramStep ((ctx++[true;true])++[false],r2) mid3).
        rewrite <-app_assoc. exact First3.
      + eapply source_program_runs_trans; [exact StackRun|].
        eapply source_program_next with (t:=mid4).
        * eapply constructor_unpad_first_step with (pad:=1).
          change (SourceProgramStep ((ctx++[true;true;true])++[false],r3) mid4).
          rewrite <-app_assoc. exact First4.
        * eapply source_program_runs_trans; eassumption. }
  assert (AllRun : SourceProgramRuns (ctx,rs) (loop_return ctx,result)).
  { eapply source_program_next; [eapply constructor_unpad_first_step with (pad:=1); exact First|exact AllTail]. }
  destruct (source_runs_zero_suffix _ _ AllRun L) as [pad [Pad _]].
  exists result,mid. repeat split; try assumption.
  - eapply constructor_unpad_first_step with (pad:=1). exact First.
  - unfold result. rewrite length_app,repeat_length,set_register_length. lia.
  - unfold result. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact T4.
  - unfold result. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact S4.
  - unfold result. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact C4.
  - unfold result. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    apply nth_error_set_same. lia.
  - unfold result. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact Y4.
  - unfold outside_select. intros i I I2 I3 I4 I8 I9.
    unfold result. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. rewrite (F4 i) by lia.
    unfold r3. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. rewrite (F2 i) by lia.
    unfold r1. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    now rewrite !nth_error_set_other by lia.
  - now exists pad.
Qed.
Print Assumptions source_select_nonempty.
