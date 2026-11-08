(** Actual-source cparam when opcode is exactly one: restore the opcode,
    pop a Cantor-coded stack head, and copy it into the parameter register. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerRegisters ConstructorArithmetic CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerContexts CompilerExecution CompilerLoopBase CompilerLoops ConstructorGraph ConstructorPaths ConstructorControl ConstructorUnpair ConstructorUnpairFull ConstructorPush ConstructorFrame ConstructorParam ConstructorTokensV SearchPrimitivesDrain SearchSelectControl SearchCParamControl SourceExecution.
Import ListNotations.

Lemma cparam_return_false_trues prefix n :
  loop_return ((prefix++[false])++repeat true n) = prefix++[true].
Proof. rewrite loop_return_true_repeat. apply constructor_loop_return_false. Qed.
Lemma cparam_stack_restore_return u :
  loop_return (u++[false;true;true;false;true;true]) = u++[false;true;true;true].
Proof.
  replace (u++[false;true;true;false;true;true])
    with ((u++[false;true;true;false])++[true;true]) by now rewrite <-app_assoc.
  replace (u++[false;true;true;false]) with ((u++[false;true;true])++[false])
    by now rewrite <-app_assoc.
  change (loop_return (((u++[false;true;true])++[false])++repeat true 2) = u++[false;true;true;true]).
  rewrite cparam_return_false_trues, <-app_assoc. reflexivity.
Qed.

Definition outside_cparam p (before after : list nat) := forall i, i<11 ->
  i<>p -> i<>3 -> i<>8 -> i<>9 -> nth_error after i=nth_error before i.

Theorem source_cparam_one_nonempty ctx root p clear copy rs a rest old :
  cparam_layout root p clear copy -> SourcePrefix source_graph source_root ctx root ->
  p<11 -> p<>3 -> p<>4 -> p<>8 -> p<>9 -> 11<=length rs ->
  nth_error rs 4=Some 1 -> nth_error rs 3=Some(cantor a rest) ->
  nth_error rs p=Some old -> nth_error rs 8=Some 0 -> nth_error rs 9=Some 0 ->
  exists result mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (loop_return ctx,result) /\ 11<=length result /\
    nth_error result 4=Some 1 /\ nth_error result 3=Some rest /\
    nth_error result p=Some a /\ nth_error result 8=Some 0 /\ nth_error result 9=Some 0 /\
    outside_cparam p rs result /\
    exists pad, skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  intros Layout P Hp H3 H4 H8 H9 L Code Stack Param X Y.
  destruct Layout as [Inner Clear Copy ClearTree CopyTree].
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P Inner) as Pinner.
  set (u := ctx++[false]).
  set (r1 := set_register 4 0 rs++[0]).
  pose proof (cparam_inner_first_positive u rs 0 Pinner Code) as First. fold r1 in First.
  assert (L1 : 11<=length r1) by (unfold r1; rewrite length_app,set_register_length; cbn; lia).
  assert (C1 : nth_error r1 4=Some 0).
  { unfold r1. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    apply nth_error_set_same. lia. }
  pose proof (cparam_inner_second_zero u r1 Pinner C1) as Second.
  pose proof (source_select_in_context _ _ _ _ _ _ Pinner cparam_inner_restore_one) as SelInc.
  set (r2 := set_register 4 1 r1).
  assert (Third : SourceProgramStep (u++[false;true;true],r1)
      (u++[false;true;true;false;true],r2)).
  { unfold r2. replace (u++[false;true;true;false;true])
      with ((u++[false;true;true;false])++[true]) by now rewrite <-app_assoc.
    eapply cparam_increment_padded with (pad:=2) (k:=0) (n:=0).
    - cbn [repeat]. repeat rewrite <-app_assoc. reflexivity.
    - cbn [repeat]. now rewrite <-app_assoc.
    - exact C1. }
  assert (L2 : 11<=length r2) by (unfold r2; rewrite set_register_length; exact L1).
  assert (C2 : nth_error r2 4=Some 1) by (unfold r2; apply nth_error_set_same; lia).
  assert (S2 : nth_error r2 3=Some(cantor a rest)).
  { unfold r2,r1. rewrite nth_error_set_other by lia.
    rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact Stack. }
  assert (P2 : nth_error r2 p=Some old).
  { unfold r2,r1. rewrite nth_error_set_other by lia.
    rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact Param. }
  assert (X2 : nth_error r2 8=Some 0).
  { unfold r2,r1. rewrite nth_error_set_other by lia.
    rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact X. }
  assert (Y2 : nth_error r2 9=Some 0).
  { unfold r2,r1. rewrite nth_error_set_other by lia.
    rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact Y. }
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ Pinner cparam_inner_unpair) as Punpair.
  destruct (source_unpair_cantor (u++[false;true;true;false;true;false]) r2 a rest
    Punpair L2 S2 X2 Y2) as [r3 [UnpairRun [L3 [S3 [X3 [Y3 F3]]]]]].
  replace (u++[false;true;true;false;true;false])
    with ((u++[false;true;true;false;true])++[false]) in UnpairRun by now rewrite <-app_assoc.
  rewrite constructor_loop_return_false in UnpairRun.
  replace ((u++[false;true;true;false;true])++[true])
    with (u++[false;true;true;false;true;true]) in UnpairRun by now rewrite <-app_assoc.
  replace ((u++[false;true;true;false;true])++[false])
    with (u++[false;true;true;false;true;false]) in UnpairRun by now rewrite <-app_assoc.
  assert (Diff : (u++[false;true;true;false;true;false],r2) <>
                 (u++[false;true;true;false;true;true],r3)).
  { intro E. apply (f_equal (@fst _ _)) in E. cbn [fst] in E.
    repeat rewrite app_assoc in E. apply app_inv_head in E. discriminate. }
  destruct (source_runs_nonempty_when_distinct _ _ UnpairRun Diff) as [mid3 [First3 Run3]].
  assert (C3 : nth_error r3 4=Some 1) by (rewrite (F3 4) by lia; exact C2).
  assert (P3 : nth_error r3 p=Some old) by (rewrite (F3 p) by lia; exact P2).
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ Pinner cparam_inner_stack_restore) as Prest.
  destruct (while1_transfer_nonempty (u++[false;true;true;false;true;true]) 30 r3 9 3 rest 0
    Prest select_stack_restore_tree ltac:(lia) ltac:(lia) ltac:(lia) L3 Y3 S3)
    as [mid4 [First4 StackRun]].
  rewrite cparam_stack_restore_return in StackRun.
  set (r4 := set_register 3 rest (set_register 9 0 r3)++repeat 0 rest).
  change (SourceProgramRuns mid4 (u++[false;true;true;true],r4)) in StackRun.
  assert (L4 : 11<=length r4) by (unfold r4; rewrite length_app,repeat_length,!set_register_length; lia).
  assert (C4 : nth_error r4 4=Some 1).
  { unfold r4. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact C3. }
  assert (S4 : nth_error r4 3=Some rest).
  { unfold r4. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    apply nth_error_set_same. rewrite set_register_length. lia. }
  assert (P4 : nth_error r4 p=Some old).
  { unfold r4. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact P3. }
  assert (X4 : nth_error r4 8=Some a).
  { unfold r4. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact X3. }
  assert (Y4 : nth_error r4 9=Some 0).
  { unfold r4. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite nth_error_set_other by lia. apply nth_error_set_same. lia. }
  pose proof (cparam_inner_break_test_step u r4 Pinner) as ExitTest.
  unfold u in ExitTest. rewrite constructor_loop_return_false in ExitTest.
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P Clear) as Pclear.
  destruct (source_drain_nonempty (ctx++[true;false]) clear p r4 old
    Pclear ClearTree Hp L4 P4) as [mid5 [ClearFirst ClearRun]].
  replace (ctx++[true;false]) with ((ctx++[true])++[false]) in ClearRun by now rewrite <-app_assoc.
  rewrite constructor_loop_return_false in ClearRun. rewrite <-app_assoc in ClearRun. cbn [app] in ClearRun.
  set (r5 := set_register p 0 r4++repeat 0 old).
  change (SourceProgramRuns mid5 (ctx++[true;true],r5)) in ClearRun.
  assert (L5 : 11<=length r5) by (unfold r5; rewrite length_app,repeat_length,set_register_length; lia).
  assert (C5 : nth_error r5 4=Some 1).
  { unfold r5. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact C4. }
  assert (S5 : nth_error r5 3=Some rest).
  { unfold r5. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact S4. }
  assert (P5 : nth_error r5 p=Some 0).
  { unfold r5. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    apply nth_error_set_same. lia. }
  assert (X5 : nth_error r5 8=Some a).
  { unfold r5. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact X4. }
  assert (Y5 : nth_error r5 9=Some 0).
  { unfold r5. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact Y4. }
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P Copy) as Pcopy.
  pose proof (while1_transfer (ctx++[true;true]) copy r5 8 p a 0
    Pcopy CopyTree ltac:(lia) Hp ltac:(lia) L5 X5 P5) as CopyRun.
  rewrite loop_return_two_true in CopyRun.
  set (result := set_register p a (set_register 8 0 r5)++repeat 0 a).
  change (SourceProgramRuns (ctx++[true;true],r5) (loop_return ctx,result)) in CopyRun.
  assert (AllTail : SourceProgramRuns (u++[false;true],r1) (loop_return ctx,result)).
  { eapply source_program_next; [exact Second|].
    eapply source_program_next; [exact Third|].
    eapply source_program_next with (t:=mid3).
    - eapply constructor_unpad_first_step with (pad:=1).
      change (SourceProgramStep ((u++[false;true;true;false;true])++[false],r2) mid3).
      rewrite <-app_assoc. exact First3.
    - eapply source_program_runs_trans; [exact Run3|].
      eapply source_program_next; [exact First4|].
      eapply source_program_runs_trans; [exact StackRun|].
      eapply source_program_next; [exact ExitTest|].
      eapply source_program_next with (t:=mid5).
      + eapply constructor_unpad_first_step with (pad:=1).
        change (SourceProgramStep ((ctx++[true])++[false],r4) mid5).
        rewrite <-app_assoc. exact ClearFirst.
      + eapply source_program_runs_trans; eassumption. }
  assert (AllRun : SourceProgramRuns (ctx,rs) (loop_return ctx,result)).
  { eapply source_program_next; [eapply constructor_unpad_first_step with (pad:=1); exact First|exact AllTail]. }
  destruct (source_runs_zero_suffix _ _ AllRun L) as [pad [Pad _]].
  exists result,(u++[false;true],r1). repeat split; try assumption.
  - eapply constructor_unpad_first_step with (pad:=1). exact First.
  - unfold result. rewrite length_app,repeat_length,!set_register_length. lia.
  - unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact C5.
  - unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact S5.
  - unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    apply nth_error_set_same. rewrite set_register_length. lia.
  - unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite nth_error_set_other by lia. apply nth_error_set_same. lia.
  - unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact Y5.
  - unfold outside_cparam. intros i I Ip I3 I8 I9.
    destruct (Nat.eq_dec i 4) as [->|I4].
    + unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      rewrite !nth_error_set_other by lia. rewrite C5. symmetry. exact Code.
    + unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      rewrite !nth_error_set_other by lia.
      unfold r5. rewrite nth_error_app1 by (rewrite set_register_length; lia).
      rewrite nth_error_set_other by lia.
      unfold r4. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      rewrite !nth_error_set_other by lia. rewrite (F3 i) by lia.
      unfold r2. rewrite nth_error_set_other by lia.
      unfold r1. rewrite nth_error_app1 by (rewrite set_register_length; lia).
      now rewrite nth_error_set_other by lia.
  - now exists pad.
Qed.
Print Assumptions source_cparam_one_nonempty.
