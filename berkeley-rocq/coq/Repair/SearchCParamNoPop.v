(** The opcode-zero and opcode-at-least-two exits of source cparam. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerRegisters CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerContexts CompilerExecution CompilerLoopBase ConstructorPaths ConstructorControl ConstructorFrame SearchCParamControl SourceExecution.
Import ListNotations.

Definition outside_opcode (before after : list nat) := forall i, i<11 -> i<>4 ->
  nth_error after i=nth_error before i.

Theorem source_cparam_zero_nonempty ctx root p clear copy rs :
  cparam_layout root p clear copy -> SourcePrefix source_graph source_root ctx root ->
  nth_error rs 4=Some 0 ->
  exists mid, SourceProgramStep (ctx,rs) mid /\ SourceProgramRuns mid (loop_return ctx,rs).
Proof.
  intros Layout P C. destruct Layout as [Inner Clear Copy CT XT].
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P Inner) as Pinner.
  pose proof (cparam_inner_first_zero (ctx++[false]) rs Pinner C) as First.
  rewrite <-app_assoc in First. cbn [app] in First.
  exists (ctx++[false;true],rs). split.
  - eapply constructor_unpad_first_step with (pad:=1). exact First.
  - eapply source_program_next; [apply cparam_outer_break_step; exact Pinner|constructor].
Qed.

Theorem source_cparam_ge2_nonempty ctx root p clear copy rs n :
  cparam_layout root p clear copy -> SourcePrefix source_graph source_root ctx root ->
  11<=length rs -> nth_error rs 4=Some(S(S n)) ->
  exists result mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (loop_return ctx,result) /\ 11<=length result /\
    nth_error result 4=Some(S(S n)) /\ outside_opcode rs result /\
    exists pad, skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  intros Layout P L C. destruct Layout as [Inner Clear Copy CT XT].
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P Inner) as Pinner.
  set (u := ctx++[false]).
  set (r1 := set_register 4 (S n) rs++[0]).
  pose proof (cparam_inner_first_positive u rs (S n) Pinner C) as First. fold r1 in First.
  assert (L1 : 11<=length r1) by (unfold r1; rewrite length_app,set_register_length; cbn; lia).
  assert (C1 : nth_error r1 4=Some(S n)).
  { unfold r1. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    apply nth_error_set_same. lia. }
  set (r2 := set_register 4 n r1++[0]).
  pose proof (cparam_inner_second_positive u r1 n Pinner C1) as Second. fold r2 in Second.
  assert (L2 : 11<=length r2).
  { unfold r2. rewrite length_app,set_register_length. change (11<=length r1+1). lia. }
  assert (C2 : nth_error r2 4=Some n).
  { unfold r2. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    apply nth_error_set_same. lia. }
  pose proof (source_select_in_context _ _ _ _ _ _ Pinner cparam_inner_inc_first) as Sel1.
  set (r3 := set_register 4 (S n) r2).
  assert (Step3 : SourceProgramStep (u++[false;true;false;true],r2)
      (u++[false;true;false;true;false;true],r3)).
  { unfold r3. replace (u++[false;true;false;true;false;true])
      with ((u++[false;true;false;true;false])++[true]) by now rewrite <-app_assoc.
    eapply cparam_increment_padded with (pad:=2) (k:=0) (n:=n).
    - cbn [repeat]. repeat rewrite <-app_assoc. reflexivity.
    - cbn [repeat]. now rewrite <-app_assoc.
    - exact C2. }
  assert (L3 : 11<=length r3) by (unfold r3; rewrite set_register_length; exact L2).
  assert (C3 : nth_error r3 4=Some(S n)) by (unfold r3; apply nth_error_set_same; lia).
  pose proof (source_select_in_context _ _ _ _ _ _ Pinner cparam_inner_inc_second) as Sel2.
  set (result := set_register 4 (S(S n)) r3).
  assert (Step4 : SourceProgramStep (u++[false;true;false;true;false;true],r3)
      (u++[false;true;false;true;true],result)).
  { unfold result. replace (u++[false;true;false;true;true])
      with ((u++[false;true;false;true])++[true]) by now rewrite <-app_assoc.
    eapply cparam_increment_padded with (pad:=0) (k:=1) (n:=S n).
    - cbn [repeat]. repeat rewrite <-app_assoc. reflexivity.
    - cbn [repeat]. rewrite app_nil_r. exact Sel2.
    - exact C3. }
  assert (Tail : SourceProgramRuns (u++[false;true],r1) (loop_return ctx,result)).
  { eapply source_program_next; [exact Second|].
    eapply source_program_next; [exact Step3|].
    eapply source_program_next; [exact Step4|].
    eapply source_program_next; [apply cparam_inner_break_inner_step; exact Pinner|].
    unfold u. rewrite <-app_assoc. cbn [app].
    eapply source_program_next; [apply cparam_outer_break_step; exact Pinner|constructor]. }
  assert (AllRun : SourceProgramRuns (ctx,rs) (loop_return ctx,result)).
  { eapply source_program_next; [eapply constructor_unpad_first_step with (pad:=1); exact First|exact Tail]. }
  destruct (source_runs_zero_suffix _ _ AllRun L) as [pad [Pad _]].
  exists result,(u++[false;true],r1). repeat split; try assumption.
  - eapply constructor_unpad_first_step with (pad:=1). exact First.
  - unfold result. rewrite set_register_length. exact L3.
  - unfold result. apply nth_error_set_same. lia.
  - unfold outside_opcode. intros i I I4.
    unfold result,r3. rewrite !nth_error_set_other by lia.
    unfold r2. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia.
    unfold r1. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    now rewrite nth_error_set_other by lia.
  - now exists pad.
Qed.
Print Assumptions source_cparam_zero_nonempty.
Print Assumptions source_cparam_ge2_nonempty.
