(** Whole source switch implementation of the numeric MP instruction. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import CompilerRegisters ConstructorArithmetic ProofSearchSyntax ProofSearchProgram.
From Repair Require Import CompilerExecution CompilerLoopBase ConstructorFrame GrammarExecutionDispatch GrammarExecutionOpcodes GrammarExecutionBodies GrammarExecutionMPBody SourceExecution.
Import ListNotations.

Theorem source_mp_exec_instruction rs old prior_stack a b c :
  11<=length rs -> nth_error rs 2=Some 0 -> nth_error rs 3=Some(cantor old prior_stack) ->
  nth_error rs 4=Some 1 -> nth_error rs 5=Some a -> nth_error rs 6=Some b -> nth_error rs 7=Some c ->
  nth_error rs 8=Some 0 -> nth_error rs 9=Some 0 -> nth_error rs 10=Some 0 ->
  exists result pad,
    SourceProgramRuns (main_switch_pc,rs) (loop_return main_switch_pc,result) /\ 11<=length result /\
    nth_error result 2=Some(fst (execute_instruction (1,a,b,c) (old,prior_stack))) /\
    nth_error result 3=Some(snd (execute_instruction (1,a,b,c) (old,prior_stack))) /\
    nth_error result 4=Some 0 /\ nth_error result 8=Some 0 /\ nth_error result 9=Some 0 /\
    nth_error result 10=Some 0 /\ nth_error result 0=nth_error rs 0 /\ nth_error result 1=nth_error rs 1 /\
    skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  intros Len Top Stack Code A B C X Y Z.
  destruct (uncantor prior_stack) as [major rest] eqn:U.
  pose proof (cantor_uncantor prior_stack) as E. rewrite U in E. cbn in E. subst prior_stack.
  pose proof (switch_special_opcode_entry 1 rs ltac:(lia) ltac:(lia) Len Code) as Switch.
  rewrite (set_register_noop _ _ _ Code) in Switch. cbn [repeat] in Switch.
  assert (Start : special_body_cursor 1 0 = switch_pc 1++[false;true;true]).
  { unfold special_body_cursor,special_body_parent. cbn [repeat]. now rewrite app_nil_r. }
  rewrite <- Start in Switch.
  assert (L0 : 11<=length(rs++[0])) by (rewrite app_length; simpl; lia).
  assert (Top0 : nth_error (rs++[0]) 2=Some 0) by (rewrite nth_error_app1 by lia; exact Top).
  assert (Stack0 : nth_error (rs++[0]) 3=Some(cantor old (cantor major rest)))
    by (rewrite nth_error_app1 by lia; exact Stack).
  assert (Code0 : nth_error (rs++[0]) 4=Some 1) by (rewrite nth_error_app1 by lia; exact Code).
  assert (A0 : nth_error (rs++[0]) 5=Some a) by (rewrite nth_error_app1 by lia; exact A).
  assert (B0 : nth_error (rs++[0]) 6=Some b) by (rewrite nth_error_app1 by lia; exact B).
  assert (C0 : nth_error (rs++[0]) 7=Some c) by (rewrite nth_error_app1 by lia; exact C).
  assert (X0 : nth_error (rs++[0]) 8=Some 0) by (rewrite nth_error_app1 by lia; exact X).
  assert (Y0 : nth_error (rs++[0]) 9=Some 0) by (rewrite nth_error_app1 by lia; exact Y).
  assert (Z0 : nth_error (rs++[0]) 10=Some 0) by (rewrite nth_error_app1 by lia; exact Z).
  destruct (source_mp_body_nonempty (rs++[0]) old major rest a b c
    L0 Top0 Stack0 Code0 A0 B0 C0 X0 Y0 Z0) as [result [mid H]].
  destruct H as [First H]. destruct H as [Tail H]. destruct H as [Len1 H].
  destruct H as [Top1 H]. destruct H as [Stack1 H]. destruct H as [Code1 H].
  destruct H as [X1 H]. destruct H as [Y1 H]. destruct H as [Z1 H].
  destruct H as [Frame0 [Frame1 Suffix]].
  assert (Run : SourceProgramRuns (main_switch_pc,rs) (loop_return main_switch_pc,result)).
  { eapply source_program_runs_trans; [exact Switch|]. eapply source_program_next; eassumption. }
  destruct (source_runs_zero_suffix _ _ Run Len) as [pad [Pad _]].
  exists result,pad. repeat split; try assumption.
  - cbn [execute_instruction]. rewrite uncantor_cantor. exact Top1.
  - cbn [execute_instruction]. rewrite uncantor_cantor. exact Stack1.
  - rewrite Frame0, nth_error_app1 by lia. reflexivity.
  - rewrite Frame1, nth_error_app1 by lia. reflexivity.
Qed.

Print Assumptions source_mp_exec_instruction.
