(** Whole source switch implementation of numeric generalization. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import CompilerRegisters ConstructorArithmetic ProofSearchProgram.
From Repair Require Import CompilerExecution CompilerLoopBase ConstructorFrame GrammarExecutionDispatch GrammarExecutionOpcodes GrammarExecutionBodies GrammarExecutionConcrete RepairedUnion SearchGen SourceExecution.
Import ListNotations.

Theorem source_gen_exec_instruction rs old prior_stack a b c :
  11<=length rs -> nth_error rs 2=Some 0 -> nth_error rs 3=Some(cantor old prior_stack) ->
  nth_error rs 4=Some 2 -> nth_error rs 5=Some a -> nth_error rs 6=Some b -> nth_error rs 7=Some c ->
  nth_error rs 8=Some 0 -> nth_error rs 9=Some 0 -> nth_error rs 10=Some 0 ->
  exists result pad,
    SourceProgramRuns (main_switch_pc,rs) (loop_return main_switch_pc,result) /\ 11<=length result /\
    nth_error result 2=Some(fst (execute_instruction (2,a,b,c) (old,prior_stack))) /\
    nth_error result 3=Some(snd (execute_instruction (2,a,b,c) (old,prior_stack))) /\
    nth_error result 4=Some 0 /\ nth_error result 8=Some 0 /\ nth_error result 9=Some 0 /\
    nth_error result 10=Some 0 /\ nth_error result 0=nth_error rs 0 /\ nth_error result 1=nth_error rs 1 /\
    skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  intros Len Top Stack Code A B C X Y Z.
  set (r0 := set_register 4 1 rs ++ repeat 0 2).
  pose proof (switch_special_opcode_entry 2 rs ltac:(lia) ltac:(lia) Len Code) as Switch.
  fold r0 in Switch.
  assert (Start : special_body_cursor 2 0 = switch_pc 2++[false;true;true]).
  { unfold special_body_cursor,special_body_parent. cbn [repeat]. now rewrite app_nil_r. }
  rewrite <- Start in Switch.
  assert (L0 : 11<=length r0) by (unfold r0; rewrite app_length,set_register_length,repeat_length; lia).
  assert (Top0 : nth_error r0 2=Some 0) by (unfold r0; rewrite nth_after_dispatch by lia; exact Top).
  assert (Stack0 : nth_error r0 3=Some(cantor old prior_stack))
    by (unfold r0; rewrite nth_after_dispatch by lia; exact Stack).
  assert (Code0 : nth_error r0 4=Some 1).
  { unfold r0. rewrite nth_error_app1 by (rewrite set_register_length; lia). apply nth_error_set_same. lia. }
  assert (A0 : nth_error r0 5=Some a) by (unfold r0; rewrite nth_after_dispatch by lia; exact A).
  assert (B0 : nth_error r0 6=Some b) by (unfold r0; rewrite nth_after_dispatch by lia; exact B).
  assert (C0 : nth_error r0 7=Some c) by (unfold r0; rewrite nth_after_dispatch by lia; exact C).
  assert (X0 : nth_error r0 8=Some 0) by (unfold r0; rewrite nth_after_dispatch by lia; exact X).
  assert (Y0 : nth_error r0 9=Some 0) by (unfold r0; rewrite nth_after_dispatch by lia; exact Y).
  assert (Z0 : nth_error r0 10=Some 0) by (unfold r0; rewrite nth_after_dispatch by lia; exact Z).
  destruct (source_gen_body_nonempty r0 old prior_stack a b c L0 Top0 Stack0 Code0 A0 B0 C0 X0 Y0)
    as [result [mid H]].
  destruct H as [First H]. destruct H as [Tail H]. destruct H as [Len1 H].
  destruct H as [Top1 H]. destruct H as [Stack1 H]. destruct H as [Code1 H].
  destruct H as [A1 H]. destruct H as [B1 H]. destruct H as [C1 H].
  destruct H as [X1 H]. destruct H as [Y1 [Frame Suffix]].
  assert (Z1 : nth_error result 10=Some 0) by (rewrite (Frame 10) by lia; exact Z0).
  assert (F0 : nth_error result 0=nth_error rs 0).
  { rewrite (Frame 0) by lia. unfold r0. now rewrite nth_after_dispatch by lia. }
  assert (F1 : nth_error result 1=nth_error rs 1).
  { rewrite (Frame 1) by lia. unfold r0. now rewrite nth_after_dispatch by lia. }
  assert (Run : SourceProgramRuns (main_switch_pc,rs) (loop_return main_switch_pc,result)).
  { eapply source_program_runs_trans; [exact Switch|]. eapply source_program_next; eassumption. }
  destruct (source_runs_zero_suffix _ _ Run Len) as [pad [Pad _]].
  exists result,pad. cbn [execute_instruction fst snd]. repeat split; assumption.
Qed.

Theorem source_case_gen : InstructionCase 2.
Proof.
  intros rs old prior a b c Len Top Stack Code A B C X Y Z.
  destruct (source_gen_exec_instruction rs old prior a b c Len Top Stack Code A B C X Y Z)
    as [result [pad [Run [L [T [S [O [X' [Y' [Z' [F0 [F1 Suffix]]]]]]]]]]]].
  exists result,pad. repeat split; assumption.
Qed.

Print Assumptions source_gen_exec_instruction.
Print Assumptions source_case_gen.
