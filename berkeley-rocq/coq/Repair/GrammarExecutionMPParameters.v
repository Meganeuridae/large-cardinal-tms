(** Source modus-ponens setup: the two cparam calls recover the minor and
    major premises from the numeric theorem stack. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerRegisters ConstructorArithmetic CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerExecution CompilerLoopBase ConstructorControl ConstructorFrame SearchCParamControl SearchCParamOne SearchCParam GrammarExecutionBodies SourceExecution.
Import ListNotations.

Definition outside_mp_parameters (before after : list nat) := forall i, i<11 ->
  i<>3 -> i<>6 -> i<>7 -> i<>8 -> i<>9 -> nth_error after i=nth_error before i.

Theorem source_mp_parameters_nonempty rs a b c minor major rest :
  11<=length rs -> nth_error rs 2=Some 0 ->
  nth_error rs 3=Some(cantor minor (cantor major rest)) -> nth_error rs 4=Some 1 ->
  nth_error rs 5=Some a -> nth_error rs 6=Some b -> nth_error rs 7=Some c ->
  nth_error rs 8=Some 0 -> nth_error rs 9=Some 0 ->
  exists result mid, SourceProgramStep (special_body_cursor 1 0,rs) mid /\
    SourceProgramRuns mid (special_body_cursor 1 2,result) /\ 11<=length result /\
    nth_error result 2=Some 0 /\ nth_error result 3=Some rest /\ nth_error result 4=Some 1 /\
    nth_error result 5=Some a /\ nth_error result 6=Some major /\ nth_error result 7=Some minor /\
    nth_error result 8=Some 0 /\ nth_error result 9=Some 0 /\ outside_mp_parameters rs result /\
    exists pad, skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  intros Len Top Stack Opcode A B C X Y.
  pose proof (special_body_paths 1 0 650 (or_introl eq_refl) ltac:(reflexivity)) as P1.
  destruct (source_cparam_nonempty (special_body_context 1 0) 650 7 635 50 rs 1
    (cantor minor (cantor major rest)) c cparam_layout_3 P1
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Len Opcode Stack C X Y)
    as [r1 [mid H1]].
  destruct H1 as [First H1]. destruct H1 as [Run1 H1].
  destruct H1 as [L1 H1]. destruct H1 as [C1 H1]. destruct H1 as [S1 H1].
  destruct H1 as [P1v H1]. destruct H1 as [X1 H1]. destruct H1 as [Y1 H1].
  destruct H1 as [F1 [pad1 Tail1]].
  cbn [cparam_stack_after cparam_value_after Nat.eqb] in S1,P1v.
  rewrite uncantor_cantor in S1,P1v. cbn [fst snd] in S1,P1v.
  rewrite special_body_context_return in Run1.
  assert (T1 : nth_error r1 2=Some 0) by (rewrite (F1 2) by lia; exact Top).
  assert (A1 : nth_error r1 5=Some a) by (rewrite (F1 5) by lia; exact A).
  assert (B1 : nth_error r1 6=Some b) by (rewrite (F1 6) by lia; exact B).
  pose proof (special_body_paths 1 1 652 (or_introl eq_refl) ltac:(reflexivity)) as P2.
  destruct (source_cparam_nonempty (special_body_context 1 1) 652 6 634 20 r1 1
    (cantor major rest) b cparam_layout_2 P2
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) L1 C1 S1 B1 X1 Y1)
    as [result [mid2 H2]].
  destruct H2 as [First2 H2]. destruct H2 as [Run2 H2].
  destruct H2 as [L2 H2]. destruct H2 as [C2 H2]. destruct H2 as [S2 H2].
  destruct H2 as [P2v H2]. destruct H2 as [X2 H2]. destruct H2 as [Y2 H2].
  destruct H2 as [F2 [pad2 Tail2]].
  cbn [cparam_stack_after cparam_value_after Nat.eqb] in S2,P2v.
  rewrite uncantor_cantor in S2,P2v. cbn [fst snd] in S2,P2v.
  rewrite special_body_context_return in Run2.
  assert (T2 : nth_error result 2=Some 0) by (rewrite (F2 2) by lia; exact T1).
  assert (A2 : nth_error result 5=Some a) by (rewrite (F2 5) by lia; exact A1).
  assert (P7 : nth_error result 7=Some minor) by (rewrite (F2 7) by lia; exact P1v).
  assert (AllTail : SourceProgramRuns mid (special_body_cursor 1 2,result)).
  { eapply source_program_runs_trans; [exact Run1|]. eapply source_program_next with (t:=mid2).
    - eapply constructor_unpad_first_step with (pad:=1).
      unfold special_body_context in First2. exact First2.
    - exact Run2. }
  assert (AllRun : SourceProgramRuns (special_body_cursor 1 0,rs) (special_body_cursor 1 2,result)).
  { eapply source_program_next; [eapply constructor_unpad_first_step with (pad:=1);
      unfold special_body_context in First; exact First|exact AllTail]. }
  destruct (source_runs_zero_suffix _ _ AllRun Len) as [pad [Pad _]].
  exists result,mid. repeat split; try assumption.
  - eapply constructor_unpad_first_step with (pad:=1). unfold special_body_context in First. exact First.
  - unfold outside_mp_parameters. intros i I I3 I6 I7 I8 I9.
    rewrite (F2 i) by lia. now apply F1.
  - now exists pad.
Qed.
Print Assumptions source_mp_parameters_nonempty.
