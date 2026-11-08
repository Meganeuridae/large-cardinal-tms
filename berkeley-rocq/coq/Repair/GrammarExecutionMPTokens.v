(** Three actual constructor subtrees build the MP comparison formula. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import CompilerRegisters ConstructorArithmetic ConstructorRegisters ProofSearchSyntax.
From Repair Require Import CompilerData CompilerExecution CompilerLoopBase ConstructorStreams ConstructorCons ConstructorTokens ConstructorFrame GrammarExecutionBlocks GrammarExecutionBodies GrammarExecutionConcrete SourceExecution.
Import ListNotations.

Lemma run_one_token params tok initial final : token_step params tok initial = Some final ->
  run_tokens params [tok] initial = Some final.
Proof. intro E. cbn [run_tokens bind]. now rewrite E. Qed.

Lemma mp_initial_constructor_view rs a major minor rest :
  11<=length rs -> nth_error rs 2=Some 0 -> nth_error rs 3=Some rest ->
  nth_error rs 5=Some a -> nth_error rs 6=Some major -> nth_error rs 7=Some minor ->
  nth_error rs 8=Some 0 -> nth_error rs 9=Some 0 ->
  constructor_view (instruction_params a major minor) rs (CR 0 rest 0 0) rs.
Proof.
  intros Len Top Stack A B C X Y. unfold constructor_view. cbn [top stack scratch1 scratch2].
  repeat split; try assumption.
  intros n Range. destruct n as [|[|[|[|n]]]]; cbn [instruction_params] in *; try lia; assumption.
Qed.

Theorem source_mp_tokens_nonempty rs a major minor rest :
  11<=length rs -> nth_error rs 2=Some 0 -> nth_error rs 3=Some rest ->
  nth_error rs 4=Some 1 -> nth_error rs 5=Some a -> nth_error rs 6=Some major ->
  nth_error rs 7=Some minor -> nth_error rs 8=Some 0 -> nth_error rs 9=Some 0 ->
  exists result mid, SourceProgramStep (special_body_cursor 1 2,rs) mid /\
    SourceProgramRuns mid (special_body_cursor 1 5,result) /\
    11<=length result /\ nth_error result 2=Some(code_imp minor a) /\
    nth_error result 3=Some(cantor 0 rest) /\ nth_error result 4=Some 1 /\
    nth_error result 5=Some a /\ nth_error result 6=Some major /\ nth_error result 7=Some minor /\
    nth_error result 8=Some 0 /\ nth_error result 9=Some 0 /\ outside_cons rs result /\
    exists pad, skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  intros Len Top Stack Code A B C X Y.
  set (params := instruction_params a major minor).
  set (View := constructor_view params rs).
  assert (V0 : View (CR 0 rest 0 0) rs).
  { unfold View,params. eapply mp_initial_constructor_view; eassumption. }
  assert (R11 : In (11,51) source_token_roots) by (vm_compute; tauto).
  assert (R9 : In (9,17) source_token_roots) by (vm_compute; tauto).
  assert (R3 : In (3,44) source_token_roots) by (vm_compute; tauto).
  assert (E11 : run_tokens params [11] (CR 0 rest 0 0) =
      Some(CR minor (cantor 0 rest) 0 0)).
  { apply run_one_token. pose proof (parameter_token_correct params 3 0 rest ltac:(lia)) as E.
    change (token_step params 11 (CR 0 rest 0 0) =
      Some(CR (params 3) (cantor 0 rest) 0 0)) in E.
    unfold params in E. cbn [instruction_params] in E. exact E. }
  destruct (special_body_block params View 1 2 51 [11]
    (CR 0 rest 0 0) (CR minor (cantor 0 rest) 0 0) rs
    ltac:(left;reflexivity) ltac:(reflexivity) (actual_source_token_block params rs 11 51 R11) V0 E11)
    as [mid1 [r1 [First1 [Tail1 V1]]]].
  assert (E9 : run_tokens params [9] (CR minor (cantor 0 rest) 0 0) =
      Some(CR a (cantor minor (cantor 0 rest)) 0 0)).
  { apply run_one_token. pose proof (parameter_token_correct params 1 minor (cantor 0 rest) ltac:(lia)) as E.
    change (token_step params 9 (CR minor (cantor 0 rest) 0 0) =
      Some(CR (params 1) (cantor minor (cantor 0 rest)) 0 0)) in E.
    unfold params in E. cbn [instruction_params] in E. exact E. }
  destruct (special_body_block params View 1 3 17 [9]
    (CR minor (cantor 0 rest) 0 0) (CR a (cantor minor (cantor 0 rest)) 0 0) r1
    ltac:(left;reflexivity) ltac:(reflexivity) (actual_source_token_block params rs 9 17 R9) V1 E9)
    as [mid2 [r2 [First2 [Tail2 V2]]]].
  assert (E3 : run_tokens params [3] (CR a (cantor minor (cantor 0 rest)) 0 0) =
      Some(CR (code_imp minor a) (cantor 0 rest) 0 0)).
  { apply run_one_token. change (source_binary 2 (CR a (cantor minor (cantor 0 rest)) 0 0) =
      Some(CR (code_imp minor a) (cantor 0 rest) 0 0)).
    unfold code_imp. apply source_binary_correct. }
  destruct (special_body_block params View 1 4 44 [3]
    (CR a (cantor minor (cantor 0 rest)) 0 0) (CR (code_imp minor a) (cantor 0 rest) 0 0) r2
    ltac:(left;reflexivity) ltac:(reflexivity) (actual_source_token_block params rs 3 44 R3) V2 E3)
    as [mid3 [result [First3 [Tail3 V3]]]].
  assert (AllTail : SourceProgramRuns mid1 (special_body_cursor 1 5,result)).
  { eapply source_program_runs_trans; [exact Tail1|]. eapply source_program_next with (t:=mid2); [exact First2|].
    eapply source_program_runs_trans; [exact Tail2|]. eapply source_program_next; eassumption. }
  assert (All : SourceProgramRuns (special_body_cursor 1 2,rs) (special_body_cursor 1 5,result)).
  { eapply source_program_next; eassumption. }
  destruct (source_runs_zero_suffix _ _ All Len) as [pad [Suffix _]].
  unfold View,constructor_view in V3.
  destruct V3 as [L [T [S [X' [Y' [_ [_ [Frame Params]]]]]]]].
  cbn [top stack scratch1 scratch2] in T,S,X',Y'.
  assert (C' : nth_error result 4=Some 1) by (rewrite (Frame 4) by lia; exact Code).
  assert (A' : nth_error result 5=Some a) by (rewrite (Frame 5) by lia; exact A).
  assert (B' : nth_error result 6=Some major) by (rewrite (Frame 6) by lia; exact B).
  assert (P' : nth_error result 7=Some minor) by (rewrite (Frame 7) by lia; exact C).
  exists result,mid1. repeat split; try assumption. now exists pad.
Qed.

Print Assumptions source_mp_tokens_nonempty.
