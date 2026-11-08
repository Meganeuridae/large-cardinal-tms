(** Full axiom opcode execution through select and the switch return. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import Syntax CompilerSyntax CompilerRegisters ConstructorArithmetic ConstructorRegisters CompilerReverse.
From Repair Require Import SyntaxData CompilerData CompilerReverse CompilerContexts CompilerExecution CompilerLoopBase ConstructorControl ConstructorStreams ConstructorTokens ConstructorFrame SearchSelect SearchSelectBranch GrammarExecutionBlocks GrammarExecutionDispatch GrammarExecutionAxioms GrammarExecutionConcrete GrammarExecutionSelect SourceExecution.
Import ListNotations.
Local Opaque source_graph source_residual_roots candidate_axioms.

Lemma axiom_select_return i : loop_return (axiom_select_context i) = axiom_break_word i.
Proof.
  unfold axiom_select_context, axiom_break_word.
  replace (axiom_parent_pc i++[true;false]) with ((axiom_parent_pc i++[true])++[false])
    by now rewrite <- app_assoc.
  rewrite sequence_left_return. now rewrite <- app_assoc.
Qed.

Theorem source_axiom_instruction params frame i f root rs old prior_stack :
  nth_error candidate_axioms i = Some f -> nth_error source_residual_roots i = Some root ->
  nth_error rs 4 = Some (3+i) ->
  constructor_view params frame (CR 0 (cantor old prior_stack) 0 0) rs ->
  exists result pad,
    SourceProgramRuns (main_switch_pc,rs) (loop_return main_switch_pc,result) /\
    11<=length result /\ nth_error result 2 = Some(formula_code params f) /\
    nth_error result 3 = Some(cantor old prior_stack) /\ nth_error result 4 = Some 0 /\
    nth_error result 8 = Some 0 /\ nth_error result 9 = Some 0 /\
    outside_select rs result /\ skipn 11 result = skipn 11 rs ++ repeat 0 pad.
Proof.
  intros F Root Code View.
  assert (I : i < 24).
  { rewrite <- candidate_axioms_count. apply nth_error_Some. rewrite F. discriminate. }
  pose proof View as InitialView. destruct InitialView as [Len _].
  destruct (actual_source_switch_constructs_axiom params frame i f root rs 0 (cantor old prior_stack)
    F Root Code View) as [r1 [pad1 [Emit [EmitView [EmitFrame EmitSuffix]]]]].
  destruct EmitView as [Len1 [Top1 [Stack1 [X1 [Y1 [X0 [Y0 [Frame1 Params1]]]]]]]].
  cbn [top stack scratch1 scratch2] in Top1,Stack1,X1,Y1.
  assert (Code1 : nth_error r1 4 = Some 1).
  { rewrite (Frame1 4) by lia.
    rewrite nth_error_app1 by (rewrite set_register_length; lia).
    apply nth_error_set_same. lia. }
  destruct (axiom_follow_paths i I) as [SelectPrefix _].
  destruct (source_select_nonempty (axiom_select_context i) r1
    (formula_code params f) 0 (cantor old prior_stack) 1
    SelectPrefix Len1 Top1 Stack1 Code1 X1 Y1)
    as [result [mid [First [Tail [Len2 [Top2 [Stack2 [Code2 [X2 [Y2 [Frame2 Suffix2]]]]]]]]]]].
  cbn [selected_top Nat.pred] in Top2,Code2. rewrite axiom_select_return in Tail.
  assert (RunSelect : SourceProgramRuns (axiom_parent_pc i++[true],r1)
      (axiom_break_word i,result)).
  { eapply source_program_next with (t:=mid); [|exact Tail].
    eapply constructor_unpad_first_step with (pad:=1).
    unfold axiom_select_context in First. change (SourceProgramStep ((axiom_parent_pc i++[true])++[false],r1) mid).
    rewrite <- app_assoc. exact First. }
  assert (Run : SourceProgramRuns (main_switch_pc,rs) (loop_return main_switch_pc,result)).
  { eapply source_program_runs_trans; [exact Emit|].
    eapply source_program_runs_trans; [exact RunSelect|].
    eapply source_program_next; [apply axiom_follow_break; exact I|constructor]. }
  destruct (source_runs_zero_suffix _ _ Run Len) as [pad [Suffix _]].
  exists result,pad. repeat split; try assumption.
  unfold outside_select, unchanged_outside_axiom in *.
  intros j J N2 N3 N4 N8 N9. rewrite Frame2 by assumption. apply EmitFrame; assumption.
Qed.

Print Assumptions source_axiom_instruction.
