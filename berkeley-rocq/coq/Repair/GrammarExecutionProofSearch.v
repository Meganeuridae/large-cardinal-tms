(** Link completed axiom/default switch runs to the numeric search instruction. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import Syntax CompilerRegisters ConstructorArithmetic ConstructorRegisters ProofSearchSyntax ProofSearchProgram.
From Repair Require Import SyntaxData CompilerData CompilerExecution ConstructorStreams ConstructorTokens ConstructorFrame SearchSelect GrammarExecutionDispatch GrammarExecutionOpcodes GrammarExecutionAxioms GrammarExecutionInstruction SourceExecution.
Import ListNotations.

Lemma source_residual_roots_count : length source_residual_roots = 25.
Proof. vm_compute. reflexivity. Qed.
Local Opaque source_graph source_residual_roots.
Local Transparent candidate_axioms.

Theorem source_axiom_exec_instruction frame i f rs old prior_stack a b c :
  nth_error candidate_axioms i = Some f -> nth_error rs 4 = Some (3+i) ->
  constructor_view (instruction_params a b c) frame (CR 0 (cantor old prior_stack) 0 0) rs ->
  exists result pad,
    SourceProgramRuns (main_switch_pc,rs) (loop_return main_switch_pc,result) /\
    11<=length result /\
    nth_error result 2 = Some(fst (execute_instruction (3+i,a,b,c) (old,prior_stack))) /\
    nth_error result 3 = Some(snd (execute_instruction (3+i,a,b,c) (old,prior_stack))) /\
    nth_error result 4 = Some 0 /\ nth_error result 8 = Some 0 /\ nth_error result 9 = Some 0 /\
    outside_select rs result /\ skipn 11 result = skipn 11 rs ++ repeat 0 pad.
Proof.
  intros F Code View.
  assert (I : i<24).
  { rewrite <- candidate_axioms_count. apply nth_error_Some. rewrite F. discriminate. }
  change (nth_error Berkeley.SyntaxData.candidate_axioms i = Some f) in F.
  assert (SomeRoot : nth_error source_residual_roots i <> None).
  { apply nth_error_Some. rewrite source_residual_roots_count. lia. }
  destruct (nth_error source_residual_roots i) as [root|] eqn:Root; [|contradiction].
  destruct (source_axiom_instruction (instruction_params a b c) frame i f root rs old prior_stack
    F Root Code View) as [result [pad [Run [Len [Top [Stack [Opcode [X [Y [Frame Suffix]]]]]]]]]].
  exists result,pad. repeat split; try assumption.
  - replace (3+i) with (S(S(S i))) by lia.
    cbn [execute_instruction]. unfold instantiated_axiom. rewrite F. exact Top.
  - replace (3+i) with (S(S(S i))) by lia.
    cbn [execute_instruction]. unfold instantiated_axiom. rewrite F. exact Stack.
Qed.

Theorem source_zero_exec_instruction rs old prior_stack a b c :
  11<=length rs -> nth_error rs 2=Some 0 -> nth_error rs 3=Some(cantor old prior_stack) ->
  nth_error rs 4=Some 0 -> nth_error rs 8=Some 0 -> nth_error rs 9=Some 0 ->
  exists result pad,
    SourceProgramRuns (main_switch_pc,rs) (loop_return main_switch_pc,result) /\
    11<=length result /\
    nth_error result 2=Some(fst (execute_instruction (0,a,b,c) (old,prior_stack))) /\
    nth_error result 3=Some(snd (execute_instruction (0,a,b,c) (old,prior_stack))) /\
    nth_error result 4=Some 0 /\ nth_error result 8=Some 0 /\ nth_error result 9=Some 0 /\
    outside_select rs result /\ skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  intros Len Top Stack Code X Y. exists rs,0. cbn [execute_instruction repeat fst snd].
  rewrite app_nil_r. repeat split; try assumption.
  - now apply switch_default_opcode.
Qed.

Theorem source_large_exec_instruction rs old prior_stack k a b c :
  11<=length rs -> nth_error rs 2=Some 0 -> nth_error rs 3=Some(cantor old prior_stack) ->
  nth_error rs 4=Some (28+k) -> nth_error rs 8=Some 0 -> nth_error rs 9=Some 0 ->
  exists result pad,
    SourceProgramRuns (main_switch_pc,rs) (loop_return main_switch_pc,result) /\
    11<=length result /\
    nth_error result 2=Some(fst (execute_instruction (28+k,a,b,c) (old,prior_stack))) /\
    nth_error result 3=Some(snd (execute_instruction (28+k,a,b,c) (old,prior_stack))) /\
    nth_error result 4=Some k /\ nth_error result 8=Some 0 /\ nth_error result 9=Some 0 /\
    outside_select rs result /\ skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  intros Len Top Stack Code X Y.
  assert (Absent : nth_error candidate_axioms (25+k) = None).
  { apply nth_error_None. rewrite candidate_axioms_count. lia. }
  change (nth_error Berkeley.SyntaxData.candidate_axioms (25+k) = None) in Absent.
  set (result := set_register 4 k rs ++ repeat 0 28).
  pose proof (switch_out_of_range k rs Len Code) as Run. fold result in Run.
  exists result,28. repeat split; try assumption.
  - unfold result. rewrite app_length,set_register_length,repeat_length. lia.
  - replace (28+k) with (S(S(S (25+k)))) by lia.
    cbn [execute_instruction]. unfold instantiated_axiom. rewrite Absent.
    unfold result. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    now rewrite nth_error_set_other by lia.
  - replace (28+k) with (S(S(S (25+k)))) by lia.
    cbn [execute_instruction]. unfold instantiated_axiom. rewrite Absent.
    unfold result. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    now rewrite nth_error_set_other by lia.
  - unfold result. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    apply nth_error_set_same. lia.
  - unfold result. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    now rewrite nth_error_set_other by lia.
  - unfold result. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    now rewrite nth_error_set_other by lia.
  - unfold outside_select, result. intros i I I2 I3 I4 I8 I9.
    rewrite nth_error_app1 by (rewrite set_register_length; lia).
    now rewrite nth_error_set_other by lia.
  - unfold result. rewrite skipn_app.
    assert (Z : 11-length (set_register 4 k rs)=0) by (rewrite set_register_length; lia).
    rewrite Z, (skipn_set_below 11 4 k rs) by lia. reflexivity.
Qed.

Print Assumptions source_axiom_exec_instruction.
Print Assumptions source_zero_exec_instruction.
Print Assumptions source_large_exec_instruction.
