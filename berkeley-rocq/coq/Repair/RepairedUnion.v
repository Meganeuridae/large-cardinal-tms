(** Uniform literal switch contract; only GEN is parameterized until its
    independent source-body theorem is supplied. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import Syntax CompilerRegisters ConstructorArithmetic ConstructorRegisters ProofSearchSyntax ProofSearchProgram GenericSearch RepairedSearchProof.
From Repair Require Import SyntaxData CompilerExecution ConstructorTokens ConstructorControl SearchSelect GrammarExecutionDispatch GrammarExecutionAxioms GrammarExecutionProofSearch GrammarExecutionMPTokens GrammarExecutionMPInstruction GuardEmitter GuardInstruction SourceExecution.
Import ListNotations.

Definition repair_execute := GenericSearch.execute_instruction repaired_axiom.
Lemma repair_execute_eq_old op a b c st : op<>27 ->
  repair_execute (op,a,b,c) st = ProofSearchProgram.execute_instruction (op,a,b,c) st.
Proof.
  intro Different. destruct op as [|[|[|i]]]; try reflexivity.
  unfold repair_execute,GenericSearch.execute_instruction,repaired_axiom,ProofSearchProgram.execute_instruction.
  assert (E : (i =? 24)=false) by (apply Nat.eqb_neq; lia). rewrite E. reflexivity.
Qed.

Definition InstructionCase op : Prop := forall rs old prior_stack a b c,
  11<=length rs -> nth_error rs 2=Some 0 -> nth_error rs 3=Some(cantor old prior_stack) ->
  nth_error rs 4=Some op -> nth_error rs 5=Some a -> nth_error rs 6=Some b -> nth_error rs 7=Some c ->
  nth_error rs 8=Some 0 -> nth_error rs 9=Some 0 -> nth_error rs 10=Some 0 ->
  exists result pad,
    SourceProgramRuns (main_switch_pc,rs) (loop_return main_switch_pc,result) /\ 11<=length result /\
    nth_error result 2=Some(fst (repair_execute (op,a,b,c) (old,prior_stack))) /\
    nth_error result 3=Some(snd (repair_execute (op,a,b,c) (old,prior_stack))) /\
    nth_error result 8=Some 0 /\ nth_error result 9=Some 0 /\ nth_error result 10=Some 0 /\
    nth_error result 0=nth_error rs 0 /\ nth_error result 1=nth_error rs 1 /\
    skipn 11 result=skipn 11 rs++repeat 0 pad.

Lemma source_case_zero : InstructionCase 0.
Proof.
  intros rs old prior a b c Len Top Stack Code A B C X Y Z.
  destruct (source_zero_exec_instruction rs old prior a b c Len Top Stack Code X Y)
    as [result [pad [Run [L [T [S [O [X' [Y' [Frame Suffix]]]]]]]]]].
  assert (Z' : nth_error result 10=Some 0) by (rewrite (Frame 10) by lia; exact Z).
  assert (F0 : nth_error result 0=nth_error rs 0) by (apply Frame; lia).
  assert (F1 : nth_error result 1=nth_error rs 1) by (apply Frame; lia).
  exists result,pad. rewrite !repair_execute_eq_old by lia. repeat split; assumption.
Qed.

Lemma source_case_mp : InstructionCase 1.
Proof.
  intros rs old prior a b c Len Top Stack Code A B C X Y Z.
  destruct (source_mp_exec_instruction rs old prior a b c Len Top Stack Code A B C X Y Z)
    as [result [pad [Run [L [T [S [O [X' [Y' [Z' [F0 [F1 Suffix]]]]]]]]]]]].
  exists result,pad. rewrite !repair_execute_eq_old by lia. repeat split; assumption.
Qed.

Lemma source_case_axiom i f : nth_error candidate_axioms i = Some f -> InstructionCase (3+i).
Proof.
  intros F rs old prior a b c Len Top Stack Code A B C X Y Z.
  assert (Bound : i<24) by (rewrite <- candidate_axioms_count; apply nth_error_Some; rewrite F; discriminate).
  assert (View : constructor_view (instruction_params a b c) rs (CR 0 (cantor old prior) 0 0) rs).
  { eapply mp_initial_constructor_view; eassumption. }
  destruct (source_axiom_exec_instruction rs i f rs old prior a b c F Code View)
    as [result [pad [Run [L [T [S [O [X' [Y' [Frame Suffix]]]]]]]]]].
  assert (Z' : nth_error result 10=Some 0) by (rewrite (Frame 10) by lia; exact Z).
  assert (F0 : nth_error result 0=nth_error rs 0) by (apply Frame; lia).
  assert (F1 : nth_error result 1=nth_error rs 1) by (apply Frame; lia).
  exists result,pad. rewrite !repair_execute_eq_old by lia. repeat split; assumption.
Qed.

Lemma source_case_large k : InstructionCase (28+k).
Proof.
  intros rs old prior a b c Len Top Stack Code A B C X Y Z.
  destruct (source_large_exec_instruction rs old prior k a b c Len Top Stack Code X Y)
    as [result [pad [Run [L [T [S [O [X' [Y' [Frame Suffix]]]]]]]]]].
  assert (Z' : nth_error result 10=Some 0) by (rewrite (Frame 10) by lia; exact Z).
  assert (F0 : nth_error result 0=nth_error rs 0) by (apply Frame; lia).
  assert (F1 : nth_error result 1=nth_error rs 1) by (apply Frame; lia).
  exists result,pad. rewrite !repair_execute_eq_old by lia. repeat split; assumption.
Qed.

Lemma source_case_guard : InstructionCase 27.
Proof.
  intros rs old prior a b c Len Top Stack Code A B C X Y Z.
  destruct (repaired_guard_instruction rs old prior a b c Len Top Stack Code A B C X Y Z)
    as [result [pad [Run [L [T [S [O [X1 [Y1 [Z1 [F0 [F1 Suffix]]]]]]]]]]]].
  exists result,pad. unfold repair_execute,GenericSearch.execute_instruction,repaired_axiom.
  cbn. unfold guard_result,guard_formula_code,code_distinctor in T.
  destruct (Nat.eqb a b); cbn in *; repeat split; assumption.
Qed.

Theorem source_cases_under_gen : InstructionCase 2 -> forall op, InstructionCase op.
Proof.
  intros Gen [|[|[|i]]].
  - apply source_case_zero.
  - apply source_case_mp.
  - exact Gen.
  - destruct (nth_error candidate_axioms i) as [f|] eqn:F.
    + replace (S(S(S i))) with (3+i) by lia. now apply source_case_axiom with (f:=f).
    + apply nth_error_None in F. rewrite candidate_axioms_count in F.
      destruct (Nat.eq_dec i 24) as [->|N].
      * change (InstructionCase 27). apply source_case_guard.
      * replace (S(S(S i))) with (28+(i-25)) by lia. apply source_case_large.
Qed.

Lemma main_switch_return_pc : loop_return main_switch_pc = repeat true 19.
Proof. vm_compute. reflexivity. Qed.

Lemma lift_completed_switch_run rs result :
  SourceProgramRuns (main_switch_pc,rs) (loop_return main_switch_pc,result) ->
  SourceProgramRuns (repeat true 18,rs) (repeat true 19,result).
Proof.
  intro Run. rewrite main_switch_return_pc in Run.
  eapply constructor_unpad_nonempty_run with (pad:=1).
  - change (SourceProgramRuns (repeat true 18++[false],rs) (repeat true 19,result)). exact Run.
  - intro E. apply (f_equal fst) in E. vm_compute in E. discriminate.
Qed.

Theorem source_all_opcodes_under_gen : InstructionCase 2 -> forall op rs old prior_stack a b c,
  11<=length rs -> nth_error rs 2=Some 0 -> nth_error rs 3=Some(cantor old prior_stack) ->
  nth_error rs 4=Some op -> nth_error rs 5=Some a -> nth_error rs 6=Some b -> nth_error rs 7=Some c ->
  nth_error rs 8=Some 0 -> nth_error rs 9=Some 0 -> nth_error rs 10=Some 0 ->
  exists result pad,
    SourceProgramRuns (repeat true 18,rs) (repeat true 19,result) /\ 11<=length result /\
    nth_error result 2=Some(fst (repair_execute (op,a,b,c) (old,prior_stack))) /\
    nth_error result 3=Some(snd (repair_execute (op,a,b,c) (old,prior_stack))) /\
    nth_error result 8=Some 0 /\ nth_error result 9=Some 0 /\ nth_error result 10=Some 0 /\
    nth_error result 0=nth_error rs 0 /\ nth_error result 1=nth_error rs 1 /\
    skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  intros Gen op rs old prior a b c Len Top Stack Code A B C X Y Z.
  destruct (source_cases_under_gen Gen op rs old prior a b c Len Top Stack Code A B C X Y Z)
    as [result [pad [Run Facts]]].
  exists result,pad. split; [now apply lift_completed_switch_run|exact Facts].
Qed.

Print Assumptions source_cases_under_gen.
Print Assumptions lift_completed_switch_run.
Print Assumptions source_all_opcodes_under_gen.
