(** The uniform checked switch yields the full iteration simulation. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import ConstructorArithmetic ProofSearchSyntax GenericSearch RepairedSearchProof.
From Repair Require Import Machine CompilerExecution GrammarExecutionDispatch RepairedUnion SearchPrimitivesHalt SearchMachinePrefix SearchMachineProof SearchMachineSwitch SourceExecution.
Import ListNotations.

Theorem source_switch_from_cases_under_gen : InstructionCase 2 -> SourceSwitchContract.
Proof.
  intros Gen op a b c tail next old prior rs V.
  unfold source_switch_view in V.
  destruct V as [L [N [Q [T [S [O [A [B [C [X [Y Z]]]]]]]]]]].
  destruct (source_cases_under_gen Gen op rs old prior a b c L T S O A B C X Y Z)
    as [result [pad [Run [Len [Top [Stack [X' [Y' [Z' [N' [Q' Suffix]]]]]]]]]]].
  rewrite main_switch_return_pc in Run.
  exists result. split.
  - change (SourceProgramRuns (main_switch_pc,rs) (repeat true 19,result)). exact Run.
  - unfold source_search_view. cbn [pending_program next_program proof_stack].
    repeat split; try assumption; congruence.
Qed.

Theorem gen_implies_blank_halts_iff_numeric_inconsistent : InstructionCase 2 ->
  (New.halts new_tm New.c0 <-> (GenericInconsistent repaired_axiom)).
Proof.
  intro Gen. apply conditional_blank_halts_iff_numeric_inconsistent.
  apply source_iteration_contract_from_switch, source_switch_from_cases_under_gen, Gen.
Qed.

Print Assumptions source_switch_from_cases_under_gen.
Print Assumptions gen_implies_blank_halts_iff_numeric_inconsistent.
