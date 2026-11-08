(** End-to-end halting theorem for the separately repaired 1,399-state TM.
    The original 1,385-state machine is a different, unchanged artifact. *)
From Stdlib Require Import Lists.List.
From Berkeley Require Import ProofFormula AugmentedLogic GenericSearch RepairedSearchProof StandardND StandardAugEquivalence.
From Repair Require Import Machine RepairedGen SearchMachineProof SearchMachineSwitch SearchMachineUnion.
Import ListNotations.

Theorem source_iteration_contract : SourceIterationContract.
Proof.
  apply source_iteration_contract_from_switch, source_switch_from_cases_under_gen, source_case_gen.
Qed.

Theorem repaired_blank_halts_iff_numeric_inconsistent :
  New.halts new_tm New.c0 <-> GenericInconsistent repaired_axiom.
Proof.
  apply conditional_blank_halts_iff_numeric_inconsistent, source_iteration_contract.
Qed.

Theorem repaired_blank_halts_iff_augmented_target :
  New.halts new_tm New.c0 <-> AugProvable (FMember 0 0).
Proof.
  rewrite repaired_blank_halts_iff_numeric_inconsistent. unfold GenericInconsistent.
  apply repaired_numeric_iff_augmented_target.
Qed.

Theorem repaired_blank_halts_iff_augmented_inconsistency :
  New.halts new_tm New.c0 <-> exists p, AugProvable p /\ AugProvable (FNeg p).
Proof.
  rewrite repaired_blank_halts_iff_numeric_inconsistent.
  rewrite <- GenericSearch.abstract_search_halting_iff_numeric_inconsistent.
  apply repaired_abstract_search_iff_augmented_inconsistency.
Qed.

(** StandardND uses the exact finite source schemas numbered 14 and above;
    the separate identification of those formulas with the intended
    conventional set-theory sentence remains a further obligation. *)
Theorem repaired_blank_halts_iff_standard_presentation_inconsistency :
  New.halts new_tm New.c0 <-> exists p, StandardND [] p /\ StandardND [] (FNeg p).
Proof.
  rewrite repaired_blank_halts_iff_augmented_inconsistency. split; intros [p [A B]];
    exists p; split; now apply augmented_iff_standard_theorem.
Qed.

Print Assumptions source_iteration_contract.
Print Assumptions repaired_blank_halts_iff_numeric_inconsistent.
Print Assumptions repaired_blank_halts_iff_augmented_target.
Print Assumptions repaired_blank_halts_iff_augmented_inconsistency.
Print Assumptions repaired_blank_halts_iff_standard_presentation_inconsistency.
