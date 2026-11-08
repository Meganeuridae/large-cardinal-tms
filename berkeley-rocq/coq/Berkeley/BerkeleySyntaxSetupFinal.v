(** The internal syntax setup is constructed from the actual first-order ZF
    prefix. Its omega can be nonstandard and all recursion is internal. *)
From Stdlib Require Import Lists.List.
From Berkeley Require Import Syntax SyntaxData ProofFormula ProofPresentation FormulaSemantics BerkeleySyntaxZFBase
  BerkeleySyntaxZFPairClosedBound BerkeleySyntaxSetup BerkeleySyntaxUniform.
Import ListNotations.

Section FinalSetup.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Theorem zf_formula_setup_exists (seed:D) : RelFormulaSetupExists R.
Proof.
  apply (zf_formula_setup_from_pair_bounds R EM Model seed).
  intros w Omega. exact (zf_pair_closed_bound_exists R EM Model w w Omega).
Qed.

Theorem candidate_axiom_iff_uniform_berkeley rho vars holes :
  FolHolds R rho (independent_instance vars holes (nth 23 candidate_axioms (Hole 0))) <-> RelUniformBerkeley R.
Proof. apply (candidate_axiom_iff_uniform_internal R EM Model rho vars holes), (zf_formula_setup_exists (rho 0)). Qed.
Theorem original_axiom_iff_uniform_berkeley rho vars holes :
  FolHolds R rho (independent_instance vars holes (nth 23 original_axioms (Hole 0))) <-> RelUniformBerkeley R.
Proof. apply (original_axiom_iff_uniform_internal R EM Model rho vars holes), (zf_formula_setup_exists (rho 0)). Qed.
End FinalSetup.

Print Assumptions zf_formula_setup_exists.
Print Assumptions candidate_axiom_iff_uniform_berkeley.
Print Assumptions original_axiom_iff_uniform_berkeley.
