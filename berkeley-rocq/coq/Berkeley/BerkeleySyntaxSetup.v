(** Assembly of an internal formula-coding setup from omega, successor tags,
    and a pair-closed bound containing omega. *)
From Stdlib Require Import Lists.List.
From Berkeley Require Import Syntax SyntaxData ProofFormula ProofPresentation FormulaSemantics BerkeleySyntaxSets
  BerkeleySyntaxOmega BerkeleySyntaxSentence BerkeleySyntaxNumerals BerkeleySyntaxTags BerkeleySyntaxZFTags BerkeleySyntaxZFBase
  BerkeleySyntaxZFOmega BerkeleySyntaxZFFormulaBound BerkeleySyntaxUniform.
Import ListNotations.

Definition RelPairBoundOverOmega {D} (R:D->D->Prop) := forall w, RelOmega R w ->
  exists bound, RelPairClosed R bound /\ RelSubset R w bound.

Section Setup.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Theorem zf_formula_setup_from_pair_bounds (seed:D) : RelPairBoundOverOmega R -> RelFormulaSetupExists R.
Proof.
  intro Bounds. destruct (zf_prefix_omega_exists R EM Model seed) as [w Omega].
  destruct (zf_prefix_tag_chain_exists R EM Model w Omega) as [te [tm [tn [ti [ta Tags]]]]].
  destruct (Bounds w Omega) as [bound [Closed Sub]].
  pose proof (zf_prefix_extensional R EM Model) as Ext. pose proof (proj1 Omega) as Ind.
  assert (TagIn : forall n z, nth_error [te;tm;tn;ti;ta] n=Some z -> R z w).
  { intros n z Nz. eapply (standard_numeral_in_omega R Ext w n z Ind).
    eapply actual_tags_numerals; [exact Tags|exact Nz]. }
  assert (TE : R te bound) by (apply Sub; eapply (TagIn 0); reflexivity).
  assert (TM : R tm bound) by (apply Sub; eapply (TagIn 1); reflexivity).
  assert (TN : R tn bound) by (apply Sub; eapply (TagIn 2); reflexivity).
  assert (TI : R ti bound) by (apply Sub; eapply (TagIn 3); reflexivity).
  assert (TA : R ta bound) by (apply Sub; eapply (TagIn 4); reflexivity).
  destruct (zf_formula_set_from_pair_closed R EM Model bound w te tm tn ti ta Closed Sub TE TM TN TI TA) as [f Formulas].
  exists w,te,tm,tn,ti,ta,f. now split.
Qed.

Corollary candidate_axiom_iff_uniform_from_pair_bounds rho vars holes : RelPairBoundOverOmega R ->
  (FolHolds R rho (independent_instance vars holes (nth 23 candidate_axioms (Hole 0))) <-> RelUniformBerkeley R).
Proof.
  intro Bounds. apply (candidate_axiom_iff_uniform_internal R EM Model rho vars holes).
  now apply (zf_formula_setup_from_pair_bounds (rho 0)).
Qed.
End Setup.

Print Assumptions zf_formula_setup_from_pair_bounds.
Print Assumptions candidate_axiom_iff_uniform_from_pair_bounds.
