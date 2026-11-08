(** Models of the independently normalized conventional axiom predicate are
    exactly the literal ZF-prefix models with the intrinsic internal Berkeley
    property. All semantic classical reasoning is an explicit argument. *)
From Berkeley Require Import ProofFormula FormulaSemantics LogicSemantics
  AugmentedSemantics ZFConventional BerkeleySyntaxZFBase BerkeleySyntaxUniform BerkeleySyntaxModel.

Definition ConventionalModel {D} (R:D->D->Prop) :=
  forall p, ConventionalAxiom p -> forall rho, FolHolds R rho p.

Section Models.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.

Theorem conventional_model_iff_source :
  ConventionalModel R <-> satisfies_nonlogical_schemas R.
Proof.
  split.
  - intros Model i f vars holes Lower E rho.
    apply Model. eapply source_nonlogical_is_conventional; eassumption.
  - intros Model p Ax rho.
    apply (augmented_sound_in_inhabited_model R EM Model p).
    now apply conventional_axiom_to_augmented.
Qed.

Theorem conventional_model_iff_zf_uniform_berkeley (seed:D) :
  ConventionalModel R <-> satisfies_zf_prefix R /\ RelUniformBerkeley R.
Proof.
  rewrite conventional_model_iff_source.
  apply (candidate_model_iff_zf_uniform_berkeley R EM seed).
Qed.
End Models.

Print Assumptions conventional_model_iff_source.
Print Assumptions conventional_model_iff_zf_uniform_berkeley.
