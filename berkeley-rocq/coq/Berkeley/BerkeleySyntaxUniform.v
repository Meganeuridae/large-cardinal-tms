(** A choice-independent internal-Berkeley formulation: elementarity ranges
    over any internally canonical coding and truth set. The equivalence below
    assumes only that a formula-coding setup exists; construction of that setup
    is a separate ZF theorem. *)
From Stdlib Require Import Lists.List.
From Berkeley Require Import Syntax SyntaxData ProofFormula ProofPresentation FormulaSemantics BerkeleySyntaxSets BerkeleySyntaxOmega BerkeleySyntaxCardinal BerkeleySyntaxSentence BerkeleySyntaxWitnesses
  BerkeleySyntaxEnvironment BerkeleySyntaxElementary BerkeleySyntaxSatisfactionSemantics BerkeleySyntaxRepresentations
  BerkeleySyntaxCanonicalData BerkeleySyntaxCanonical BerkeleySyntaxZFBase.
Import ListNotations.

Definition RelUniformElementary {D} (R:D->D->Prop) j m :=
  forall w te tm tn ti ta f e sat, RelSentenceSetup R w te tm tn ti ta f -> RelEnvironments R e w m ->
    RelSatisfaction R sat e f w m te tm tn ti ta -> RelElementary R j m e f w sat.
Definition RelUniformBerkeley {D} (R:D->D->Prop) :=
  exists w d, RelOmega R w /\ RelCardinal R d /\ R w d /\
    forall m, RelTransitive R m -> R d m -> forall eta, R eta d -> exists j k,
      RelCritical R j k d eta /\ RelUniformElementary R j m.
Definition RelFormulaSetupExists {D} (R:D->D->Prop) :=
  exists w te tm tn ti ta f, RelSentenceSetup R w te tm tn ti ta f.

Lemma relational_setup_unique {D} (R:D->D->Prop) w a0 a1 a2 a3 a4 f w' b0 b1 b2 b3 b4 f' :
  RelExtensional R -> RelSentenceSetup R w a0 a1 a2 a3 a4 f -> RelSentenceSetup R w' b0 b1 b2 b3 b4 f' ->
  w=w' /\ a0=b0 /\ a1=b1 /\ a2=b2 /\ a3=b3 /\ a4=b4 /\ f=f'.
Proof.
  intros Ext [Tags Formulas] [Tags' Formulas'].
  destruct (relational_tag_chains_unique R w a0 a1 a2 a3 a4 w' b0 b1 b2 b3 b4 Ext Tags Tags') as [W [E0 [E1 [E2 [E3 E4]]]]].
  subst w' b0 b1 b2 b3 b4. assert (f=f') by (eapply relational_formula_set_unique; eassumption). tauto.
Qed.

Section Uniform.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Lemma canonical_elementarity_is_uniform j m w te tm tn ti ta f :
  RelSentenceSetup R w te tm tn ti ta f -> RelCanonicalElementary R j m f w te tm tn ti ta -> RelUniformElementary R j m.
Proof.
  intros Setup Canon w' te' tm' tn' ti' ta' f' e sat Setup' Env Truth.
  destruct (relational_setup_unique R w te tm tn ti ta f w' te' tm' tn' ti' ta' f'
    (zf_prefix_extensional R EM Model) Setup Setup') as [W [E0 [E1 [E2 [E3 [E4 F]]]]]].
  subst w' te' tm' tn' ti' ta' f'. now apply (Canon e sat).
Qed.

Theorem canonical_iff_uniform_internal_berkeley : RelFormulaSetupExists R ->
  (RelCanonicalBerkeley R <-> RelUniformBerkeley R).
Proof.
  intros SetupExists. split.
  - intros Sentence. destruct Sentence as [w [te [tm [tn [ti [ta [f Body]]]]]]].
    destruct Body as [Setup [d [Card [Large Prop0]]]].
    exists w,d. split; [exact (proj1 (proj1 Setup))|]. split; [exact Card|]. split; [exact Large|].
    intros m Trans Contains eta Eta. destruct (Prop0 m Trans Contains eta Eta) as [j [k [Critical Canon]]].
    exists j,k. split; [exact Critical|]. eapply canonical_elementarity_is_uniform; eassumption.
  - intros [w [d [Omega [Card [Large Prop0]]]]].
    destruct SetupExists as [w' [te [tm [tn [ti [ta [f Setup]]]]]]].
    assert (w=w') by (eapply relational_omega_unique; [apply (zf_prefix_extensional R EM Model)|exact Omega|exact (proj1 (proj1 Setup))]).
    subst w'. exists w,te,tm,tn,ti,ta,f. split; [exact Setup|]. exists d. split; [exact Card|]. split; [exact Large|].
    intros m Trans Contains eta Eta. destruct (Prop0 m Trans Contains eta Eta) as [j [k [Critical Uniform]]].
    exists j,k. split; [exact Critical|]. intros e sat Env Truth. exact (Uniform w te tm tn ti ta f e sat Setup Env Truth).
Qed.

Corollary candidate_axiom_iff_uniform_internal rho vars holes : RelFormulaSetupExists R ->
  (FolHolds R rho (independent_instance vars holes (nth 23 candidate_axioms (Hole 0))) <-> RelUniformBerkeley R).
Proof.
  intro SetupExists. rewrite (candidate_berkeley_iff_canonical_internal R EM Model).
  now apply canonical_iff_uniform_internal_berkeley.
Qed.
Corollary original_axiom_iff_uniform_internal rho vars holes : RelFormulaSetupExists R ->
  (FolHolds R rho (independent_instance vars holes (nth 23 original_axioms (Hole 0))) <-> RelUniformBerkeley R).
Proof.
  intro SetupExists. rewrite (original_berkeley_iff_canonical_internal R EM Model).
  now apply canonical_iff_uniform_internal_berkeley.
Qed.
End Uniform.

Print Assumptions candidate_axiom_iff_uniform_internal.
Print Assumptions original_axiom_iff_uniform_internal.
Print Assumptions relational_setup_unique.
Print Assumptions canonical_elementarity_is_uniform.
Print Assumptions canonical_iff_uniform_internal_berkeley.
