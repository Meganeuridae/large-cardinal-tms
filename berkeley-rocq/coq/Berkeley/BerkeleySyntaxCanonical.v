(** Canonical internal all-code satisfaction and elementarity. The existential
    truth set in the literal sentence exists by first-order ZF and is unique
    on all internal formula/environment pairs. No converse from merely external
    finite-formula elementarity is asserted. *)
From Stdlib Require Import Lists.List.
From Berkeley Require Import Syntax SyntaxData ProofFormula ProofPresentation FormulaSemantics BerkeleySyntaxPairs BerkeleySyntaxSets
  BerkeleySyntaxFormulaSet BerkeleySyntaxEnvironment BerkeleySyntaxElementary BerkeleySyntaxSatisfactionSemantics BerkeleySyntaxWitnesses
  BerkeleySyntaxLocal BerkeleySyntaxCardinalWitness BerkeleySyntaxSentence BerkeleySyntaxZFBase BerkeleySyntaxZFEnvironments
  BerkeleySyntaxSatisfactionUnique BerkeleySyntaxSatisfactionExists.
Import ListNotations.

Definition RelCanonicalElementary {D} (R:D->D->Prop) j m f w te tm tn ti ta :=
  forall e sat, RelEnvironments R e w m -> RelSatisfaction R sat e f w m te tm tn ti ta ->
    RelElementary R j m e f w sat.
Definition RelCanonicalBerkeley {D} (R:D->D->Prop) :=
  exists w te tm tn ti ta f, RelSentenceSetup R w te tm tn ti ta f /\ exists d,
    BerkeleySyntaxCardinal.RelCardinal R d /\ R w d /\
    forall m, RelTransitive R m -> R d m -> forall eta, R eta d -> exists j k,
      RelCritical R j k d eta /\ RelCanonicalElementary R j m f w te tm tn ti ta.

Lemma relational_environments_unique {D} (R:D->D->Prop) w m e e' :
  BerkeleySyntaxRepresentations.RelExtensional R -> RelEnvironments R e w m -> RelEnvironments R e' w m -> e=e'.
Proof. intros Ext A B. apply Ext. intro s. rewrite (A s),(B s). reflexivity. Qed.

Section Canonical.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Lemma satisfaction_elementarity_independent f w m e te tm tn ti ta sat1 sat2 j :
  RelFormulas R f w te tm tn ti ta -> RelEnvironments R e w m ->
  RelSatisfaction R sat1 e f w m te tm tn ti ta -> RelSatisfaction R sat2 e f w m te tm tn ti ta ->
  (RelElementary R j m e f w sat1 <-> RelElementary R j m e f w sat2).
Proof.
  intros Formulas Env T1 T2. pose proof (zf_internal_satisfaction_unique R EM Model f w m e te tm tn ti ta sat1 sat2
    Formulas Env T1 T2) as Unique. unfold RelElementary,RelElementaryClause. split; intros [Func Elem]; split; [exact Func| |exact Func|].
  - intros p s t P S T Image. specialize (Elem p s t P S T Image).
    pose proof (Unique p s P S) as L. pose proof (Unique p t P T) as H. tauto.
  - intros p s t P S T Image. specialize (Elem p s t P S T Image).
    pose proof (Unique p s P S) as L. pose proof (Unique p t P T) as H. tauto.
Qed.

Theorem literal_iff_canonical_internal_berkeley : RelBerkeleySentence R <-> RelCanonicalBerkeley R.
Proof.
  split.
  - intros Sentence. destruct Sentence as [w [te [tm [tn [ti [ta [f Body]]]]]]].
    destruct Body as [Setup [d [Card [Large Scope]]]].
    pose proof Setup as [Tags Formulas]. exists w,te,tm,tn,ti,ta,f. split; [exact Setup|].
    exists d. split; [exact Card|]. split; [exact Large|]. intros m Trans Contains eta Eta.
    destruct (Scope m Trans Contains) as [e [sat [Env [Truth Witness]]]].
    destruct (Witness eta Eta) as [j [k [Critical Elementary]]]. exists j,k. split; [exact Critical|].
    intros e' sat' Env' Truth'.
    assert (e=e') by (eapply relational_environments_unique; [apply (zf_prefix_extensional R EM Model)|exact Env|exact Env']).
    subst e'. apply (proj1 (satisfaction_elementarity_independent f w m e te tm tn ti ta sat sat' j Formulas Env Truth Truth')). exact Elementary.
  - intros Sentence. destruct Sentence as [w [te [tm [tn [ti [ta [f Body]]]]]]].
    destruct Body as [Setup [d [Card [Large Property]]]].
    pose proof Setup as [Tags Formulas]. exists w,te,tm,tn,ti,ta,f. split; [exact Setup|].
    exists d. split; [exact Card|]. split; [exact Large|]. intros m Trans Contains.
    destruct (zf_prefix_environments_exist R EM Model w m) as [e Env].
    destruct (zf_prefix_satisfaction_exists R EM Model f e w m te tm tn ti ta Tags Formulas Env) as [sat Truth].
    exists e,sat. split; [exact Env|]. split; [exact Truth|]. intros eta Eta.
    destruct (Property m Trans Contains eta Eta) as [j [k [Critical Canonical]]].
    exists j,k. split; [exact Critical|]. now apply (Canonical e sat).
Qed.

Corollary candidate_berkeley_iff_canonical_internal rho vars holes :
  FolHolds R rho (independent_instance vars holes (nth 23 candidate_axioms (Hole 0))) <-> RelCanonicalBerkeley R.
Proof. rewrite (candidate_berkeley_relational_semantics EM). apply literal_iff_canonical_internal_berkeley. Qed.
Corollary original_berkeley_iff_canonical_internal rho vars holes :
  FolHolds R rho (independent_instance vars holes (nth 23 original_axioms (Hole 0))) <-> RelCanonicalBerkeley R.
Proof. rewrite (original_berkeley_relational_semantics EM). apply literal_iff_canonical_internal_berkeley. Qed.
End Canonical.

Print Assumptions satisfaction_elementarity_independent.
Print Assumptions literal_iff_canonical_internal_berkeley.
Print Assumptions candidate_berkeley_iff_canonical_internal.
Print Assumptions original_berkeley_iff_canonical_internal.
