(** Classical model-theoretic consequences of the actual Pairing and
    Foundation source axioms, independently of syntactic completeness. *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
From Berkeley Require Import ProofFormula ProofSearchSyntax ProofPresentation FormulaSemantics LogicSemantics TheoryIrreflexiveND.
Import ListNotations.
Section ClassicalStructures.
Context {D:Type} (R:D->D->Prop).
Variable classic : forall P:Prop, P \/ ~P.
Lemma classical_notall_not_exists (p:D->Prop) : ~(forall x, ~p x) -> exists x, p x.
Proof.
  intro H. destruct (classic (exists x, p x)) as [E|E]; [exact E|].
  exfalso. apply H. intros x P. apply E. now exists x.
Qed.
Lemma classical_encoded_and p q : ~ (p -> ~q) -> p /\ q.
Proof.
  intro H. destruct (classic p) as [P|P]; [|exfalso;apply H; tauto].
  destruct (classic q) as [Q|Q]; [now split|exfalso;apply H;tauto].
Qed.
Theorem pair_foundation_membership_irreflexive :
  (forall rho, FolHolds R rho pair_axiom) ->
  (forall rho, FolHolds R rho foundation_axiom) ->
  forall a, ~ R a a.
Proof.
  intros Pair Foundation a Self.
  pose proof (Pair (fun _=>a)) as P.
  cbn [pair_axiom nd_ex nd_iff nd_and nd_or FolHolds update_variable] in P.
  cbv [update_variable Nat.eqb] in P.
  apply classical_notall_not_exists in P as [b P].
  assert (P0 : R a b).
  { destruct (classical_encoded_and _ _ (P a)) as [_ Back]. apply Back. intros _. reflexivity. }
  assert (P1 : forall d, R d b -> d=a).
  { intros d Hd. destruct (classical_encoded_and _ _ (P d)) as [Forward _].
    destruct (classic (d=a)) as [E|E]; [exact E|]. exact (Forward Hd E). }
  pose proof (Foundation (fun _=>b)) as F.
  cbn [foundation_axiom foundation_body nd_ex nd_and FolHolds update_variable] in F.
  cbv [update_variable Nat.eqb] in F. specialize (F b).
  assert (Nonempty : ~(forall d, ~R d b)) by (intro N; apply (N a); exact P0).
  specialize (F Nonempty). apply classical_notall_not_exists in F as [d F].
  destruct (classical_encoded_and _ _ F) as [Db Minimal].
  specialize (P1 d Db). subst d. apply (Minimal a Self). exact P0.
Qed.
Theorem nonlogical_model_membership_irreflexive : satisfies_nonlogical_schemas R ->
  forall a, ~ R a a.
Proof.
  intro Model. apply pair_foundation_membership_irreflexive.
  - intros rho. eapply presented_sound; [exact classic|exact Model|apply pair_axiom_presented].
  - intros rho. eapply presented_sound; [exact classic|exact Model|apply foundation_axiom_presented].
Qed.
Theorem inhabited_nonlogical_model_numeric_consistent : satisfies_nonlogical_schemas R ->
  (exists a : D, True) -> ~NumericInconsistent.
Proof.
  intros Model [a _]. eapply (nonlogical_model_irreflexive_consistency R classic Model (fun _=>a)).
  now apply (nonlogical_model_membership_irreflexive Model).
Qed.
End ClassicalStructures.
Print Assumptions pair_foundation_membership_irreflexive.
Print Assumptions nonlogical_model_membership_irreflexive.
Print Assumptions inhabited_nonlogical_model_numeric_consistent.
