(** The guarded-D augmentation is sound for the exact nonlogical source
    schemas: Empty and Pairing force every inhabited model to have two
    distinct elements. This does not identify the augmented calculus with
    the original machine's proof system. *)
From Stdlib Require Import Lists.List.
From Berkeley Require Import Syntax SyntaxData ProofFormula ProofPresentation FormulaSemantics LogicSemantics
  TheoryIrreflexiveND TheoryFoundationSemantics AugmentedLogic.
Import ListNotations.
Definition empty_axiom := nd_ex 0 (FAll 1 (FNeg (FMember 1 0))).
Lemma empty_axiom_presented : PresentedProvable empty_axiom.
Proof.
  change (PresentedProvable (independent_instance (fun n=>n) (fun _=>FEqual 0 0)
    (nth 15 candidate_axioms (Hole 0)))).
  eapply presented_axiom with (i:=15). reflexivity.
Qed.
Section ClassicalStructures.
Context {D:Type} (R:D->D->Prop).
Variable classic : forall P:Prop, P \/ ~P.
Hypothesis Model : satisfies_nonlogical_schemas R.
Theorem inhabited_nonlogical_model_nontrivial : (exists a:D, True) -> exists a b:D, a<>b.
Proof.
  intros [a _].
  pose proof (presented_sound R classic Model empty_axiom empty_axiom_presented (fun _=>a)) as Empty.
  cbn [empty_axiom nd_ex FolHolds update_variable] in Empty.
  cbv [update_variable Nat.eqb] in Empty.
  apply (classical_notall_not_exists classic) in Empty as [e Empty].
  pose proof (presented_sound R classic Model pair_axiom pair_axiom_presented (fun _=>e)) as Pair.
  cbn [pair_axiom nd_ex nd_iff nd_and nd_or FolHolds update_variable] in Pair.
  cbv [update_variable Nat.eqb] in Pair.
  apply (classical_notall_not_exists classic) in Pair as [b Pair].
  destruct (classical_encoded_and classic _ _ (Pair e)) as [_ Back].
  assert (InPair : R e b) by (apply Back; intros _; reflexivity).
  exists e,b. intro Eq. subst b. now apply (Empty e).
Qed.
Theorem augmented_sound_in_inhabited_model f : AugProvable f -> forall rho, FolHolds R rho f.
Proof.
  intros H rho. eapply augmented_sound; [exact classic|exact Model| |exact H].
  apply inhabited_nonlogical_model_nontrivial. exists (rho 0). exact I.
Qed.
Theorem augmented_model_consistency : (exists a:D, True) ->
  ~(exists p, AugProvable p /\ AugProvable (FNeg p)).
Proof.
  intros [a _] [p [P N]].
  pose proof (augmented_sound_in_inhabited_model _ P (fun _=>a)) as A.
  pose proof (augmented_sound_in_inhabited_model _ N (fun _=>a)) as B.
  cbn [FolHolds] in B. contradiction.
Qed.
End ClassicalStructures.
Print Assumptions empty_axiom_presented.
Print Assumptions inhabited_nonlogical_model_nontrivial.
Print Assumptions augmented_sound_in_inhabited_model.
Print Assumptions augmented_model_consistency.
