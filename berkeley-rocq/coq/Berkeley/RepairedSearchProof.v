(** Abstract proof-search correctness for the experimental guarded-D repair.
    A separate literal-machine compilation theorem is still required. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import Syntax SyntaxData ConstructorStreams ProofSearchSyntax ProofFormula
  ProofPresentation LogicFresh AugmentedLogic AugmentedContradiction GenericSearch.
Import ListNotations.
Definition code_distinctor x y := code_neg (code_all x (code_eq x y)).
Definition repaired_axiom i a b c :=
  if Nat.eqb i 24 then
    if Nat.eqb a b then None else Some (code_distinctor a b)
  else instantiated_axiom i a b c.
Lemma old_axiom_24_absent a b c : instantiated_axiom 24 a b c=None.
Proof. unfold instantiated_axiom. change (nth_error candidate_axioms 24) with (@None formula). reflexivity. Qed.
Lemma original_axiom_survives i a b c n : instantiated_axiom i a b c=Some n ->
  repaired_axiom i a b c=Some n.
Proof.
  intro H. unfold repaired_axiom. destruct (Nat.eqb i 24) eqn:E; [|exact H].
  apply Nat.eqb_eq in E. subst. rewrite old_axiom_24_absent in H. discriminate.
Qed.
Lemma original_numeric_embeds n : NumericProvable n -> Derivable repaired_axiom n.
Proof.
  intro H. induction H as [|i a b c f E|p q M IHm P IHp|x p P IH].
  - constructor.
  - exact (derive_axiom repaired_axiom i a b c f (original_axiom_survives i a b c f E)).
  - eapply derive_mp; eassumption.
  - now apply derive_gen.
Qed.
Theorem repaired_numeric_decodes n : Derivable repaired_axiom n -> AugProvable (decode_formula n).
Proof.
  intro H. induction H as [|i a b c n E|p q Major IHm Minor IHp|x p P IH].
  - change (AugProvable (FEqual 0 0)). apply aug_original,presented_reflexivity.
  - unfold repaired_axiom in E. destruct (Nat.eqb i 24) eqn:I.
    + destruct (Nat.eqb a b) eqn:AB; [discriminate|]. inversion E; subst n.
      unfold code_distinctor. rewrite decode_neg,decode_all,decode_equal.
      apply aug_distinctor,Nat.eqb_neq,AB.
    + apply aug_original,numeric_proof_decodes. eapply numeric_axiom; exact E.
  - rewrite decode_imp in IHm. eapply aug_mp; eassumption.
  - rewrite decode_all. now apply aug_gen.
Qed.
Theorem augmented_proof_encodes f : AugProvable f -> Derivable repaired_axiom (encode_formula f).
Proof.
  intro H. induction H as [p P|x y XY|p q Major IHm Minor IHp|x p P IH].
  - apply original_numeric_embeds,presented_proof_encodes,P.
  - cbn [distinctor encode_formula]. eapply derive_axiom with (i:=24) (a:=x) (b:=y) (c:=0).
    unfold repaired_axiom. rewrite Nat.eqb_refl. apply Nat.eqb_neq in XY. rewrite XY. reflexivity.
  - cbn [encode_formula] in IHm. eapply derive_mp; eassumption.
  - cbn [encode_formula]. now apply derive_gen.
Qed.
Theorem repaired_numeric_iff_augmented_target :
  Derivable repaired_axiom 1 <-> AugProvable (FMember 0 0).
Proof.
  split; intro H; [exact (repaired_numeric_decodes 1 H)|exact (augmented_proof_encodes _ H)].
Qed.
Theorem repaired_abstract_search_iff_augmented_inconsistency :
  SearchHalts repaired_axiom <-> exists p,AugProvable p /\ AugProvable (FNeg p).
Proof.
  rewrite abstract_search_halting_iff_numeric_inconsistent.
  unfold GenericInconsistent. rewrite repaired_numeric_iff_augmented_target.
  apply augmented_target_iff_internal_inconsistency.
Qed.
Print Assumptions original_numeric_embeds.
Print Assumptions repaired_numeric_decodes.
Print Assumptions augmented_proof_encodes.
Print Assumptions repaired_abstract_search_iff_augmented_inconsistency.
