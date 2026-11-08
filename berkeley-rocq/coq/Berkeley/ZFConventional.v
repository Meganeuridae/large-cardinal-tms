(** An independently written, fixed-variable normal form for conventional ZF
    plus the exact literal Berkeley sentence. Separation and Replacement use
    an arbitrary formula parameter whose output variable 1 is not free. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Arith.Compare_dec Lia.
From Berkeley Require Import Syntax SyntaxData TheorySchemas ProofFormula ProofPresentation LogicFresh
  TheoryIrreflexiveND AugmentedLogic StandardND StandardAugEquivalence ZFProtected.
Import ListNotations.
Inductive ConventionalAxiom : fol_formula -> Prop :=
| conv_fixed i f vars holes : i<>6 -> i<>7 -> nth_error zf_schemas i=Some f ->
    ConventionalAxiom (independent_instance vars holes f)
| conv_separation p : nd_free 1 p=false -> ConventionalAxiom (conventional_separation p)
| conv_replacement p : nd_free 1 p=false -> ConventionalAxiom (conventional_replacement p)
| conv_berkeley f vars holes : nth_error candidate_axioms 23=Some f ->
    ConventionalAxiom (independent_instance vars holes f).
Lemma zf_schema_length : length zf_schemas=9. Proof. reflexivity. Qed.
Lemma candidate_axiom_length : length candidate_axioms=24. Proof. reflexivity. Qed.
Lemma zf_schema_candidate_index i f : nth_error zf_schemas i=Some f ->
  nth_error candidate_axioms (14+i)=Some f.
Proof.
  intro E. assert (B:i<9).
  { rewrite <- zf_schema_length. apply nth_error_Some. rewrite E. discriminate. }
  rewrite <- (nth_error_firstn_lt candidate_axioms (14+i) 23) by lia.
  rewrite candidate_standard_prefix, nth_error_app2.
  - change (nth_error zf_schemas (14+i-14)=Some f). replace (14+i-14) with i by lia. exact E.
  - change (14<=14+i). lia.
Qed.
Theorem conventional_axiom_to_augmented p : ConventionalAxiom p -> AugProvable p.
Proof.
  intro H. destruct H as [i f vars holes A B E|p F|p F|f vars holes E].
  - apply aug_original. eapply (presented_axiom (14+i) f vars holes). now apply zf_schema_candidate_index.
  - now apply conventional_separation_derivable.
  - now apply conventional_replacement_derivable.
  - apply aug_original. eapply (presented_axiom 23 f vars holes); exact E.
Qed.
Lemma candidate_nonlogical_zf i f : 14<=i -> i<23 -> nth_error candidate_axioms i=Some f ->
  nth_error zf_schemas (i-14)=Some f.
Proof.
  intros Lower Upper E.
  rewrite <- (nth_error_firstn_lt candidate_axioms i 23 Upper),candidate_standard_prefix in E.
  rewrite nth_error_app2 in E; [|change (14<=i); exact Lower].
  change (nth_error zf_schemas (i-14)=Some f) in E. exact E.
Qed.
Theorem source_nonlogical_is_conventional i f vars holes : 14<=i -> nth_error candidate_axioms i=Some f ->
  ConventionalAxiom (independent_instance vars holes f).
Proof.
  intros Lower E. assert (Upper:i<24).
  { rewrite <- candidate_axiom_length. apply nth_error_Some. rewrite E. discriminate. }
  destruct (Nat.eq_dec i 20) as [S|S].
  - subst i. cbn [candidate_axioms] in E. inversion E; subst f.
    change (ConventionalAxiom (conventional_separation (FAll 1 (holes 1)))).
    apply conv_separation. cbn [nd_free]. now rewrite Nat.eqb_refl.
  - destruct (Nat.eq_dec i 21) as [R|R].
    + subst i. cbn [candidate_axioms] in E. inversion E; subst f.
      change (ConventionalAxiom (conventional_replacement (FAll 1 (holes 1)))).
      apply conv_replacement. cbn [nd_free]. now rewrite Nat.eqb_refl.
    + destruct (Nat.eq_dec i 23) as [Ber|Ber].
      * subst i. now apply conv_berkeley.
      * eapply (conv_fixed (i-14)); [lia|lia|]. eapply candidate_nonlogical_zf; [exact Lower|lia|exact E].
Qed.
Theorem conventional_axiom_to_standard p : ConventionalAxiom p -> StandardND [] p.
Proof. intro H. apply augmented_theorem_to_standard,conventional_axiom_to_augmented,H. Qed.
Print Assumptions zf_schema_candidate_index.
Print Assumptions conventional_axiom_to_augmented.
Print Assumptions source_nonlogical_is_conventional.
Print Assumptions conventional_axiom_to_standard.
