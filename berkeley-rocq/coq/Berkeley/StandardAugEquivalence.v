(** Equivalence between the guarded-D augmentation and an independent
    first-order natural deduction presentation over the exact nonlogical
    source axiom instances. This is not a theorem about the original machine. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Arith.Compare_dec Lia.
From Berkeley Require Import Syntax SyntaxData TheorySchemas ProofFormula ProofPresentation LogicFresh
  TheoryIrreflexiveND AugmentedLogic StandardND StandardLogical StandardDistinctor StandardAugSound.
Import ListNotations.
Lemma logical_schema_standard i f vars holes : nth_error logical_schemas i=Some f ->
  StandardND [] (independent_instance vars holes f).
Proof.
  intro E. do 14 (destruct i as [|i];
    [cbn [logical_schemas] in E; inversion E; subst f;
     cbn [independent_instance independent_variable];
     first [apply std_b1 | apply std_b2 | apply std_b3 | apply std_b4 | apply std_b5 |
       apply std_b6 | apply std_b7 | apply std_b8 | apply std_b9 | apply std_b10 |
       apply std_b11 | apply std_b12 | apply std_b13 | apply std_b14] |]).
  destruct i; discriminate.
Qed.
Theorem presented_theorem_to_standard p : PresentedProvable p -> StandardND [] p.
Proof.
  intro H. induction H as [|i f vars holes E|p q A IHA B IHB|x p A IH].
  - apply std_eq_refl.
  - destruct (lt_dec i 14) as [Small|Large].
    + eapply logical_schema_standard. rewrite <- candidate_logical_prefix,nth_error_firstn_lt by exact Small. exact E.
    + eapply (std_nonlogical [] i f vars holes); [lia|exact E].
  - eapply std_imp_elim; eassumption.
  - apply std_all_intro; [unfold nd_fresh;intros h []|exact IH].
Qed.
Theorem augmented_theorem_to_standard p : AugProvable p -> StandardND [] p.
Proof.
  intro H. induction H as [p P|x y Different|p q A IHA B IHB|x p A IH].
  - now apply presented_theorem_to_standard.
  - now apply std_distinctor.
  - eapply std_imp_elim; eassumption.
  - apply std_all_intro; [unfold nd_fresh;intros h []|exact IH].
Qed.
Theorem augmented_iff_standard_theorem p : AugProvable p <-> StandardND [] p.
Proof. split; [apply augmented_theorem_to_standard|apply standard_theorem_to_augmented]. Qed.
Print Assumptions logical_schema_standard.
Print Assumptions presented_theorem_to_standard.
Print Assumptions augmented_theorem_to_standard.
Print Assumptions augmented_iff_standard_theorem.
