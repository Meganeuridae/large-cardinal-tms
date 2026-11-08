(** The total-functional textbook antecedent is stronger than bounded partial
    uniqueness. The intended reading of the substituted instance additionally
    requires the explicitly stated capture-safety check. *)
From Stdlib Require Import Lists.List.
From Berkeley Require Import ProofFormula TheoryIrreflexiveND AugmentedInstantiation AugmentedCapture AugmentedLogic
  StandardND StandardLogical StandardAugSound StandardAugEquivalence ZFConventionalND ZFBoundedReplacementCore ZFBoundedReplacement.
Import ListNotations.

Definition replacement_total_bounded_unique p := FAll 3 (FImp replacement_domain
  (nd_ex 1 (nd_and (nd_subst 2 1 p) (replacement_unique_body p)))).
Definition bounded_total_replacement p := FImp (replacement_total_bounded_unique p) (replacement_image p).

Lemma bounded_total_implies_bounded_partial p : StandardND []
  (FImp (replacement_total_bounded_unique p) (replacement_bounded_unique p)).
Proof.
  apply std_imp_intro. unfold replacement_bounded_unique. apply std_all_intro.
  - unfold nd_fresh. intros t [E|[]]. subst t. cbn [replacement_total_bounded_unique nd_free]. reflexivity.
  - apply std_imp_intro. set (A := replacement_total_bounded_unique p). set (M := replacement_domain).
    change (StandardND [M;A] (nd_ex 1 (replacement_unique_body p))).
    assert (Has : StandardND [M;A] (nd_ex 1 (nd_and (nd_subst 2 1 p) (replacement_unique_body p)))).
    { eapply std_imp_elim.
      - eapply (std_all_same _ 3 (FImp M (nd_ex 1 (nd_and (nd_subst 2 1 p) (replacement_unique_body p))))).
        apply std_hyp. cbn. auto.
      - apply std_hyp. now left. }
    eapply (std_ex_elim [M;A] 1 1 (nd_and (nd_subst 2 1 p) (replacement_unique_body p))
      (nd_ex 1 (replacement_unique_body p))).
    + apply safe_subst_self.
    + now left.
    + unfold nd_fresh. intros t [E|[E|[]]]; subst t; unfold M,A,replacement_domain,replacement_total_bounded_unique,nd_ex;
        cbn [nd_free]; reflexivity.
    + unfold nd_ex. cbn [nd_free]. reflexivity.
    + exact Has.
    + rewrite nd_subst_self. eapply (std_ex_intro _ 1 1); [apply safe_subst_self|]. rewrite nd_subst_self.
      eapply std_and_right. apply std_hyp. now left.
Qed.

Theorem bounded_total_replacement_derivable p : nd_free 1 p=false -> AugProvable (bounded_total_replacement p).
Proof.
  intro Fresh. unfold bounded_total_replacement. eapply aug_syllogism.
  - apply standard_theorem_to_augmented,bounded_total_implies_bounded_partial.
  - apply bounded_replacement_derivable,Fresh.
Qed.
Corollary textbook_total_replacement_derivable p : nd_free 1 p=false -> safe_subst 2 1 p=true ->
  AugProvable (bounded_total_replacement p).
Proof. intros Fresh _. now apply bounded_total_replacement_derivable. Qed.

Corollary bounded_replacement_conventional_nd p : nd_free 1 p=false -> ConventionalND [] (bounded_replacement p).
Proof. intro Fresh. apply standard_to_conventional,augmented_theorem_to_standard,bounded_replacement_derivable,Fresh. Qed.
Corollary bounded_total_replacement_conventional_nd p : nd_free 1 p=false -> safe_subst 2 1 p=true ->
  ConventionalND [] (bounded_total_replacement p).
Proof. intros Fresh Safe. apply standard_to_conventional,augmented_theorem_to_standard; now apply textbook_total_replacement_derivable. Qed.

Print Assumptions bounded_total_implies_bounded_partial.
Print Assumptions bounded_total_replacement_derivable.
Print Assumptions bounded_replacement_conventional_nd.
Print Assumptions bounded_total_replacement_conventional_nd.
