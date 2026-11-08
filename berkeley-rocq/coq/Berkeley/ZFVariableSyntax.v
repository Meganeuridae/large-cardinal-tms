(** Syntactic variable changes inside arbitrary formula contexts. These
    lemmas do not assume completeness or semantic-to-syntactic conversion. *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
From Berkeley Require Import Syntax ProofFormula TheoryIrreflexiveND LogicBridge LogicFresh
  AugmentedLogic AugmentedInstantiation AugmentedCapture StandardND StandardLogical StandardAugEquivalence ZFProtected.
Import ListNotations.
Theorem standard_theorem_substitution x y p : safe_subst x y p=true ->
  StandardND [] p -> StandardND [] (nd_subst x y p).
Proof.
  intros Safe H. eapply std_all_elim; [exact Safe|].
  apply std_all_intro; [unfold nd_fresh;intros q []|exact H].
Qed.
Lemma aug_all_alpha_forward x y p : nd_not_bound y p=true -> nd_free y p=false ->
  AugProvable (FImp (FAll x p) (FAll y (nd_subst x y p))).
Proof.
  intros Bound Free. destruct (Nat.eq_dec x y) as [E|E].
  - subst y. rewrite nd_subst_self. apply aug_logical,logical_identity.
  - apply aug_fresh_generalization.
    + apply nd_free_not_occurs. cbn [nd_free]. apply Nat.eqb_neq in E.
      rewrite Nat.eqb_sym,E. exact Free.
    + apply aug_all_instantiate_safe,nd_not_bound_implies_safe,Bound.
Qed.
Theorem aug_alpha_in_arbitrary_context f x y p : nd_not_bound y p=true -> nd_free y p=false ->
  AugEquiv (fill_template f (FAll x p)) (fill_template f (FAll y (nd_subst x y p))).
Proof.
  intros Bound Free. apply aug_instance_congruence. intro n. split.
  - now apply aug_all_alpha_forward.
  - now apply aug_all_alpha_reverse.
Qed.
Theorem standard_alpha_in_arbitrary_context f x y p : nd_not_bound y p=true -> nd_free y p=false ->
  StandardND [] (FImp (fill_template f (FAll x p)) (fill_template f (FAll y (nd_subst x y p)))) /\
  StandardND [] (FImp (fill_template f (FAll y (nd_subst x y p)) ) (fill_template f (FAll x p))).
Proof.
  intros Bound Free. destruct (aug_alpha_in_arbitrary_context f x y p Bound Free) as [H K].
  split; now apply augmented_theorem_to_standard.
Qed.
Theorem standard_rename_bound_in_context f x y p : nd_not_bound y p=true -> nd_free y p=false ->
  StandardND [] (fill_template f (FAll x p)) ->
  StandardND [] (fill_template f (FAll y (nd_subst x y p))).
Proof.
  intros Bound Free H. eapply std_imp_elim.
  - apply (proj1 (standard_alpha_in_arbitrary_context f x y p Bound Free)).
  - exact H.
Qed.
Print Assumptions standard_theorem_substitution.
Print Assumptions aug_all_alpha_forward.
Print Assumptions standard_alpha_in_arbitrary_context.
Print Assumptions standard_rename_bound_in_context.
