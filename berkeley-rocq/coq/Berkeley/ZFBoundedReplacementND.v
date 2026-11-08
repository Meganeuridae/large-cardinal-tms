(** First-order ND with the bounded-domain partial-functional Replacement
    family in place of the global-domain family, and translations both ways. *)
From Stdlib Require Import Lists.List.
From Berkeley Require Import Syntax SyntaxData TheorySchemas ProofFormula ProofPresentation TheoryIrreflexiveND AugmentedInstantiation
  AugmentedCapture StandardLogical ZFProtected ZFConventional ZFConventionalND ZFBoundedReplacementCore ZFBoundedReplacement
  ZFBoundedReplacementTotal.
Import ListNotations.

Inductive BoundedReplacementAxiom : fol_formula -> Prop :=
| bra_fixed i f vars holes : i<>6 -> i<>7 -> nth_error zf_schemas i=Some f ->
    BoundedReplacementAxiom (independent_instance vars holes f)
| bra_separation p : nd_free 1 p=false -> BoundedReplacementAxiom (conventional_separation p)
| bra_replacement p : nd_free 1 p=false -> BoundedReplacementAxiom (bounded_replacement p)
| bra_berkeley f vars holes : nth_error candidate_axioms 23=Some f ->
    BoundedReplacementAxiom (independent_instance vars holes f).

Inductive BoundedReplacementND (ctx:list fol_formula) : fol_formula -> Prop :=
| bnd_hyp p : In p ctx -> BoundedReplacementND ctx p
| bnd_closed p : BoundedReplacementND [] p -> BoundedReplacementND ctx p
| bnd_axiom p : BoundedReplacementAxiom p -> BoundedReplacementND ctx p
| bnd_imp_intro p q : BoundedReplacementND (p::ctx) q -> BoundedReplacementND ctx (FImp p q)
| bnd_imp_elim p q : BoundedReplacementND ctx (FImp p q) -> BoundedReplacementND ctx p -> BoundedReplacementND ctx q
| bnd_neg_intro p : BoundedReplacementND (p::ctx) nd_false -> BoundedReplacementND ctx (FNeg p)
| bnd_classical p : BoundedReplacementND (FNeg p::ctx) nd_false -> BoundedReplacementND ctx p
| bnd_exfalso p q : BoundedReplacementND ctx p -> BoundedReplacementND ctx (FNeg p) -> BoundedReplacementND ctx q
| bnd_and_intro p q : BoundedReplacementND ctx p -> BoundedReplacementND ctx q -> BoundedReplacementND ctx (nd_and p q)
| bnd_and_left p q : BoundedReplacementND ctx (nd_and p q) -> BoundedReplacementND ctx p
| bnd_and_right p q : BoundedReplacementND ctx (nd_and p q) -> BoundedReplacementND ctx q
| bnd_or_left p q : BoundedReplacementND ctx p -> BoundedReplacementND ctx (nd_or p q)
| bnd_or_elim p q r : BoundedReplacementND ctx (nd_or p q) -> BoundedReplacementND (p::ctx) r -> BoundedReplacementND (q::ctx) r -> BoundedReplacementND ctx r
| bnd_all_intro x p : nd_fresh x ctx -> BoundedReplacementND ctx p -> BoundedReplacementND ctx (FAll x p)
| bnd_all_elim x y p : safe_subst x y p=true -> BoundedReplacementND ctx (FAll x p) -> BoundedReplacementND ctx (nd_subst x y p)
| bnd_all_alpha_reverse x y p : nd_not_bound y p=true -> nd_free y p=false ->
    BoundedReplacementND ctx (FAll y (nd_subst x y p)) -> BoundedReplacementND ctx (FAll x p)
| bnd_ex_intro x y p : safe_subst x y p=true -> BoundedReplacementND ctx (nd_subst x y p) -> BoundedReplacementND ctx (nd_ex x p)
| bnd_ex_elim x y p q : safe_subst x y p=true -> (x=y \/ nd_free y p=false) -> nd_fresh y ctx -> nd_free y q=false ->
    BoundedReplacementND ctx (nd_ex x p) -> BoundedReplacementND (nd_subst x y p::ctx) q -> BoundedReplacementND ctx q
| bnd_eq_refl x : BoundedReplacementND ctx (FEqual x x)
| bnd_eq_sym x y : BoundedReplacementND ctx (FEqual x y) -> BoundedReplacementND ctx (FEqual y x)
| bnd_eq_trans x y z : BoundedReplacementND ctx (FEqual x y) -> BoundedReplacementND ctx (FEqual y z) -> BoundedReplacementND ctx (FEqual x z)
| bnd_eq_substitute x y p : safe_subst x y p=true -> BoundedReplacementND ctx (FEqual x y) -> BoundedReplacementND ctx p -> BoundedReplacementND ctx (nd_subst x y p)
| bnd_mem_left x y z : BoundedReplacementND ctx (FEqual x y) -> BoundedReplacementND ctx (FMember x z) -> BoundedReplacementND ctx (FMember y z)
| bnd_mem_right x y z : BoundedReplacementND ctx (FEqual x y) -> BoundedReplacementND ctx (FMember z x) -> BoundedReplacementND ctx (FMember z y).

Lemma conventional_replacement_from_bounded p : nd_free 1 p=false -> BoundedReplacementND [] (conventional_replacement p).
Proof.
  intro Fresh. change (BoundedReplacementND [] (FImp (replacement_global_unique p) (replacement_image p))).
  apply bnd_imp_intro. eapply bnd_imp_elim with (p:=replacement_bounded_unique p).
  - change (BoundedReplacementND [replacement_global_unique p] (bounded_replacement p)).
    apply bnd_axiom,bra_replacement,Fresh.
  - unfold replacement_bounded_unique. apply bnd_all_intro.
    + unfold nd_fresh. intros t [E|[]]. subst t. cbn [replacement_global_unique nd_free]. reflexivity.
    + apply bnd_imp_intro. rewrite <- (nd_subst_self 3 (nd_ex 1 (replacement_unique_body p))).
      eapply bnd_all_elim; [apply safe_subst_self|]. apply bnd_hyp. cbn. auto.
Qed.

Lemma bounded_axiom_to_conventional p : BoundedReplacementAxiom p -> ConventionalND [] p.
Proof.
  intro H. destruct H as [i f vars holes A B E|p F|p F|f vars holes E].
  - apply cnd_axiom. eapply conv_fixed; eassumption.
  - apply cnd_axiom,conv_separation,F.
  - now apply bounded_replacement_conventional_nd.
  - apply cnd_axiom. eapply conv_berkeley; exact E.
Qed.
Lemma conventional_axiom_to_bounded p : ConventionalAxiom p -> BoundedReplacementND [] p.
Proof.
  intro H. destruct H as [i f vars holes A B E|p F|p F|f vars holes E].
  - apply bnd_axiom. eapply bra_fixed; eassumption.
  - apply bnd_axiom,bra_separation,F.
  - now apply conventional_replacement_from_bounded.
  - apply bnd_axiom. eapply bra_berkeley; exact E.
Qed.

Theorem bounded_to_conventional_nd ctx p : BoundedReplacementND ctx p -> ConventionalND ctx p.
Proof.
  intro H. induction H.
  - now apply cnd_hyp.
  - now apply cnd_closed.
  - apply cnd_closed,bounded_axiom_to_conventional,H.
  - now apply cnd_imp_intro.
  - eapply cnd_imp_elim; eassumption.
  - now apply cnd_neg_intro.
  - now apply cnd_classical.
  - eapply cnd_exfalso with (p:=p); eassumption.
  - now apply cnd_and_intro.
  - eapply cnd_and_left; eassumption.
  - eapply cnd_and_right; eassumption.
  - now apply cnd_or_left.
  - eapply cnd_or_elim; eassumption.
  - eapply cnd_all_intro; eassumption.
  - eapply cnd_all_elim; eassumption.
  - eapply cnd_all_alpha_reverse; eassumption.
  - eapply cnd_ex_intro; eassumption.
  - eapply cnd_ex_elim; eassumption.
  - apply cnd_eq_refl.
  - now apply cnd_eq_sym.
  - eapply cnd_eq_trans; eassumption.
  - eapply cnd_eq_substitute; eassumption.
  - eapply cnd_mem_left; eassumption.
  - eapply cnd_mem_right; eassumption.
Qed.
Theorem conventional_to_bounded_nd ctx p : ConventionalND ctx p -> BoundedReplacementND ctx p.
Proof.
  intro H. induction H.
  - now apply bnd_hyp.
  - now apply bnd_closed.
  - apply bnd_closed,conventional_axiom_to_bounded,H.
  - now apply bnd_imp_intro.
  - eapply bnd_imp_elim; eassumption.
  - now apply bnd_neg_intro.
  - now apply bnd_classical.
  - eapply bnd_exfalso with (p:=p); eassumption.
  - now apply bnd_and_intro.
  - eapply bnd_and_left; eassumption.
  - eapply bnd_and_right; eassumption.
  - now apply bnd_or_left.
  - eapply bnd_or_elim; eassumption.
  - eapply bnd_all_intro; eassumption.
  - eapply bnd_all_elim; eassumption.
  - eapply bnd_all_alpha_reverse; eassumption.
  - eapply bnd_ex_intro; eassumption.
  - eapply bnd_ex_elim; eassumption.
  - apply bnd_eq_refl.
  - now apply bnd_eq_sym.
  - eapply bnd_eq_trans; eassumption.
  - eapply bnd_eq_substitute; eassumption.
  - eapply bnd_mem_left; eassumption.
  - eapply bnd_mem_right; eassumption.
Qed.
Theorem conventional_iff_bounded_replacement_nd ctx p : ConventionalND ctx p <-> BoundedReplacementND ctx p.
Proof. split; [apply conventional_to_bounded_nd|apply bounded_to_conventional_nd]. Qed.

Print Assumptions conventional_replacement_from_bounded.
Print Assumptions bounded_to_conventional_nd.
Print Assumptions conventional_to_bounded_nd.
Print Assumptions conventional_iff_bounded_replacement_nd.
