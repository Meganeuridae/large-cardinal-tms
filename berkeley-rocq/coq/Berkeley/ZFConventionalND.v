(** First-order ND over the normalized conventional ZF schemas and the literal
    Berkeley formula, with the same explicit side conditions as StandardND. *)
From Stdlib Require Import Lists.List.
From Berkeley Require Import Syntax SyntaxData ProofFormula ProofPresentation TheoryIrreflexiveND AugmentedCapture
  AugmentedLogic StandardND StandardAugEquivalence ZFConventional.
Import ListNotations.
Inductive ConventionalND (ctx:list fol_formula) : fol_formula -> Prop :=
| cnd_hyp p : In p ctx -> ConventionalND ctx p
| cnd_closed p : ConventionalND [] p -> ConventionalND ctx p
| cnd_axiom p : ConventionalAxiom p -> ConventionalND ctx p
| cnd_imp_intro p q : ConventionalND (p::ctx) q -> ConventionalND ctx (FImp p q)
| cnd_imp_elim p q : ConventionalND ctx (FImp p q) -> ConventionalND ctx p -> ConventionalND ctx q
| cnd_neg_intro p : ConventionalND (p::ctx) nd_false -> ConventionalND ctx (FNeg p)
| cnd_classical p : ConventionalND (FNeg p::ctx) nd_false -> ConventionalND ctx p
| cnd_exfalso p q : ConventionalND ctx p -> ConventionalND ctx (FNeg p) -> ConventionalND ctx q
| cnd_and_intro p q : ConventionalND ctx p -> ConventionalND ctx q -> ConventionalND ctx (nd_and p q)
| cnd_and_left p q : ConventionalND ctx (nd_and p q) -> ConventionalND ctx p
| cnd_and_right p q : ConventionalND ctx (nd_and p q) -> ConventionalND ctx q
| cnd_or_left p q : ConventionalND ctx p -> ConventionalND ctx (nd_or p q)
| cnd_or_elim p q r : ConventionalND ctx (nd_or p q) -> ConventionalND (p::ctx) r -> ConventionalND (q::ctx) r -> ConventionalND ctx r
| cnd_all_intro x p : nd_fresh x ctx -> ConventionalND ctx p -> ConventionalND ctx (FAll x p)
| cnd_all_elim x y p : safe_subst x y p=true -> ConventionalND ctx (FAll x p) -> ConventionalND ctx (nd_subst x y p)
| cnd_all_alpha_reverse x y p : nd_not_bound y p=true -> nd_free y p=false ->
    ConventionalND ctx (FAll y (nd_subst x y p)) -> ConventionalND ctx (FAll x p)
| cnd_ex_intro x y p : safe_subst x y p=true -> ConventionalND ctx (nd_subst x y p) -> ConventionalND ctx (nd_ex x p)
| cnd_ex_elim x y p q : safe_subst x y p=true -> (x=y \/ nd_free y p=false) ->
    nd_fresh y ctx -> nd_free y q=false -> ConventionalND ctx (nd_ex x p) ->
    ConventionalND (nd_subst x y p::ctx) q -> ConventionalND ctx q
| cnd_eq_refl x : ConventionalND ctx (FEqual x x)
| cnd_eq_sym x y : ConventionalND ctx (FEqual x y) -> ConventionalND ctx (FEqual y x)
| cnd_eq_trans x y z : ConventionalND ctx (FEqual x y) -> ConventionalND ctx (FEqual y z) -> ConventionalND ctx (FEqual x z)
| cnd_eq_substitute x y p : safe_subst x y p=true -> ConventionalND ctx (FEqual x y) ->
    ConventionalND ctx p -> ConventionalND ctx (nd_subst x y p)
| cnd_mem_left x y z : ConventionalND ctx (FEqual x y) -> ConventionalND ctx (FMember x z) -> ConventionalND ctx (FMember y z)
| cnd_mem_right x y z : ConventionalND ctx (FEqual x y) -> ConventionalND ctx (FMember z x) -> ConventionalND ctx (FMember z y).
Theorem standard_to_conventional ctx p : StandardND ctx p -> ConventionalND ctx p.
Proof.
  intro H. induction H.
  - now apply cnd_hyp.
  - now apply cnd_closed.
  - apply cnd_axiom. eapply source_nonlogical_is_conventional; eassumption.
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
Theorem conventional_to_standard ctx p : ConventionalND ctx p -> StandardND ctx p.
Proof.
  intro H. induction H.
  - now apply std_hyp.
  - now apply std_closed.
  - apply std_closed,conventional_axiom_to_standard,H.
  - now apply std_imp_intro.
  - eapply std_imp_elim; eassumption.
  - now apply std_neg_intro.
  - now apply std_classical.
  - eapply std_exfalso with (p:=p); eassumption.
  - now apply std_and_intro.
  - eapply std_and_left; eassumption.
  - eapply std_and_right; eassumption.
  - now apply std_or_left.
  - eapply std_or_elim; eassumption.
  - eapply std_all_intro; eassumption.
  - eapply std_all_elim; eassumption.
  - eapply std_all_alpha_reverse; eassumption.
  - eapply std_ex_intro; eassumption.
  - eapply std_ex_elim; eassumption.
  - apply std_eq_refl.
  - now apply std_eq_sym.
  - eapply std_eq_trans; eassumption.
  - eapply std_eq_substitute; eassumption.
  - eapply std_mem_left; eassumption.
  - eapply std_mem_right; eassumption.
Qed.
Theorem conventional_iff_standard_nd ctx p : ConventionalND ctx p <-> StandardND ctx p.
Proof. split; [apply conventional_to_standard|apply standard_to_conventional]. Qed.
Theorem conventional_iff_augmented p : ConventionalND [] p <-> AugProvable p.
Proof. rewrite conventional_iff_standard_nd. symmetry. apply augmented_iff_standard_theorem. Qed.
Print Assumptions standard_to_conventional.
Print Assumptions conventional_to_standard.
Print Assumptions conventional_iff_augmented.
