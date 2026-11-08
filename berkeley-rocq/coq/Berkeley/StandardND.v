(** A separately specified classical first-order natural deduction system.
    The only nonlogical axiom instances are candidate indices >=14. *)
From Stdlib Require Import Lists.List.
From Berkeley Require Import Syntax SyntaxData ProofFormula ProofPresentation TheoryIrreflexiveND AugmentedCapture.
Import ListNotations.
Inductive StandardND (ctx:list fol_formula) : fol_formula -> Prop :=
| std_hyp p : In p ctx -> StandardND ctx p
| std_closed p : StandardND [] p -> StandardND ctx p
| std_nonlogical i f vars holes : 14<=i -> nth_error candidate_axioms i=Some f ->
    StandardND ctx (independent_instance vars holes f)
| std_imp_intro p q : StandardND (p::ctx) q -> StandardND ctx (FImp p q)
| std_imp_elim p q : StandardND ctx (FImp p q) -> StandardND ctx p -> StandardND ctx q
| std_neg_intro p : StandardND (p::ctx) nd_false -> StandardND ctx (FNeg p)
| std_classical p : StandardND (FNeg p::ctx) nd_false -> StandardND ctx p
| std_exfalso p q : StandardND ctx p -> StandardND ctx (FNeg p) -> StandardND ctx q
| std_and_intro p q : StandardND ctx p -> StandardND ctx q -> StandardND ctx (nd_and p q)
| std_and_left p q : StandardND ctx (nd_and p q) -> StandardND ctx p
| std_and_right p q : StandardND ctx (nd_and p q) -> StandardND ctx q
| std_or_left p q : StandardND ctx p -> StandardND ctx (nd_or p q)
| std_or_elim p q r : StandardND ctx (nd_or p q) -> StandardND (p::ctx) r -> StandardND (q::ctx) r -> StandardND ctx r
| std_all_intro x p : nd_fresh x ctx -> StandardND ctx p -> StandardND ctx (FAll x p)
| std_all_elim x y p : safe_subst x y p=true -> StandardND ctx (FAll x p) -> StandardND ctx (nd_subst x y p)
| std_all_alpha_reverse x y p : nd_not_bound y p=true -> nd_free y p=false ->
    StandardND ctx (FAll y (nd_subst x y p)) -> StandardND ctx (FAll x p)
| std_ex_intro x y p : safe_subst x y p=true -> StandardND ctx (nd_subst x y p) -> StandardND ctx (nd_ex x p)
| std_ex_elim x y p q : safe_subst x y p=true -> (x=y \/ nd_free y p=false) ->
    nd_fresh y ctx -> nd_free y q=false -> StandardND ctx (nd_ex x p) ->
    StandardND (nd_subst x y p::ctx) q -> StandardND ctx q
| std_eq_refl x : StandardND ctx (FEqual x x)
| std_eq_sym x y : StandardND ctx (FEqual x y) -> StandardND ctx (FEqual y x)
| std_eq_trans x y z : StandardND ctx (FEqual x y) -> StandardND ctx (FEqual y z) -> StandardND ctx (FEqual x z)
| std_eq_substitute x y p : safe_subst x y p=true -> StandardND ctx (FEqual x y) ->
    StandardND ctx p -> StandardND ctx (nd_subst x y p)
| std_mem_left x y z : StandardND ctx (FEqual x y) -> StandardND ctx (FMember x z) -> StandardND ctx (FMember y z)
| std_mem_right x y z : StandardND ctx (FEqual x y) -> StandardND ctx (FMember z x) -> StandardND ctx (FMember z y).
Print Assumptions StandardND.
