(** Interpretation of independent classical first-order ND in the separate
    guarded-distinguisher calculus. Only actual nonlogical source axioms are
    used as theory axioms. *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
From Berkeley Require Import ProofFormula ProofPresentation LogicBridge LogicQuantifier LogicFresh
  TheoryIrreflexiveND AugmentedLogic AugmentedContext AugmentedInstantiation AugmentedIrreflexive
  AugmentedCapture StandardND.
Import ListNotations.
Lemma ac_standard_all_intro ctx x p : nd_fresh x ctx -> AugContext ctx p -> AugContext ctx (FAll x p).
Proof. apply ac_all_intro_from_fresh. intros y q H. now apply aug_fresh_C5,nd_free_not_occurs. Qed.
Lemma ac_standard_all_elim ctx x y p : safe_subst x y p=true ->
  AugContext ctx (FAll x p) -> AugContext ctx (nd_subst x y p).
Proof. intros Safe H. eapply ac_mp; [apply ac_theorem,aug_all_instantiate_safe,Safe|exact H]. Qed.
Lemma ac_standard_ex_intro ctx x y p : safe_subst x y p=true ->
  AugContext ctx (nd_subst x y p) -> AugContext ctx (nd_ex x p).
Proof.
  intros Safe H. unfold nd_ex. apply ac_neg_intro.
  assert (Neg : AugContext (FAll x (FNeg p)::ctx) (FNeg (nd_subst x y p))).
  { change (AugContext (FAll x (FNeg p)::ctx) (nd_subst x y (FNeg p))).
    eapply ac_standard_all_elim; [exact Safe|apply ac_hyp; now left]. }
  eapply ac_explosion with (p:=nd_subst x y p); [|exact Neg].
  eapply ac_weaken; [|exact H]. intros q Q. now right.
Qed.
Lemma aug_standard_alpha x y p : safe_subst x y p=true -> (x=y \/ nd_free y p=false) ->
  AugProvable (FImp (FAll y (FNeg (nd_subst x y p))) (FAll x (FNeg p))).
Proof.
  intros Safe [E|Free].
  - subst y. rewrite nd_subst_self. apply aug_logical,logical_identity.
  - now apply aug_quantifier_alpha_safe.
Qed.
Lemma ac_standard_ex_elim ctx x y p q : safe_subst x y p=true -> (x=y \/ nd_free y p=false) ->
  nd_fresh y ctx -> nd_free y q=false -> AugContext ctx (nd_ex x p) ->
  AugContext (nd_subst x y p::ctx) q -> AugContext ctx q.
Proof.
  intros Safe Free Fctx Fq Ex Branch.
  apply ac_deduction in Branch. apply ac_classical.
  assert (Branch' : AugContext (FNeg q::ctx) (FImp (nd_subst x y p) q)).
  { eapply ac_weaken; [|exact Branch]. intros r R. now right. }
  assert (NegSub : AugContext (FNeg q::ctx) (FNeg (nd_subst x y p))).
  { apply ac_neg_intro. eapply ac_explosion with (p:=q).
    - eapply ac_mp; [eapply ac_weaken; [|exact Branch']; intros r R; now right|apply ac_hyp; now left].
    - apply ac_hyp. cbn. auto. }
  assert (Fy : nd_fresh y (FNeg q::ctx)).
  { unfold nd_fresh. intros r [E|E]; [subst; exact Fq|now apply Fctx]. }
  pose proof (ac_standard_all_intro (FNeg q::ctx) y _ Fy NegSub) as AllY.
  assert (AllX : AugContext (FNeg q::ctx) (FAll x (FNeg p))).
  { eapply ac_mp; [apply ac_theorem,aug_standard_alpha; eassumption|exact AllY]. }
  eapply ac_explosion with (p:=FAll x (FNeg p)); [exact AllX|].
  eapply ac_weaken; [|exact Ex]. intros r R. now right.
Qed.
Theorem standard_nd_to_augmented ctx p : StandardND ctx p -> AugContext ctx p.
Proof.
  intro H. induction H.
  - now apply ac_hyp.
  - apply ac_theorem,ac_finish,IHStandardND.
  - apply ac_theorem,aug_original. eapply presented_axiom; exact H0.
  - now apply ac_deduction.
  - eapply ac_mp; eassumption.
  - now apply ac_neg_intro.
  - now apply ac_classical.
  - eapply ac_explosion with (p:=p); eassumption.
  - now apply ac_and_intro.
  - eapply ac_and_left; eassumption.
  - eapply ac_and_right; eassumption.
  - now apply ac_or_left.
  - eapply ac_or_elim; eassumption.
  - eapply ac_standard_all_intro; eassumption.
  - eapply ac_standard_all_elim; eassumption.
  - eapply ac_mp; [apply ac_theorem,aug_all_alpha_reverse; eassumption|exact IHStandardND].
  - eapply ac_standard_ex_intro; eassumption.
  - eapply ac_standard_ex_elim; eassumption.
  - apply ac_theorem,aug_equality_reflexive.
  - eapply ac_mp; [apply ac_theorem,aug_equality_sym|exact IHStandardND].
  - assert (S : AugContext ctx (FEqual y x)).
    { eapply ac_mp; [apply ac_theorem,aug_equality_sym|exact IHStandardND1]. }
    eapply ac_mp; [eapply ac_mp; [apply ac_logical,logical_b8|exact S]|exact IHStandardND2].
  - eapply ac_mp; [eapply ac_mp; [apply ac_theorem; exact (proj1 (aug_equality_substitution_safe x y p H))|exact IHStandardND1]|exact IHStandardND2].
  - eapply ac_mp; [eapply ac_mp; [apply ac_logical,logical_b12|exact IHStandardND1]|exact IHStandardND2].
  - eapply ac_mp; [eapply ac_mp; [apply ac_logical,logical_b13|exact IHStandardND1]|exact IHStandardND2].
Qed.
Theorem standard_theorem_to_augmented p : StandardND [] p -> AugProvable p.
Proof. intro H. apply ac_finish,standard_nd_to_augmented,H. Qed.
Print Assumptions standard_nd_to_augmented.
Print Assumptions standard_theorem_to_augmented.
