(** Transfer of the independently checked ND certificate to the explicitly
    augmented calculus. This does not change the original machine calculus. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import Syntax TheorySchemas ProofFormula ProofPresentation LogicBridge LogicQuantifier
  TheoryIrreflexiveND AugmentedLogic AugmentedContext AugmentedInstantiation.
Import ListNotations.

Definition AugQuantifierFresh := forall x p, nd_free x p=false -> AugProvable (FImp p (FAll x p)).
Definition AugQuantifierSubst := forall x y p, nd_not_bound y p=true ->
  AugProvable (FImp (FAll x p) (nd_subst x y p)).
Definition AugQuantifierAlpha := forall x y p, nd_not_bound y p=true -> nd_free y p=false ->
  AugProvable (FImp (FAll y (FNeg (nd_subst x y p))) (FAll x (FNeg p))).
Definition AugEqualityRules :=
  (forall x, AugProvable (FEqual x x)) /\
  (forall x y, AugProvable (FImp (FEqual x y) (FEqual y x))) /\
  (forall x y z, AugProvable (FImp (FEqual x y) (FImp (FMember z x) (FMember z y)))).

Theorem ac_all_intro_from_fresh : AugQuantifierFresh -> forall ctx x p,
  nd_fresh x ctx -> AugContext ctx p -> AugContext ctx (FAll x p).
Proof.
  intros Fresh ctx. induction ctx as [|h ctx IH]; intros x p F H.
  - apply ac_theorem,aug_gen,ac_finish. exact H.
  - assert (Fh : nd_free x h=false) by (apply F; now left).
    assert (Fctx : nd_fresh x ctx) by (intros q Q; apply F; now right).
    pose proof (ac_deduction ctx h p H) as Impl.
    pose proof (IH x (FImp h p) Fctx Impl) as Generalized.
    assert (Dist : AugContext ctx (FImp (FAll x h) (FAll x p))).
    { eapply ac_mp; [apply ac_logical,logical_all_distribution|exact Generalized]. }
    eapply ac_mp.
    + eapply ac_weaken; [|exact Dist]. intros q Q. now right.
    + eapply ac_mp; [apply ac_theorem,Fresh,Fh|apply ac_hyp; now left].
Qed.

Lemma ac_all_elim_from_subst : AugQuantifierSubst -> forall ctx x y p,
  nd_not_bound y p=true -> AugContext ctx (FAll x p) -> AugContext ctx (nd_subst x y p).
Proof. intros Spec ctx x y p Safe H. eapply ac_mp; [apply ac_theorem,Spec,Safe|exact H]. Qed.

Lemma ac_ex_intro_from_subst : AugQuantifierSubst -> forall ctx x y p,
  nd_not_bound y p=true -> AugContext ctx (nd_subst x y p) -> AugContext ctx (nd_ex x p).
Proof.
  intros Spec ctx x y p Safe H. unfold nd_ex. apply ac_neg_intro.
  assert (Neg : AugContext (FAll x (FNeg p)::ctx) (FNeg (nd_subst x y p))).
  { change (AugContext (FAll x (FNeg p)::ctx) (nd_subst x y (FNeg p))).
    eapply ac_all_elim_from_subst; [exact Spec|exact Safe|apply ac_hyp; now left]. }
  eapply ac_explosion with (p:=nd_subst x y p); [|exact Neg].
  eapply ac_weaken; [|exact H]. intros q Q. now right.
Qed.

Lemma ac_ex_elim_from_quantifiers : AugQuantifierFresh -> AugQuantifierAlpha ->
  forall ctx x y p q, nd_not_bound y p=true -> nd_free y p=false ->
  nd_fresh y ctx -> nd_free y q=false -> AugContext ctx (nd_ex x p) ->
  AugContext (nd_subst x y p::ctx) q -> AugContext ctx q.
Proof.
  intros Fresh Alpha ctx x y p q Safe Free Fctx Fq Ex Branch.
  apply ac_deduction in Branch. apply ac_classical.
  assert (Branch' : AugContext (FNeg q::ctx) (FImp (nd_subst x y p) q)).
  { eapply ac_weaken; [|exact Branch]. intros r R. now right. }
  assert (NegSub : AugContext (FNeg q::ctx) (FNeg (nd_subst x y p))).
  { apply ac_neg_intro. eapply ac_explosion with (p:=q).
    - eapply ac_mp; [eapply ac_weaken; [|exact Branch']; intros r R; now right|apply ac_hyp; now left].
    - apply ac_hyp. cbn. auto. }
  assert (Fy : nd_fresh y (FNeg q::ctx)).
  { unfold nd_fresh. intros r [E|E]; [subst; exact Fq|now apply Fctx]. }
  pose proof (ac_all_intro_from_fresh Fresh (FNeg q::ctx) y _ Fy NegSub) as AllY.
  assert (AllX : AugContext (FNeg q::ctx) (FAll x (FNeg p))).
  { eapply ac_mp; [apply ac_theorem,Alpha; eassumption|exact AllY]. }
  eapply ac_explosion with (p:=FAll x (FNeg p)); [exact AllX|].
  eapply ac_weaken; [|exact Ex]. intros r R. now right.
Qed.

Theorem nd_to_augcontext : AugQuantifierFresh -> AugQuantifierSubst -> AugQuantifierAlpha -> AugEqualityRules ->
  forall ctx p, ND ctx p -> AugContext ctx p.
Proof.
  intros Fresh Spec Alpha [Refl [Sym Mem]] ctx p Derivation. induction Derivation.
  - now apply ac_hyp.
  - apply ac_theorem,aug_original. assumption.
  - now apply ac_deduction.
  - eapply ac_mp; eassumption.
  - now apply ac_neg_intro.
  - eapply ac_explosion with (p:=p); eassumption.
  - now apply ac_and_intro.
  - eapply ac_and_left; eassumption.
  - eapply ac_and_right; eassumption.
  - now apply ac_or_left.
  - eapply ac_or_elim; eassumption.
  - unfold nd_iff in IHDerivation1. eapply ac_mp; [eapply ac_and_left; exact IHDerivation1|exact IHDerivation2].
  - unfold nd_iff in IHDerivation1. eapply ac_mp; [eapply ac_and_right; exact IHDerivation1|exact IHDerivation2].
  - eapply ac_all_intro_from_fresh; eassumption.
  - eapply ac_all_elim_from_subst; eassumption.
  - eapply ac_ex_intro_from_subst; eassumption.
  - eapply ac_ex_elim_from_quantifiers; eassumption.
  - apply ac_theorem,Refl.
  - eapply ac_mp; [apply ac_theorem,Sym|exact IHDerivation].
  - eapply ac_mp; [eapply ac_mp; [apply ac_theorem,Mem|exact IHDerivation1]|exact IHDerivation2].
Qed.

Theorem aug_irreflexive_from_quantifier_bridges :
  AugQuantifierFresh -> AugQuantifierSubst -> AugQuantifierAlpha -> AugEqualityRules ->
  AugProvable (FNeg (FMember 0 0)).
Proof.
  intros Fresh Spec Alpha Eq. apply ac_finish.
  eapply nd_to_augcontext; [exact Fresh|exact Spec|exact Alpha|exact Eq|apply natural_deduction_irreflexive].
Qed.

(** The extra distinctors in AugProvable discharge the quantifier bridges.
    This theorem is about the augmented calculus, not the original machine. *)
Theorem augmented_irreflexive : AugProvable (FNeg (FMember 0 0)).
Proof.
  apply aug_irreflexive_from_quantifier_bridges.
  - intros x p Fresh. apply aug_fresh_C5,nd_free_not_occurs,Fresh.
  - exact aug_all_instantiate.
  - exact aug_quantifier_alpha.
  - repeat split.
    + exact aug_equality_reflexive.
    + exact aug_equality_sym.
    + intros x y z. apply aug_logical,logical_b13.
Qed.

Print Assumptions ac_all_intro_from_fresh.
Print Assumptions ac_ex_intro_from_subst.
Print Assumptions ac_ex_elim_from_quantifiers.
Print Assumptions nd_to_augcontext.
Print Assumptions aug_irreflexive_from_quantifier_bridges.
Print Assumptions augmented_irreflexive.
