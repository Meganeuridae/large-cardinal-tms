(** Derivation of fresh-variable generalization from the actual schemas,
    conditional only on the indicated distinctors being theorems. *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
From Berkeley Require Import ProofFormula ProofPresentation LogicBridge LogicQuantifier.
Import ListNotations.
Definition distinctor x y := FNeg (FAll x (FEqual x y)).
Fixpoint fresh_support x f :=
  match f with
  | FEqual y z | FMember y z => [y;z]
  | FNeg p => fresh_support x p
  | FImp p q => fresh_support x p ++ fresh_support x q
  | FAll y p => if Nat.eqb x y then [] else fresh_support x p
  end.
Definition occurs_free x f := In x (fresh_support x f).

Theorem presented_fresh_from_distinctors x f :
  (forall y, In y (fresh_support x f) -> PresentedProvable (distinctor x y)) ->
  PresentedProvable (FImp f (FAll x f)).
Proof.
  induction f as [y z|y z|p IH|p IHp q IHq|y p IH]; intro H.
  - eapply presented_mp.
    + eapply presented_mp.
      * apply logical_embeds_in_presented, logical_b9.
      * apply H. cbn. auto.
    + apply H. cbn. auto.
  - eapply presented_mp.
    + eapply presented_mp.
      * apply logical_embeds_in_presented, logical_b14.
      * apply H. cbn. auto.
    + apply H. cbn. auto.
  - eapply presented_mp.
    + apply logical_embeds_in_presented, logical_fresh_negation.
    + apply presented_gen, IH. exact H.
  - assert (HP : PresentedProvable (FImp p (FAll x p))).
    { apply IHp. intros v V. apply H. cbn. apply in_or_app. now left. }
    assert (HQ : PresentedProvable (FImp q (FAll x q))).
    { apply IHq. intros v V. apply H. cbn. apply in_or_app. now right. }
    eapply presented_mp.
    + eapply presented_mp.
      * apply logical_embeds_in_presented, logical_fresh_implication.
      * now apply presented_gen.
    + exact HQ.
  - destruct (Nat.eq_dec x y) as [E|E].
    + subst y. apply logical_embeds_in_presented. apply (proj1 (logical_all_idempotent x p)).
    + assert (HP : PresentedProvable (FImp p (FAll x p))).
      { apply IH. intros v V. apply H. cbn. apply Nat.eqb_neq in E. now rewrite E. }
      eapply presented_mp.
      * apply logical_embeds_in_presented, logical_fresh_quantifier.
      * now apply presented_gen.
Qed.
Corollary presented_fresh_C5 x f :
  (forall y, x<>y -> PresentedProvable (distinctor x y)) ->
  ~occurs_free x f -> PresentedProvable (FImp f (FAll x f)).
Proof.
  intros Dist Fresh. apply presented_fresh_from_distinctors. intros y Y.
  apply Dist. intro E. subst y. now apply Fresh.
Qed.
Lemma presented_syllogism p q r : PresentedProvable (FImp p q) ->
  PresentedProvable (FImp q r) -> PresentedProvable (FImp p r).
Proof.
  intros H K.
  assert (W : PresentedProvable (FImp p (FImp q r))).
  { eapply presented_mp; [apply logical_embeds_in_presented, logical_b1|exact K]. }
  eapply presented_mp; [eapply presented_mp; [apply logical_embeds_in_presented, logical_b2|exact W]|exact H].
Qed.
Lemma presented_all_monotone x p q : PresentedProvable (FImp p q) ->
  PresentedProvable (FImp (FAll x p) (FAll x q)).
Proof.
  intro H. eapply presented_mp.
  - apply logical_embeds_in_presented, logical_all_distribution.
  - now apply presented_gen.
Qed.
Theorem presented_fresh_generalization x p q :
  (forall y, x<>y -> PresentedProvable (distinctor x y)) ->
  ~occurs_free x p -> PresentedProvable (FImp p q) -> PresentedProvable (FImp p (FAll x q)).
Proof.
  intros Dist Fresh H. eapply (presented_syllogism p (FAll x p) (FAll x q)).
  - now apply presented_fresh_C5.
  - now apply presented_all_monotone.
Qed.
Print Assumptions presented_fresh_from_distinctors.
Print Assumptions presented_fresh_C5.
Print Assumptions presented_fresh_generalization.

Theorem presented_fresh_generalization_with_support x p q :
  (forall y, In y (fresh_support x p) -> PresentedProvable (distinctor x y)) ->
  PresentedProvable (FImp p q) -> PresentedProvable (FImp p (FAll x q)).
Proof.
  intros Dist H. eapply (presented_syllogism p (FAll x p) (FAll x q)).
  - now apply presented_fresh_from_distinctors.
  - now apply presented_all_monotone.
Qed.
Print Assumptions presented_fresh_generalization_with_support.
