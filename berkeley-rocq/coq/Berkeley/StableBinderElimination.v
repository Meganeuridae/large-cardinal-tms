(** Rename binders away from two names, using equivalences stable under all
    injective simultaneous variable renamings. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
From Berkeley Require Import ProofFormula TheoryIrreflexiveND LogicFinite StandardLogical StandardDistinctor
  StableLogic StableCongruence StableAlpha.
Import ListNotations.

Theorem stable_eliminate_two_binders a b p :
  exists q, StableEquiv p q /\ nd_not_bound a q=true /\ nd_not_bound b q=true.
Proof.
  induction p as [x y|x y|p IH|p IH q JH|x p IH].
  - exists (FEqual x y). cbn [nd_not_bound]. repeat split; apply stable_equiv_refl.
  - exists (FMember x y). cbn [nd_not_bound]. repeat split; apply stable_equiv_refl.
  - destruct IH as [q [Equiv [A B]]].
    exists (FNeg q). cbn [nd_not_bound]. split; [now apply stable_equiv_neg|auto].
  - destruct IH as [p' [EP [AP BP]]]. destruct JH as [q' [EQ [AQ BQ]]].
    exists (FImp p' q'). cbn [nd_not_bound]. split; [now apply stable_equiv_imp|].
    now rewrite AP,AQ,BP,BQ.
  - destruct IH as [q [Equiv [A B]]].
    destruct (Nat.eq_dec x a) as [XA|XA]; [|destruct (Nat.eq_dec x b) as [XB|XB]].
    + set (c:=S (Nat.max (Nat.max a b) (max_var q))).
      assert (AC:a<c) by (unfold c;pose proof (Nat.le_max_l a b);pose proof (Nat.le_max_l (Nat.max a b) (max_var q));lia).
      assert (BC:b<c) by (unfold c;pose proof (Nat.le_max_r a b);pose proof (Nat.le_max_l (Nat.max a b) (max_var q));lia).
      assert (M:S (max_var q)<=c) by (unfold c;pose proof (Nat.le_max_r (Nat.max a b) (max_var q));lia).
      assert (V:vars_below c q) by (eapply vars_below_monotone; [exact M|apply vars_below_max]).
      destruct (below_var_is_fresh c q V) as [Free Bound].
      exists (FAll c (nd_subst x c q)). split.
      * eapply (stable_equiv_trans _ (FAll x q)); [now apply stable_equiv_all|now apply stable_alpha_equiv].
      * cbn [nd_not_bound]. rewrite !nd_not_bound_substitution, A, B.
        assert ((c=?a)=false) by (apply Nat.eqb_neq;lia).
        assert ((c=?b)=false) by (apply Nat.eqb_neq;lia).
        now rewrite H,H0.
    + set (c:=S (Nat.max (Nat.max a b) (max_var q))).
      assert (AC:a<c) by (unfold c;pose proof (Nat.le_max_l a b);pose proof (Nat.le_max_l (Nat.max a b) (max_var q));lia).
      assert (BC:b<c) by (unfold c;pose proof (Nat.le_max_r a b);pose proof (Nat.le_max_l (Nat.max a b) (max_var q));lia).
      assert (M:S (max_var q)<=c) by (unfold c;pose proof (Nat.le_max_r (Nat.max a b) (max_var q));lia).
      assert (V:vars_below c q) by (eapply vars_below_monotone; [exact M|apply vars_below_max]).
      destruct (below_var_is_fresh c q V) as [Free Bound].
      exists (FAll c (nd_subst x c q)). split.
      * eapply (stable_equiv_trans _ (FAll x q)); [now apply stable_equiv_all|now apply stable_alpha_equiv].
      * cbn [nd_not_bound]. rewrite !nd_not_bound_substitution, A, B.
        assert ((c=?a)=false) by (apply Nat.eqb_neq;lia).
        assert ((c=?b)=false) by (apply Nat.eqb_neq;lia).
        now rewrite H,H0.
    + exists (FAll x q). split; [now apply stable_equiv_all|].
      cbn [nd_not_bound]. apply Nat.eqb_neq in XA,XB. now rewrite XA,XB,A,B.
Qed.
Print Assumptions stable_eliminate_two_binders.
