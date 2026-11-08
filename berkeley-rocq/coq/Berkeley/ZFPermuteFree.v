(** A constructive first step toward simultaneous tuple normalization: swap
    two variable names in a theorem when neither name occurs as a binder.
    A fresh temporary name makes the three substitutions capture-safe. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
From Berkeley Require Import ProofFormula LogicBridge LogicFinite TheoryIrreflexiveND AugmentedInstantiation AugmentedCapture
  StandardND StandardLogical StandardDistinctor NatPermutations ZFVariableSyntax.
Import ListNotations.
Lemma swap_subvar a b c u : a<>b -> c<>a -> c<>b -> u<>c ->
  subvar c b (subvar b a (subvar a c u)) = swap_nat a b u.
Proof.
  intros AB CA CB UC. destruct (Nat.eq_dec u a) as [A|A].
  - subst u. unfold subvar,swap_nat. rewrite Nat.eqb_refl.
    assert ((c=?b)=false) by (apply Nat.eqb_neq;congruence). rewrite H,Nat.eqb_refl. reflexivity.
  - destruct (Nat.eq_dec u b) as [B|B].
    + subst u. unfold subvar,swap_nat. assert ((b=?a)=false) by (apply Nat.eqb_neq;congruence).
      rewrite H,Nat.eqb_refl. assert ((a=?c)=false) by (apply Nat.eqb_neq;congruence). now rewrite H0.
    + unfold subvar,swap_nat. assert ((u=?a)=false) by (apply Nat.eqb_neq;congruence).
      assert ((u=?b)=false) by (apply Nat.eqb_neq;congruence).
      assert ((u=?c)=false) by (apply Nat.eqb_neq;congruence). now rewrite H,H0,H1.
Qed.
Lemma swap_substitution_formula a b c p : a<>b -> c<>a -> c<>b -> nd_free c p=false ->
  nd_not_bound a p=true -> nd_not_bound b p=true -> nd_not_bound c p=true ->
  nd_subst c b (nd_subst b a (nd_subst a c p)) = rename_formula (swap_nat a b) p.
Proof.
  intros AB CA CB. induction p as [x y|x y|p IH|p IH q JH|z p IH];
    intros Free BA BB BC; cbn [nd_free nd_not_bound] in *.
  - apply orb_false_iff in Free as [X Y]. apply Nat.eqb_neq in X,Y.
    cbn [nd_subst rename_formula]. change (FEqual (subvar c b (subvar b a (subvar a c x)))
      (subvar c b (subvar b a (subvar a c y))) = FEqual (swap_nat a b x) (swap_nat a b y)).
    now rewrite !(swap_subvar a b c) by congruence.
  - apply orb_false_iff in Free as [X Y]. apply Nat.eqb_neq in X,Y.
    cbn [nd_subst rename_formula]. change (FMember (subvar c b (subvar b a (subvar a c x)))
      (subvar c b (subvar b a (subvar a c y))) = FMember (swap_nat a b x) (swap_nat a b y)).
    now rewrite !(swap_subvar a b c) by congruence.
  - cbn [nd_subst rename_formula]. f_equal. now apply IH.
  - apply orb_false_iff in Free as [P Q]. apply andb_true_iff in BA as [PA QA].
    apply andb_true_iff in BB as [PB QB]. apply andb_true_iff in BC as [PC QC].
    cbn [nd_subst rename_formula]. f_equal; [apply IH|apply JH]; assumption.
  - apply andb_true_iff in BA as [ZA PA]. apply andb_true_iff in BB as [ZB PB].
    apply andb_true_iff in BC as [ZC PC]. apply negb_true_iff,Nat.eqb_neq in ZA,ZB,ZC.
    assert (CAz : (c=?z)=false) by (apply Nat.eqb_neq;congruence). rewrite CAz in Free.
    cbn [nd_subst rename_formula].
    assert (Za : (z=?a)=false) by (apply Nat.eqb_neq;assumption).
    assert (Zb : (z=?b)=false) by (apply Nat.eqb_neq;assumption).
    assert (Zc : (z=?c)=false) by (apply Nat.eqb_neq;assumption).
    rewrite Za. cbn [nd_subst]. rewrite Zb. cbn [nd_subst]. rewrite Zc.
    rewrite (swap_other a b z ZA ZB). f_equal. now apply IH.
Qed.
Theorem standard_theorem_swap_without_bound a b p : a<>b ->
  nd_not_bound a p=true -> nd_not_bound b p=true -> StandardND [] p ->
  StandardND [] (rename_formula (swap_nat a b) p).
Proof.
  intros AB BA BB H. set (c:=S (Nat.max (Nat.max a b) (max_var p))).
  assert (AC:a<c) by (unfold c;pose proof (Nat.le_max_l a b);pose proof (Nat.le_max_l (Nat.max a b) (max_var p));lia).
  assert (BC:b<c) by (unfold c;pose proof (Nat.le_max_r a b);pose proof (Nat.le_max_l (Nat.max a b) (max_var p));lia).
  assert (M:S (max_var p)<=c) by (unfold c;pose proof (Nat.le_max_r (Nat.max a b) (max_var p));lia).
  assert (V:vars_below c p) by (eapply vars_below_monotone; [exact M|apply vars_below_max]).
  destruct (below_var_is_fresh c p V) as [Free Bound].
  assert (H1:StandardND [] (nd_subst a c p)).
  { apply standard_theorem_substitution; [now apply nd_not_bound_implies_safe|exact H]. }
  assert (H2:StandardND [] (nd_subst b a (nd_subst a c p))).
  { apply standard_theorem_substitution; [apply nd_not_bound_implies_safe; now rewrite nd_not_bound_substitution|exact H1]. }
  assert (H3:StandardND [] (nd_subst c b (nd_subst b a (nd_subst a c p)))).
  { apply standard_theorem_substitution; [apply nd_not_bound_implies_safe; now rewrite !nd_not_bound_substitution|exact H2]. }
  rewrite (swap_substitution_formula a b c p AB ltac:(lia) ltac:(lia) Free BA BB Bound) in H3. exact H3.
Qed.
Print Assumptions swap_substitution_formula.
Print Assumptions standard_theorem_swap_without_bound.
