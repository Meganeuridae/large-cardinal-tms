(** Capture avoidance that stops at a binder shadowing the substituted
    variable. This is more general than requiring the replacement name to be
    absent from every binder in the whole formula. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool.
From Berkeley Require Import ProofFormula LogicBridge LogicQuantifier LogicFresh TheoryIrreflexiveND
  AugmentedCapture StableLogic StableContext StableInstantiation.
Import ListNotations.
Theorem stable_equality_substitution_safe x y p : safe_subst x y p=true ->
  RenameStable (FImp (FEqual x y) (FImp p (nd_subst x y p))) /\
  RenameStable (FImp (FEqual x y) (FImp (nd_subst x y p) p)).
Proof.
  induction p as [a b|a b|p IH|p IH q JH|z p IH]; intro Safe.
  - cbn [nd_subst]. change
      (RenameStable (FImp (FEqual x y) (FImp (atom_of false a b)
        (atom_of false (subvar x y a) (subvar x y b)))) /\
       RenameStable (FImp (FEqual x y) (FImp
        (atom_of false (subvar x y a) (subvar x y b)) (atom_of false a b)))).
    split; apply sc_finish,sc_deduction,sc_deduction.
    + eapply sc_atom_substitute; apply sc_hyp; cbn; auto.
    + eapply sc_atom_unsubstitute; [apply stable_inst_all_distinctors|apply sc_hyp; cbn; auto|apply sc_hyp; cbn; auto].
  - cbn [nd_subst]. change
      (RenameStable (FImp (FEqual x y) (FImp (atom_of true a b)
        (atom_of true (subvar x y a) (subvar x y b)))) /\
       RenameStable (FImp (FEqual x y) (FImp
        (atom_of true (subvar x y a) (subvar x y b)) (atom_of true a b)))).
    split; apply sc_finish,sc_deduction,sc_deduction.
    + eapply sc_atom_substitute; apply sc_hyp; cbn; auto.
    + eapply sc_atom_unsubstitute; [apply stable_inst_all_distinctors|apply sc_hyp; cbn; auto|apply sc_hyp; cbn; auto].
  - cbn [safe_subst] in Safe. specialize (IH Safe). cbn [nd_subst]. now apply stable_inst_neg_substitution.
  - cbn [safe_subst] in Safe. apply andb_true_iff in Safe as [NP NQ].
    specialize (IH NP). specialize (JH NQ). cbn [nd_subst]. now apply stable_inst_imp_substitution.
  - cbn [safe_subst] in Safe. cbn [nd_subst]. destruct (Nat.eqb z x) eqn:ZX.
    + split; apply stable_logical,logical_weakening,logical_identity.
    + apply andb_true_iff in Safe as [ZY NP]. apply negb_true_iff, Nat.eqb_neq in ZY.
      apply Nat.eqb_neq in ZX. specialize (IH NP). split;
        eapply stable_inst_all_substitution; try apply stable_inst_all_distinctors; try eassumption; tauto.
Qed.
Theorem stable_all_instantiate_safe x y p : safe_subst x y p=true ->
  RenameStable (FImp (FAll x p) (nd_subst x y p)).
Proof.
  intro Safe. destruct (Nat.eq_dec x y) as [E|E].
  - subst y. rewrite nd_subst_self. apply stable_logical,logical_b5.
  - set (q := nd_subst x y p).
    assert (Fresh : ~occurs_free x q) by (unfold q; now apply nd_subst_fresh).
    assert (Sub : RenameStable (FImp (FEqual x y) (FImp p q))).
    { unfold q. exact (proj1 (stable_equality_substitution_safe x y p Safe)). }
    assert (Gen : RenameStable (FImp q (FAll x q))) by (now apply stable_fresh_C5).
    assert (Lift : RenameStable (FImp p (FImp (FEqual x y) (FAll x q)))).
    { apply sc_finish,sc_deduction,sc_deduction. eapply sc_mp.
      - apply sc_theorem. exact Gen.
      - eapply sc_with_antecedent; [exact Sub|apply sc_hyp; cbn; auto|apply sc_hyp; cbn; auto]. }
    eapply (stable_syllogism (FAll x p) (FAll x (FImp (FEqual x y) (FAll x q))) q).
    + now apply stable_all_monotone.
    + apply stable_logical,logical_b10.
Qed.
Print Assumptions stable_equality_substitution_safe.
Print Assumptions stable_all_instantiate_safe.
Theorem stable_quantifier_alpha_safe x y p : safe_subst x y p=true -> nd_free y p=false ->
  RenameStable (FImp (FAll y (FNeg (nd_subst x y p))) (FAll x (FNeg p))).
Proof.
  intros Safe NF. destruct (Nat.eq_dec x y) as [E|E].
  - subst y. rewrite nd_subst_self. apply stable_logical,logical_identity.
  - set (q:=nd_subst x y p).
    assert (FreshY : ~occurs_free y (FNeg p)).
    { unfold occurs_free. cbn [fresh_support]. apply nd_free_not_occurs. exact NF. }
    assert (Gen : RenameStable (FImp (FNeg p) (FAll y (FNeg p))) ) by (now apply stable_fresh_C5).
    assert (Sub : RenameStable (FImp (FEqual x y) (FImp (FNeg q) (FNeg p)))).
    { unfold q. pose proof (stable_equality_substitution_safe x y (FNeg p) Safe) as H.
      cbn [nd_subst] in H. exact (proj2 H). }
    assert (Point : RenameStable (FImp (FNeg q) (FImp (FEqual y x) (FAll y (FNeg p))))).
    { apply sc_finish,sc_deduction,sc_deduction.
      eapply sc_mp with (p:=FNeg p); [apply sc_theorem; exact Gen|].
      eapply sc_with_antecedent; [exact Sub| |apply sc_hyp; cbn; auto].
      eapply sc_mp; [apply sc_theorem,stable_equality_sym|apply sc_hyp; cbn; auto]. }
    assert (First : RenameStable (FImp (FAll y (FNeg q)) (FNeg p))).
    { eapply (stable_syllogism (FAll y (FNeg q))
        (FAll y (FImp (FEqual y x) (FAll y (FNeg p)))) (FNeg p)).
      - now apply stable_all_monotone.
      - apply stable_logical,logical_b10. }
    apply stable_fresh_generalization; [|exact First].
    unfold occurs_free. cbn [fresh_support].
    assert (XY : (x =? y)=false) by (now apply Nat.eqb_neq).
    rewrite XY. change (~occurs_free x q). unfold q. now apply nd_subst_fresh.
Qed.
Print Assumptions stable_quantifier_alpha_safe.
Theorem stable_all_alpha_reverse x y p : nd_not_bound y p=true -> nd_free y p=false ->
  RenameStable (FImp (FAll y (nd_subst x y p)) (FAll x p)).
Proof.
  intros NB NF. set (q:=nd_subst x y p).
  assert (Forward : RenameStable (FImp (FAll y q) (FAll y (FNeg (FNeg q))))).
  { apply stable_all_monotone,stable_inst_double_neg_intro. }
  assert (Middle : RenameStable (FImp (FAll y (FNeg (FNeg q))) (FAll x (FNeg (FNeg p))))).
  { unfold q. change (RenameStable (FImp (FAll y (FNeg (nd_subst x y (FNeg p))))
        (FAll x (FNeg (FNeg p))))).
    apply stable_quantifier_alpha_safe; [cbn [safe_subst]; now apply nd_not_bound_implies_safe|exact NF]. }
  assert (Back : RenameStable (FImp (FAll x (FNeg (FNeg p))) (FAll x p))).
  { apply stable_all_monotone,stable_inst_double_neg_elim. }
  eapply (stable_syllogism (FAll y q) (FAll y (FNeg (FNeg q))) (FAll x p)); [exact Forward|].
  eapply stable_syllogism; eassumption.
Qed.
Print Assumptions stable_all_alpha_reverse.
