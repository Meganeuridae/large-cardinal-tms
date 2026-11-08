(** Capture avoidance that stops at a binder shadowing the substituted
    variable. This is more general than requiring the replacement name to be
    absent from every binder in the whole formula. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool.
From Berkeley Require Import ProofFormula LogicBridge LogicQuantifier LogicFresh TheoryIrreflexiveND
  AugmentedLogic AugmentedContext AugmentedInstantiation.
Import ListNotations.
Fixpoint safe_subst x y p :=
  match p with
  | FEqual _ _ | FMember _ _ => true
  | FNeg p => safe_subst x y p
  | FImp p q => safe_subst x y p && safe_subst x y q
  | FAll z p => if Nat.eqb z x then true else negb (Nat.eqb z y) && safe_subst x y p
  end.
Lemma nd_not_bound_implies_safe x y p : nd_not_bound y p=true -> safe_subst x y p=true.
Proof.
  induction p as [a b|a b|p IH|p IH q JH|z p IH]; cbn [nd_not_bound safe_subst]; auto.
  - rewrite !andb_true_iff. intros [P Q]. split; auto.
  - intros H. destruct (Nat.eqb z x); auto. apply andb_true_iff in H as [Z P].
    apply andb_true_iff. split; auto.
Qed.
Theorem aug_equality_substitution_safe x y p : safe_subst x y p=true ->
  AugProvable (FImp (FEqual x y) (FImp p (nd_subst x y p))) /\
  AugProvable (FImp (FEqual x y) (FImp (nd_subst x y p) p)).
Proof.
  induction p as [a b|a b|p IH|p IH q JH|z p IH]; intro Safe.
  - cbn [nd_subst]. change
      (AugProvable (FImp (FEqual x y) (FImp (atom_of false a b)
        (atom_of false (subvar x y a) (subvar x y b)))) /\
       AugProvable (FImp (FEqual x y) (FImp
        (atom_of false (subvar x y a) (subvar x y b)) (atom_of false a b)))).
    split; apply ac_finish,ac_deduction,ac_deduction.
    + eapply ac_atom_substitute; apply ac_hyp; cbn; auto.
    + eapply ac_atom_unsubstitute; [apply aug_inst_all_distinctors|apply ac_hyp; cbn; auto|apply ac_hyp; cbn; auto].
  - cbn [nd_subst]. change
      (AugProvable (FImp (FEqual x y) (FImp (atom_of true a b)
        (atom_of true (subvar x y a) (subvar x y b)))) /\
       AugProvable (FImp (FEqual x y) (FImp
        (atom_of true (subvar x y a) (subvar x y b)) (atom_of true a b)))).
    split; apply ac_finish,ac_deduction,ac_deduction.
    + eapply ac_atom_substitute; apply ac_hyp; cbn; auto.
    + eapply ac_atom_unsubstitute; [apply aug_inst_all_distinctors|apply ac_hyp; cbn; auto|apply ac_hyp; cbn; auto].
  - cbn [safe_subst] in Safe. specialize (IH Safe). cbn [nd_subst]. now apply aug_inst_neg_substitution.
  - cbn [safe_subst] in Safe. apply andb_true_iff in Safe as [NP NQ].
    specialize (IH NP). specialize (JH NQ). cbn [nd_subst]. now apply aug_inst_imp_substitution.
  - cbn [safe_subst] in Safe. cbn [nd_subst]. destruct (Nat.eqb z x) eqn:ZX.
    + split; apply aug_logical,logical_weakening,logical_identity.
    + apply andb_true_iff in Safe as [ZY NP]. apply negb_true_iff, Nat.eqb_neq in ZY.
      apply Nat.eqb_neq in ZX. specialize (IH NP). split;
        eapply aug_inst_all_substitution; try apply aug_inst_all_distinctors; try eassumption; tauto.
Qed.
Theorem aug_all_instantiate_safe x y p : safe_subst x y p=true ->
  AugProvable (FImp (FAll x p) (nd_subst x y p)).
Proof.
  intro Safe. destruct (Nat.eq_dec x y) as [E|E].
  - subst y. rewrite nd_subst_self. apply aug_logical,logical_b5.
  - set (q := nd_subst x y p).
    assert (Fresh : ~occurs_free x q) by (unfold q; now apply nd_subst_fresh).
    assert (Sub : AugProvable (FImp (FEqual x y) (FImp p q))).
    { unfold q. exact (proj1 (aug_equality_substitution_safe x y p Safe)). }
    assert (Gen : AugProvable (FImp q (FAll x q))) by (now apply aug_fresh_C5).
    assert (Lift : AugProvable (FImp p (FImp (FEqual x y) (FAll x q)))).
    { apply ac_finish,ac_deduction,ac_deduction. eapply ac_mp.
      - apply ac_theorem. exact Gen.
      - eapply ac_with_antecedent; [exact Sub|apply ac_hyp; cbn; auto|apply ac_hyp; cbn; auto]. }
    eapply (aug_syllogism (FAll x p) (FAll x (FImp (FEqual x y) (FAll x q))) q).
    + now apply aug_all_monotone.
    + apply aug_logical,logical_b10.
Qed.
Print Assumptions aug_equality_substitution_safe.
Print Assumptions aug_all_instantiate_safe.
Theorem aug_quantifier_alpha_safe x y p : safe_subst x y p=true -> nd_free y p=false ->
  AugProvable (FImp (FAll y (FNeg (nd_subst x y p))) (FAll x (FNeg p))).
Proof.
  intros Safe NF. destruct (Nat.eq_dec x y) as [E|E].
  - subst y. rewrite nd_subst_self. apply aug_logical,logical_identity.
  - set (q:=nd_subst x y p).
    assert (FreshY : ~occurs_free y (FNeg p)).
    { unfold occurs_free. cbn [fresh_support]. apply nd_free_not_occurs. exact NF. }
    assert (Gen : AugProvable (FImp (FNeg p) (FAll y (FNeg p))) ) by (now apply aug_fresh_C5).
    assert (Sub : AugProvable (FImp (FEqual x y) (FImp (FNeg q) (FNeg p)))).
    { unfold q. pose proof (aug_equality_substitution_safe x y (FNeg p) Safe) as H.
      cbn [nd_subst] in H. exact (proj2 H). }
    assert (Point : AugProvable (FImp (FNeg q) (FImp (FEqual y x) (FAll y (FNeg p))))).
    { apply ac_finish,ac_deduction,ac_deduction.
      eapply ac_mp with (p:=FNeg p); [apply ac_theorem; exact Gen|].
      eapply ac_with_antecedent; [exact Sub| |apply ac_hyp; cbn; auto].
      eapply ac_mp; [apply ac_theorem,aug_equality_sym|apply ac_hyp; cbn; auto]. }
    assert (First : AugProvable (FImp (FAll y (FNeg q)) (FNeg p))).
    { eapply (aug_syllogism (FAll y (FNeg q))
        (FAll y (FImp (FEqual y x) (FAll y (FNeg p)))) (FNeg p)).
      - now apply aug_all_monotone.
      - apply aug_logical,logical_b10. }
    apply aug_fresh_generalization; [|exact First].
    unfold occurs_free. cbn [fresh_support].
    assert (XY : (x =? y)=false) by (now apply Nat.eqb_neq).
    rewrite XY. change (~occurs_free x q). unfold q. now apply nd_subst_fresh.
Qed.
Print Assumptions aug_quantifier_alpha_safe.
Theorem aug_all_alpha_reverse x y p : nd_not_bound y p=true -> nd_free y p=false ->
  AugProvable (FImp (FAll y (nd_subst x y p)) (FAll x p)).
Proof.
  intros NB NF. set (q:=nd_subst x y p).
  assert (Forward : AugProvable (FImp (FAll y q) (FAll y (FNeg (FNeg q))))).
  { apply aug_all_monotone,aug_inst_double_neg_intro. }
  assert (Middle : AugProvable (FImp (FAll y (FNeg (FNeg q))) (FAll x (FNeg (FNeg p))))).
  { unfold q. change (AugProvable (FImp (FAll y (FNeg (nd_subst x y (FNeg p))))
        (FAll x (FNeg (FNeg p))))).
    apply aug_quantifier_alpha_safe; [cbn [safe_subst]; now apply nd_not_bound_implies_safe|exact NF]. }
  assert (Back : AugProvable (FImp (FAll x (FNeg (FNeg p))) (FAll x p))).
  { apply aug_all_monotone,aug_inst_double_neg_elim. }
  eapply (aug_syllogism (FAll y q) (FAll y (FNeg (FNeg q))) (FAll x p)); [exact Forward|].
  eapply aug_syllogism; eassumption.
Qed.
Print Assumptions aug_all_alpha_reverse.
