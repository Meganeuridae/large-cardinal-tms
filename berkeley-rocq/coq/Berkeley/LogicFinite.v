(** Quantifier rules restricted to finite variables and explicit finite
    distinctor hypotheses. No global distinction assumption is made. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
From Berkeley Require Import ProofFormula ProofPresentation LogicBridge LogicQuantifier LogicFresh
  TheoryIrreflexiveND TheoryIrreflexiveHilbert TheoryIrreflexiveObstruction LogicInstantiation.
Import ListNotations.

Definition BoundedDistinctors n := forall x y, x<n -> y<n -> x<>y -> PresentedProvable (distinctor x y).
Fixpoint vars_below n f : Prop :=
  match f with
  | FEqual x y | FMember x y => x<n /\ y<n
  | FNeg p => vars_below n p
  | FImp p q => vars_below n p /\ vars_below n q
  | FAll x p => x<n /\ vars_below n p
  end.
Lemma support_below n x p v : vars_below n p -> In v (fresh_support x p) -> v<n.
Proof.
  induction p as [a b|a b|p IH|p IH q JH|z p IH]; cbn [vars_below fresh_support].
  - intros [A B] [E|[E|[]]]; subst; assumption.
  - intros [A B] [E|[E|[]]]; subst; assumption.
  - apply IH.
  - intros [A B] V. apply in_app_iff in V as [V|V]; [eapply IH|eapply JH]; eassumption.
  - intros [_ B]. destruct (Nat.eqb x z); cbn [In]; [contradiction|now apply IH].
Qed.
Lemma bounded_fresh_generalization n x p q : BoundedDistinctors n -> x<n -> vars_below n p ->
  ~occurs_free x p -> PresentedProvable (FImp p q) -> PresentedProvable (FImp p (FAll x q)).
Proof.
  intros Dist X Bound Fresh H. apply presented_fresh_generalization_with_support; [|exact H].
  intros v V. apply Dist; [exact X|eapply support_below; eassumption|].
  intro E. subst v. apply Fresh. exact V.
Qed.
Lemma bounded_fresh_C5 n x p : BoundedDistinctors n -> x<n -> vars_below n p ->
  ~occurs_free x p -> PresentedProvable (FImp p (FAll x p)).
Proof.
  intros Dist X B F. apply presented_fresh_from_distinctors. intros v V.
  apply Dist; [exact X|eapply support_below; eassumption|]. intro E. subst. now apply F.
Qed.
Lemma bounded_subvar n x y a : y<n -> a<n -> subvar x y a<n.
Proof. intros Y A. unfold subvar. now destruct (Nat.eqb a x). Qed.
Lemma bounded_nd_subst n x y p : y<n -> vars_below n p -> vars_below n (nd_subst x y p).
Proof.
  intro Y. induction p as [a b|a b|p IH|p IH q JH|z p IH]; cbn [vars_below nd_subst].
  - intros [A B]. split; apply bounded_subvar; assumption.
  - intros [A B]. split; apply bounded_subvar; assumption.
  - apply IH.
  - intros [P Q]. split; auto.
  - intros [Z P]. destruct (Nat.eqb z x); cbn [vars_below]; split; auto.
Qed.
Lemma presented_equality_sym_unconditional x y :
  PresentedProvable (FImp (FEqual x y) (FEqual y x)).
Proof.
  apply hc_finish,hc_deduction. eapply hc_mp.
  - eapply hc_mp; [apply hc_logical,logical_b8|apply hc_hyp; now left].
  - apply hc_theorem,presented_equality_reflexive_unconditional.
Qed.
Lemma hc_atom_unsubstitute_unconditional Γ b x y a c :
  HContext Γ (FEqual x y) -> HContext Γ (atom_of b (subvar x y a) (subvar x y c)) ->
  HContext Γ (atom_of b a c).
Proof.
  intros E H. assert (S : HContext Γ (FEqual y x)).
  { eapply hc_mp; [apply hc_theorem,presented_equality_sym_unconditional|exact E]. }
  assert (L : HContext Γ (atom_of b (subvar x y a) c)).
  { unfold subvar in H. destruct (Nat.eqb c x) eqn:C.
    - apply Nat.eqb_eq in C. subst c. eapply hc_atom_right; eassumption.
    - exact H. }
  unfold subvar in L. destruct (Nat.eqb a x) eqn:A.
  - apply Nat.eqb_eq in A. subst a. eapply hc_atom_left; eassumption.
  - exact L.
Qed.
Lemma bounded_all_substitution n x y z p q : BoundedDistinctors n -> x<n -> y<n -> z<n -> z<>x -> z<>y ->
  PresentedProvable (FImp (FEqual x y) (FImp p q)) ->
  PresentedProvable (FImp (FEqual x y) (FImp (FAll z p) (FAll z q))).
Proof.
  intros Dist X Y Z ZX ZY H. eapply (presented_syllogism (FEqual x y) (FAll z (FImp p q))
    (FImp (FAll z p) (FAll z q))).
  - apply (bounded_fresh_generalization n); try assumption.
    + cbn [vars_below]. auto.
    + unfold occurs_free. cbn [fresh_support In]. intros [E|[E|[]]]; congruence.
  - apply logical_embeds_in_presented,logical_all_distribution.
Qed.
Print Assumptions bounded_fresh_C5.
Print Assumptions bounded_nd_subst.
Print Assumptions presented_equality_sym_unconditional.
Print Assumptions bounded_all_substitution.
Theorem bounded_equality_substitution n x y p : BoundedDistinctors n -> x<n -> y<n ->
  vars_below n p -> nd_not_bound y p=true ->
  PresentedProvable (FImp (FEqual x y) (FImp p (nd_subst x y p))) /\
  PresentedProvable (FImp (FEqual x y) (FImp (nd_subst x y p) p)).
Proof.
  intros Dist X Y. induction p as [a b|a b|p IH|p IH q JH|z p IH]; intros B NB.
  - cbn [nd_subst]. change
      (PresentedProvable (FImp (FEqual x y) (FImp (atom_of false a b)
        (atom_of false (subvar x y a) (subvar x y b)))) /\
       PresentedProvable (FImp (FEqual x y) (FImp
        (atom_of false (subvar x y a) (subvar x y b)) (atom_of false a b)))).
    split; apply hc_finish,hc_deduction,hc_deduction.
    + eapply hc_atom_substitute; apply hc_hyp; cbn; auto.
    + eapply hc_atom_unsubstitute_unconditional; apply hc_hyp; cbn; auto.
  - cbn [nd_subst]. change
      (PresentedProvable (FImp (FEqual x y) (FImp (atom_of true a b)
        (atom_of true (subvar x y a) (subvar x y b)))) /\
       PresentedProvable (FImp (FEqual x y) (FImp
        (atom_of true (subvar x y a) (subvar x y b)) (atom_of true a b)))).
    split; apply hc_finish,hc_deduction,hc_deduction.
    + eapply hc_atom_substitute; apply hc_hyp; cbn; auto.
    + eapply hc_atom_unsubstitute_unconditional; apply hc_hyp; cbn; auto.
  - cbn [nd_not_bound] in NB. specialize (IH B NB). cbn [nd_subst]. now apply presented_neg_substitution.
  - cbn [vars_below] in B. destruct B as [BP BQ].
    cbn [nd_not_bound] in NB. apply andb_true_iff in NB as [NP NQ].
    specialize (IH BP NP). specialize (JH BQ NQ). cbn [nd_subst]. now apply presented_imp_substitution.
  - cbn [vars_below] in B. destruct B as [Z BP].
    cbn [nd_not_bound] in NB. apply andb_true_iff in NB as [ZY NP]. apply negb_true_iff, Nat.eqb_neq in ZY.
    cbn [nd_subst]. destruct (Nat.eqb z x) eqn:ZX.
    + split; apply logical_embeds_in_presented,logical_weakening,logical_identity.
    + apply Nat.eqb_neq in ZX. specialize (IH BP NP). split;
        eapply bounded_all_substitution; try eassumption; tauto.
Qed.
Theorem bounded_all_instantiate n x y p : BoundedDistinctors n -> x<n -> y<n ->
  vars_below n p -> nd_not_bound y p=true ->
  PresentedProvable (FImp (FAll x p) (nd_subst x y p)).
Proof.
  intros Dist X Y Bound NB. destruct (Nat.eq_dec x y) as [E|E].
  - subst y. rewrite nd_subst_self. apply logical_embeds_in_presented,logical_b5.
  - set (q := nd_subst x y p).
    assert (Fresh : ~occurs_free x q) by (unfold q; now apply nd_subst_fresh).
    assert (BQ : vars_below n q) by (unfold q; now apply bounded_nd_subst).
    assert (Sub : PresentedProvable (FImp (FEqual x y) (FImp p q))).
    { unfold q. exact (proj1 (bounded_equality_substitution n x y p Dist X Y Bound NB)). }
    assert (Gen : PresentedProvable (FImp q (FAll x q))).
    { eapply bounded_fresh_C5; eassumption. }
    assert (Lift : PresentedProvable (FImp p (FImp (FEqual x y) (FAll x q)))).
    { apply hc_finish,hc_deduction,hc_deduction. eapply hc_mp.
      - apply hc_theorem. exact Gen.
      - eapply hc_with_antecedent; [exact Sub|apply hc_hyp; cbn; auto|apply hc_hyp; cbn; auto]. }
    eapply (presented_syllogism (FAll x p) (FAll x (FImp (FEqual x y) (FAll x q))) q).
    + now apply presented_all_monotone.
    + apply logical_embeds_in_presented,logical_b10.
Qed.
Print Assumptions bounded_equality_substitution.
Print Assumptions bounded_all_instantiate.
Theorem bounded_quantifier_alpha n x y p : BoundedDistinctors n -> x<n -> y<n -> vars_below n p ->
  nd_not_bound y p=true -> nd_free y p=false ->
  PresentedProvable (FImp (FAll y (FNeg (nd_subst x y p))) (FAll x (FNeg p))).
Proof.
  intros Dist X Y Bound NB NF. destruct (Nat.eq_dec x y) as [E|E].
  - subst y. rewrite nd_subst_self. apply logical_embeds_in_presented,logical_identity.
  - set (q:=nd_subst x y p).
    assert (BQ : vars_below n q) by (unfold q; now apply bounded_nd_subst).
    assert (FreshY : ~occurs_free y (FNeg p)).
    { unfold occurs_free. cbn [fresh_support]. apply nd_free_not_occurs. exact NF. }
    assert (Gen : PresentedProvable (FImp (FNeg p) (FAll y (FNeg p)))).
    { eapply bounded_fresh_C5; [exact Dist|exact Y|exact Bound|exact FreshY]. }
    assert (Sub : PresentedProvable (FImp (FEqual x y) (FImp (FNeg q) (FNeg p)))).
    { unfold q. pose proof (bounded_equality_substitution n x y (FNeg p) Dist X Y Bound NB) as H.
      cbn [nd_subst] in H. exact (proj2 H). }
    assert (Point : PresentedProvable
      (FImp (FNeg q) (FImp (FEqual y x) (FAll y (FNeg p))))).
    { apply hc_finish,hc_deduction,hc_deduction.
      eapply hc_mp with (p:=FNeg p); [apply hc_theorem; exact Gen|].
      eapply hc_with_antecedent; [exact Sub| |apply hc_hyp; cbn; auto].
      eapply hc_mp; [apply hc_theorem,presented_equality_sym_unconditional|apply hc_hyp; cbn; auto]. }
    assert (First : PresentedProvable (FImp (FAll y (FNeg q)) (FNeg p))).
    { eapply (presented_syllogism (FAll y (FNeg q))
        (FAll y (FImp (FEqual y x) (FAll y (FNeg p)))) (FNeg p)).
      - now apply presented_all_monotone.
      - apply logical_embeds_in_presented,logical_b10. }
    eapply (bounded_fresh_generalization n x); [exact Dist|exact X| | |exact First].
    + cbn [vars_below]. auto.
    + unfold occurs_free. cbn [fresh_support].
      assert (XY : (x =? y)=false) by (now apply Nat.eqb_neq).
      rewrite XY. change (~occurs_free x q). unfold q. now apply nd_subst_fresh.
Qed.
Print Assumptions bounded_quantifier_alpha.
