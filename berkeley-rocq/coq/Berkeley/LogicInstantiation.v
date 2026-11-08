(** Quantifier and equality rules derived from the checked Hilbert calculus.
    Distinctor provability remains an explicit hypothesis until discharged. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
From Berkeley Require Import Syntax TheorySchemas ProofFormula ProofPresentation LogicBridge LogicQuantifier LogicFresh
  TheoryIrreflexiveND TheoryIrreflexiveHilbert.
Import ListNotations.
Definition AllDistinctors := forall x y, x<>y -> PresentedProvable (distinctor x y).

Lemma presented_contraposition p q : PresentedProvable (FImp p q) ->
  PresentedProvable (FImp (FNeg q) (FNeg p)).
Proof.
  intro H. apply hc_finish,hc_deduction,hc_neg_intro.
  eapply hc_explosion with (p:=q).
  - eapply hc_mp with (p:=p); [apply hc_theorem; exact H|apply hc_hyp; cbn; auto].
  - apply hc_hyp. cbn. auto.
Qed.
Lemma presented_double_neg_elim p : PresentedProvable (FImp (FNeg (FNeg p)) p).
Proof. apply hc_finish,hc_deduction,hc_double_neg_elim,hc_hyp. cbn; auto. Qed.
Lemma presented_double_neg_intro p : PresentedProvable (FImp p (FNeg (FNeg p))).
Proof. apply hc_finish,hc_deduction,hc_double_neg_intro,hc_hyp. cbn; auto. Qed.

Theorem presented_exists_elim x p q : AllDistinctors -> ~occurs_free x q ->
  PresentedProvable (FImp p q) -> PresentedProvable (FImp (nd_ex x p) q).
Proof.
  intros Dist Fresh H.
  assert (A : PresentedProvable (FImp (FNeg q) (FNeg p))) by (now apply presented_contraposition).
  assert (B : PresentedProvable (FImp (FNeg q) (FAll x (FNeg p)))).
  { apply presented_fresh_generalization; [apply Dist| |exact A].
    unfold occurs_free in *. cbn [fresh_support]. exact Fresh. }
  assert (C : PresentedProvable (FImp (FNeg (FAll x (FNeg p))) (FNeg (FNeg q))))
    by (now apply presented_contraposition).
  unfold nd_ex. eapply presented_syllogism; [exact C|apply presented_double_neg_elim].
Qed.
Theorem presented_equality_reflexive : AllDistinctors -> forall x, PresentedProvable (FEqual x x).
Proof.
  intros Dist x. set (w:=S x).
  assert (H : PresentedProvable (FImp (FEqual w x) (FEqual x x))).
  { apply hc_finish,hc_deduction. eapply hc_mp.
    - eapply hc_mp; [apply hc_logical,logical_b8|apply hc_hyp; now left].
    - apply hc_hyp. now left. }
  eapply presented_mp.
  - eapply (presented_exists_elim w (FEqual w x) (FEqual x x)); [exact Dist| |exact H].
    unfold occurs_free, w. cbn [fresh_support]. intros [E|[E|[]]]; lia.
  - apply logical_embeds_in_presented,logical_equality_exists.
Qed.
Theorem presented_equality_sym x y : AllDistinctors ->
  PresentedProvable (FImp (FEqual x y) (FEqual y x)).
Proof.
  intro Dist. apply hc_finish,hc_deduction.
  eapply hc_mp.
  - eapply hc_mp; [apply hc_logical,logical_b8|apply hc_hyp; now left].
  - apply hc_theorem. now apply presented_equality_reflexive.
Qed.
Print Assumptions presented_contraposition.
Print Assumptions presented_exists_elim.
Print Assumptions presented_equality_reflexive.
Print Assumptions presented_equality_sym.

Definition atom_of (b:bool) x y := if b then FMember x y else FEqual x y.
Definition subvar x y z := if Nat.eqb z x then y else z.
Lemma hc_atom_left Γ b x y z : HContext Γ (FEqual x y) ->
  HContext Γ (atom_of b x z) -> HContext Γ (atom_of b y z).
Proof.
  intros E H. destruct b; cbn [atom_of] in *.
  - eapply hc_mp; [eapply hc_mp; [apply hc_logical,logical_b12|exact E]|exact H].
  - eapply hc_mp; [eapply hc_mp; [apply hc_logical,logical_b8|exact E]|exact H].
Qed.
Lemma hc_atom_right Γ b x y z : HContext Γ (FEqual x y) ->
  HContext Γ (atom_of b z x) -> HContext Γ (atom_of b z y).
Proof.
  intros E H. destruct b; cbn [atom_of] in *.
  - eapply hc_mp; [eapply hc_mp; [apply hc_logical,logical_b13|exact E]|exact H].
  - eapply hc_mp; [eapply hc_mp; [apply hc_logical,logical_equality_right|exact E]|exact H].
Qed.
Lemma hc_atom_substitute Γ b x y a c :
  HContext Γ (FEqual x y) -> HContext Γ (atom_of b a c) ->
  HContext Γ (atom_of b (subvar x y a) (subvar x y c)).
Proof.
  intros E H. assert (L : HContext Γ (atom_of b (subvar x y a) c)).
  { unfold subvar. destruct (Nat.eqb a x) eqn:A.
    - apply Nat.eqb_eq in A. subst a. eapply hc_atom_left; eassumption.
    - exact H. }
  unfold subvar at 2. destruct (Nat.eqb c x) eqn:C.
  - apply Nat.eqb_eq in C. subst c. eapply hc_atom_right; eassumption.
  - exact L.
Qed.
Lemma hc_atom_unsubstitute Γ b x y a c : AllDistinctors ->
  HContext Γ (FEqual x y) -> HContext Γ (atom_of b (subvar x y a) (subvar x y c)) ->
  HContext Γ (atom_of b a c).
Proof.
  intros Dist E H. assert (S : HContext Γ (FEqual y x)).
  { eapply hc_mp; [apply hc_theorem,presented_equality_sym,Dist|exact E]. }
  assert (L : HContext Γ (atom_of b (subvar x y a) c)).
  { unfold subvar in H. destruct (Nat.eqb c x) eqn:C.
    - apply Nat.eqb_eq in C. subst c. eapply hc_atom_right; eassumption.
    - exact H. }
  unfold subvar in L. destruct (Nat.eqb a x) eqn:A.
  - apply Nat.eqb_eq in A. subst a. eapply hc_atom_left; eassumption.
  - exact L.
Qed.

Lemma hc_with_antecedent Γ e p q : PresentedProvable (FImp e (FImp p q)) ->
  HContext Γ e -> HContext Γ p -> HContext Γ q.
Proof. intros H E P. eapply hc_mp with (p:=p); [eapply hc_mp with (p:=e); [apply hc_theorem; exact H|exact E]|exact P]. Qed.

Lemma presented_neg_substitution e p q :
  PresentedProvable (FImp e (FImp p q)) -> PresentedProvable (FImp e (FImp q p)) ->
  PresentedProvable (FImp e (FImp (FNeg p) (FNeg q))) /\
  PresentedProvable (FImp e (FImp (FNeg q) (FNeg p))).
Proof.
  intros F B. split; apply hc_finish,hc_deduction,hc_deduction,hc_neg_intro.
  - eapply hc_explosion with (p:=p).
    + eapply hc_with_antecedent; [exact B|apply hc_hyp; cbn; auto|apply hc_hyp; cbn; auto].
    + apply hc_hyp. cbn. auto.
  - eapply hc_explosion with (p:=q).
    + eapply hc_with_antecedent; [exact F|apply hc_hyp; cbn; auto|apply hc_hyp; cbn; auto].
    + apply hc_hyp. cbn. auto.
Qed.
Lemma presented_imp_substitution e p p' q q' :
  PresentedProvable (FImp e (FImp p p')) -> PresentedProvable (FImp e (FImp p' p)) ->
  PresentedProvable (FImp e (FImp q q')) -> PresentedProvable (FImp e (FImp q' q)) ->
  PresentedProvable (FImp e (FImp (FImp p q) (FImp p' q'))) /\
  PresentedProvable (FImp e (FImp (FImp p' q') (FImp p q))).
Proof.
  intros PF PB QF QB. split; apply hc_finish,hc_deduction,hc_deduction,hc_deduction.
  - eapply hc_with_antecedent; [exact QF|apply hc_hyp; cbn; auto|].
    eapply hc_mp; [apply hc_hyp; cbn; auto|].
    eapply hc_with_antecedent; [exact PB|apply hc_hyp; cbn; auto|apply hc_hyp; cbn; auto].
  - eapply hc_with_antecedent; [exact QB|apply hc_hyp; cbn; auto|].
    eapply hc_mp; [apply hc_hyp; cbn; auto|].
    eapply hc_with_antecedent; [exact PF|apply hc_hyp; cbn; auto|apply hc_hyp; cbn; auto].
Qed.
Lemma presented_all_substitution x y z p q : AllDistinctors -> z<>x -> z<>y ->
  PresentedProvable (FImp (FEqual x y) (FImp p q)) ->
  PresentedProvable (FImp (FEqual x y) (FImp (FAll z p) (FAll z q))).
Proof.
  intros Dist X Y H. eapply (presented_syllogism (FEqual x y) (FAll z (FImp p q))
    (FImp (FAll z p) (FAll z q))).
  - apply presented_fresh_generalization; [apply Dist| |exact H].
    unfold occurs_free. cbn [fresh_support]. intros [E|[E|[]]]; congruence.
  - apply logical_embeds_in_presented,logical_all_distribution.
Qed.
Theorem presented_equality_substitution x y p : AllDistinctors -> nd_not_bound y p=true ->
  PresentedProvable (FImp (FEqual x y) (FImp p (nd_subst x y p))) /\
  PresentedProvable (FImp (FEqual x y) (FImp (nd_subst x y p) p)).
Proof.
  intros Dist. induction p as [a b|a b|p IH|p IH q JH|z p IH]; intro NB.
  - cbn [nd_subst]. change
      (PresentedProvable (FImp (FEqual x y) (FImp (atom_of false a b)
        (atom_of false (subvar x y a) (subvar x y b)))) /\
       PresentedProvable (FImp (FEqual x y) (FImp
        (atom_of false (subvar x y a) (subvar x y b)) (atom_of false a b)))).
    split; apply hc_finish,hc_deduction,hc_deduction.
    + eapply hc_atom_substitute; apply hc_hyp; cbn; auto.
    + eapply hc_atom_unsubstitute; [exact Dist|apply hc_hyp; cbn; auto|apply hc_hyp; cbn; auto].
  - cbn [nd_subst]. change
      (PresentedProvable (FImp (FEqual x y) (FImp (atom_of true a b)
        (atom_of true (subvar x y a) (subvar x y b)))) /\
       PresentedProvable (FImp (FEqual x y) (FImp
        (atom_of true (subvar x y a) (subvar x y b)) (atom_of true a b)))).
    split; apply hc_finish,hc_deduction,hc_deduction.
    + eapply hc_atom_substitute; apply hc_hyp; cbn; auto.
    + eapply hc_atom_unsubstitute; [exact Dist|apply hc_hyp; cbn; auto|apply hc_hyp; cbn; auto].
  - cbn [nd_not_bound] in NB. specialize (IH NB). cbn [nd_subst].
    now apply presented_neg_substitution.
  - cbn [nd_not_bound] in NB. apply andb_true_iff in NB as [NP NQ].
    specialize (IH NP). specialize (JH NQ). cbn [nd_subst].
    now apply presented_imp_substitution.
  - cbn [nd_not_bound] in NB. apply andb_true_iff in NB as [ZY NP].
    apply negb_true_iff, Nat.eqb_neq in ZY.
    cbn [nd_subst]. destruct (Nat.eqb z x) eqn:ZX.
    + split; apply logical_embeds_in_presented,logical_weakening,logical_identity.
    + apply Nat.eqb_neq in ZX. specialize (IH NP). split; eapply presented_all_substitution; try eassumption; tauto.
Qed.
Print Assumptions presented_equality_substitution.

Lemma subvar_self x a : subvar x x a=a.
Proof. unfold subvar. destruct (Nat.eqb a x) eqn:E; [apply Nat.eqb_eq in E; now subst|reflexivity]. Qed.
Lemma nd_subst_self x p : nd_subst x x p=p.
Proof.
  induction p as [a b|a b|p IH|p IH q JH|z p IH]; cbn [nd_subst].
  - change (FEqual (subvar x x a) (subvar x x b)=FEqual a b). now rewrite !subvar_self.
  - change (FMember (subvar x x a) (subvar x x b)=FMember a b). now rewrite !subvar_self.
  - now rewrite IH.
  - now rewrite IH,JH.
  - destruct (Nat.eqb z x); auto. now rewrite IH.
Qed.
Lemma subvar_fresh x y a : x<>y -> subvar x y a<>x.
Proof.
  intro N. unfold subvar. destruct (Nat.eqb a x) eqn:E; [congruence|].
  apply Nat.eqb_neq in E. congruence.
Qed.
Lemma nd_subst_fresh x y p : x<>y -> ~occurs_free x (nd_subst x y p).
Proof.
  intro XY. unfold occurs_free. induction p as [a b|a b|p IH|p IH q JH|z p IH]; cbn [nd_subst fresh_support].
  - change (~In x [subvar x y a;subvar x y b]).
    intros [E|[E|[]]]; [apply (subvar_fresh x y a XY)|apply (subvar_fresh x y b XY)]; congruence.
  - change (~In x [subvar x y a;subvar x y b]).
    intros [E|[E|[]]]; [apply (subvar_fresh x y a XY)|apply (subvar_fresh x y b XY)]; congruence.
  - exact IH.
  - rewrite in_app_iff. tauto.
  - destruct (Nat.eqb z x) eqn:Z.
    + apply Nat.eqb_eq in Z. subst z. cbn [fresh_support]. rewrite Nat.eqb_refl. tauto.
    + assert (X : (x =? z)=false) by (apply Nat.eqb_neq; apply Nat.eqb_neq in Z; congruence).
      cbn [fresh_support]. rewrite X. exact IH.
Qed.
Lemma logical_b10 x y p : LogicalProvable
  (FImp (FAll x (FImp (FEqual x y) (FAll x p))) p).
Proof.
  change (LogicalProvable (independent_instance (logic_vars x y 0) (fun _=>p)
    (nth 9 logical_schemas (Hole 0)))).
  eapply logical_axiom with (i:=9). reflexivity.
Qed.
Theorem presented_all_instantiate x y p : AllDistinctors -> nd_not_bound y p=true ->
  PresentedProvable (FImp (FAll x p) (nd_subst x y p)).
Proof.
  intros Dist NB. destruct (Nat.eq_dec x y) as [E|E].
  - subst y. rewrite nd_subst_self. apply logical_embeds_in_presented,logical_b5.
  - set (q := nd_subst x y p).
    assert (Fresh : ~occurs_free x q) by (unfold q; now apply nd_subst_fresh).
    assert (Sub : PresentedProvable (FImp (FEqual x y) (FImp p q))).
    { unfold q. exact (proj1 (presented_equality_substitution x y p Dist NB)). }
    assert (Gen : PresentedProvable (FImp q (FAll x q))).
    { apply presented_fresh_C5; [apply Dist|exact Fresh]. }
    assert (Lift : PresentedProvable (FImp p (FImp (FEqual x y) (FAll x q)))).
    { apply hc_finish,hc_deduction,hc_deduction. eapply hc_mp.
      - apply hc_theorem. exact Gen.
      - eapply hc_with_antecedent; [exact Sub|apply hc_hyp; cbn; auto|apply hc_hyp; cbn; auto]. }
    eapply (presented_syllogism (FAll x p) (FAll x (FImp (FEqual x y) (FAll x q))) q).
    + now apply presented_all_monotone.
    + apply logical_embeds_in_presented,logical_b10.
Qed.
Print Assumptions presented_all_instantiate.

Lemma nd_free_support x p : nd_free x p=true <-> occurs_free x p.
Proof.
  unfold occurs_free. induction p as [a b|a b|p IH|p IH q JH|z p IH]; cbn [nd_free fresh_support].
  - rewrite orb_true_iff,!Nat.eqb_eq. cbn [In]. intuition congruence.
  - rewrite orb_true_iff,!Nat.eqb_eq. cbn [In]. intuition congruence.
  - exact IH.
  - rewrite orb_true_iff,in_app_iff,IH,JH. tauto.
  - destruct (Nat.eqb x z); cbn [In]; [split; [discriminate|contradiction]|exact IH].
Qed.
Lemma nd_free_not_occurs x p : nd_free x p=false -> ~occurs_free x p.
Proof. intros N O. apply nd_free_support in O. congruence. Qed.

Theorem presented_quantifier_alpha x y p : AllDistinctors ->
  nd_not_bound y p=true -> nd_free y p=false ->
  PresentedProvable (FImp (FAll y (FNeg (nd_subst x y p))) (FAll x (FNeg p))).
Proof.
  intros Dist NB NF. destruct (Nat.eq_dec x y) as [E|E].
  - subst y. rewrite nd_subst_self. apply logical_embeds_in_presented,logical_identity.
  - set (q:=nd_subst x y p).
    assert (FreshY : ~occurs_free y (FNeg p)).
    { unfold occurs_free. cbn [fresh_support]. apply nd_free_not_occurs. exact NF. }
    assert (Gen : PresentedProvable (FImp (FNeg p) (FAll y (FNeg p)))).
    { apply presented_fresh_C5; [apply Dist|exact FreshY]. }
    assert (Sub : PresentedProvable (FImp (FEqual x y) (FImp (FNeg q) (FNeg p)))).
    { unfold q. pose proof (presented_equality_substitution x y (FNeg p) Dist NB) as H.
      cbn [nd_subst] in H. exact (proj2 H). }
    assert (Point : PresentedProvable
      (FImp (FNeg q) (FImp (FEqual y x) (FAll y (FNeg p))))).
    { apply hc_finish,hc_deduction,hc_deduction.
      eapply hc_mp with (p:=FNeg p); [apply hc_theorem;exact Gen|].
      eapply hc_with_antecedent; [exact Sub| |apply hc_hyp; cbn; auto].
      eapply hc_mp; [apply hc_theorem,presented_equality_sym,Dist|apply hc_hyp; cbn; auto]. }
    assert (First : PresentedProvable (FImp (FAll y (FNeg q)) (FNeg p))).
    { eapply (presented_syllogism (FAll y (FNeg q))
        (FAll y (FImp (FEqual y x) (FAll y (FNeg p)))) (FNeg p)).
      - now apply presented_all_monotone.
      - apply logical_embeds_in_presented,logical_b10. }
    apply presented_fresh_generalization; [apply Dist| |exact First].
    unfold occurs_free. cbn [fresh_support].
    assert (XY : (x =? y)=false) by (now apply Nat.eqb_neq).
    rewrite XY. change (~occurs_free x q). unfold q. now apply nd_subst_fresh.
Qed.
Print Assumptions presented_quantifier_alpha.
