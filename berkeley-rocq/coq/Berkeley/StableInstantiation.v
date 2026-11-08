(** Derived quantifier and equality rules stable under injective renaming. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
From Berkeley Require Import Syntax TheorySchemas ProofFormula ProofPresentation LogicBridge LogicQuantifier LogicFresh
  TheoryIrreflexiveND StableLogic StableContext.
Import ListNotations.
Definition StableAllDistinctors := forall x y, x<>y -> RenameStable (distinctor x y).

Lemma stable_inst_all_distinctors : StableAllDistinctors.
Proof. intros x y E. now apply stable_distinctor. Qed.
Lemma stable_fresh_C5_compat x p : StableAllDistinctors -> ~occurs_free x p -> RenameStable (FImp p (FAll x p)).
Proof. intros _ H. now apply stable_fresh_C5. Qed.
Lemma stable_fresh_generalization_compat x p q : StableAllDistinctors -> ~occurs_free x p ->
  RenameStable (FImp p q) -> RenameStable (FImp p (FAll x q)).
Proof. intros _ H P. now apply stable_fresh_generalization. Qed.

Lemma stable_inst_contraposition p q : RenameStable (FImp p q) ->
  RenameStable (FImp (FNeg q) (FNeg p)).
Proof.
  intro H. apply sc_finish,sc_deduction,sc_neg_intro.
  eapply sc_explosion with (p:=q).
  - eapply sc_mp with (p:=p); [apply sc_theorem; exact H|apply sc_hyp; cbn; auto].
  - apply sc_hyp. cbn. auto.
Qed.
Lemma stable_inst_double_neg_elim p : RenameStable (FImp (FNeg (FNeg p)) p).
Proof. apply sc_finish,sc_deduction,sc_double_neg_elim,sc_hyp. cbn; auto. Qed.
Lemma stable_inst_double_neg_intro p : RenameStable (FImp p (FNeg (FNeg p))).
Proof. apply sc_finish,sc_deduction,sc_double_neg_intro,sc_hyp. cbn; auto. Qed.

Theorem stable_inst_exists_elim x p q : StableAllDistinctors -> ~occurs_free x q ->
  RenameStable (FImp p q) -> RenameStable (FImp (nd_ex x p) q).
Proof.
  intros Dist Fresh H.
  assert (A : RenameStable (FImp (FNeg q) (FNeg p))) by (now apply stable_inst_contraposition).
  assert (B : RenameStable (FImp (FNeg q) (FAll x (FNeg p)))).
  { apply stable_fresh_generalization_compat; [apply Dist| |exact A].
    unfold occurs_free in *. cbn [fresh_support]. exact Fresh. }
  assert (C : RenameStable (FImp (FNeg (FAll x (FNeg p))) (FNeg (FNeg q))))
    by (now apply stable_inst_contraposition).
  unfold nd_ex. eapply stable_syllogism; [exact C|apply stable_inst_double_neg_elim].
Qed.
Theorem stable_inst_equality_reflexive : StableAllDistinctors -> forall x, RenameStable (FEqual x x).
Proof.
  intros Dist x. set (w:=S x).
  assert (H : RenameStable (FImp (FEqual w x) (FEqual x x))).
  { apply sc_finish,sc_deduction. eapply sc_mp.
    - eapply sc_mp; [apply sc_logical,logical_b8|apply sc_hyp; now left].
    - apply sc_hyp. now left. }
  eapply stable_mp.
  - eapply (stable_inst_exists_elim w (FEqual w x) (FEqual x x)); [exact Dist| |exact H].
    unfold occurs_free, w. cbn [fresh_support]. intros [E|[E|[]]]; lia.
  - apply stable_logical,logical_equality_exists.
Qed.
Theorem stable_inst_equality_sym x y : StableAllDistinctors ->
  RenameStable (FImp (FEqual x y) (FEqual y x)).
Proof.
  intro Dist. apply sc_finish,sc_deduction.
  eapply sc_mp.
  - eapply sc_mp; [apply sc_logical,logical_b8|apply sc_hyp; now left].
  - apply sc_theorem. now apply stable_inst_equality_reflexive.
Qed.
Print Assumptions stable_inst_contraposition.
Print Assumptions stable_inst_exists_elim.
Print Assumptions stable_inst_equality_reflexive.
Print Assumptions stable_inst_equality_sym.

Definition atom_of (b:bool) x y := if b then FMember x y else FEqual x y.
Definition subvar x y z := if Nat.eqb z x then y else z.
Lemma sc_atom_left Γ b x y z : StableContext Γ (FEqual x y) ->
  StableContext Γ (atom_of b x z) -> StableContext Γ (atom_of b y z).
Proof.
  intros E H. destruct b; cbn [atom_of] in *.
  - eapply sc_mp; [eapply sc_mp; [apply sc_logical,logical_b12|exact E]|exact H].
  - eapply sc_mp; [eapply sc_mp; [apply sc_logical,logical_b8|exact E]|exact H].
Qed.
Lemma sc_atom_right Γ b x y z : StableContext Γ (FEqual x y) ->
  StableContext Γ (atom_of b z x) -> StableContext Γ (atom_of b z y).
Proof.
  intros E H. destruct b; cbn [atom_of] in *.
  - eapply sc_mp; [eapply sc_mp; [apply sc_logical,logical_b13|exact E]|exact H].
  - eapply sc_mp; [eapply sc_mp; [apply sc_logical,logical_equality_right|exact E]|exact H].
Qed.
Lemma sc_atom_substitute Γ b x y a c :
  StableContext Γ (FEqual x y) -> StableContext Γ (atom_of b a c) ->
  StableContext Γ (atom_of b (subvar x y a) (subvar x y c)).
Proof.
  intros E H. assert (L : StableContext Γ (atom_of b (subvar x y a) c)).
  { unfold subvar. destruct (Nat.eqb a x) eqn:A.
    - apply Nat.eqb_eq in A. subst a. eapply sc_atom_left; eassumption.
    - exact H. }
  unfold subvar at 2. destruct (Nat.eqb c x) eqn:C.
  - apply Nat.eqb_eq in C. subst c. eapply sc_atom_right; eassumption.
  - exact L.
Qed.
Lemma sc_atom_unsubstitute Γ b x y a c : StableAllDistinctors ->
  StableContext Γ (FEqual x y) -> StableContext Γ (atom_of b (subvar x y a) (subvar x y c)) ->
  StableContext Γ (atom_of b a c).
Proof.
  intros Dist E H. assert (S : StableContext Γ (FEqual y x)).
  { eapply sc_mp; [apply sc_theorem,stable_inst_equality_sym,Dist|exact E]. }
  assert (L : StableContext Γ (atom_of b (subvar x y a) c)).
  { unfold subvar in H. destruct (Nat.eqb c x) eqn:C.
    - apply Nat.eqb_eq in C. subst c. eapply sc_atom_right; eassumption.
    - exact H. }
  unfold subvar in L. destruct (Nat.eqb a x) eqn:A.
  - apply Nat.eqb_eq in A. subst a. eapply sc_atom_left; eassumption.
  - exact L.
Qed.

Lemma sc_with_antecedent Γ e p q : RenameStable (FImp e (FImp p q)) ->
  StableContext Γ e -> StableContext Γ p -> StableContext Γ q.
Proof. intros H E P. eapply sc_mp with (p:=p); [eapply sc_mp with (p:=e); [apply sc_theorem; exact H|exact E]|exact P]. Qed.

Lemma stable_inst_neg_substitution e p q :
  RenameStable (FImp e (FImp p q)) -> RenameStable (FImp e (FImp q p)) ->
  RenameStable (FImp e (FImp (FNeg p) (FNeg q))) /\
  RenameStable (FImp e (FImp (FNeg q) (FNeg p))).
Proof.
  intros F B. split; apply sc_finish,sc_deduction,sc_deduction,sc_neg_intro.
  - eapply sc_explosion with (p:=p).
    + eapply sc_with_antecedent; [exact B|apply sc_hyp; cbn; auto|apply sc_hyp; cbn; auto].
    + apply sc_hyp. cbn. auto.
  - eapply sc_explosion with (p:=q).
    + eapply sc_with_antecedent; [exact F|apply sc_hyp; cbn; auto|apply sc_hyp; cbn; auto].
    + apply sc_hyp. cbn. auto.
Qed.
Lemma stable_inst_imp_substitution e p p' q q' :
  RenameStable (FImp e (FImp p p')) -> RenameStable (FImp e (FImp p' p)) ->
  RenameStable (FImp e (FImp q q')) -> RenameStable (FImp e (FImp q' q)) ->
  RenameStable (FImp e (FImp (FImp p q) (FImp p' q'))) /\
  RenameStable (FImp e (FImp (FImp p' q') (FImp p q))).
Proof.
  intros PF PB QF QB. split; apply sc_finish,sc_deduction,sc_deduction,sc_deduction.
  - eapply sc_with_antecedent; [exact QF|apply sc_hyp; cbn; auto|].
    eapply sc_mp; [apply sc_hyp; cbn; auto|].
    eapply sc_with_antecedent; [exact PB|apply sc_hyp; cbn; auto|apply sc_hyp; cbn; auto].
  - eapply sc_with_antecedent; [exact QB|apply sc_hyp; cbn; auto|].
    eapply sc_mp; [apply sc_hyp; cbn; auto|].
    eapply sc_with_antecedent; [exact PF|apply sc_hyp; cbn; auto|apply sc_hyp; cbn; auto].
Qed.
Lemma stable_inst_all_substitution x y z p q : StableAllDistinctors -> z<>x -> z<>y ->
  RenameStable (FImp (FEqual x y) (FImp p q)) ->
  RenameStable (FImp (FEqual x y) (FImp (FAll z p) (FAll z q))).
Proof.
  intros Dist X Y H. eapply (stable_syllogism (FEqual x y) (FAll z (FImp p q))
    (FImp (FAll z p) (FAll z q))).
  - apply stable_fresh_generalization_compat; [apply Dist| |exact H].
    unfold occurs_free. cbn [fresh_support]. intros [E|[E|[]]]; congruence.
  - apply stable_logical,logical_all_distribution.
Qed.
Theorem stable_inst_equality_substitution x y p : StableAllDistinctors -> nd_not_bound y p=true ->
  RenameStable (FImp (FEqual x y) (FImp p (nd_subst x y p))) /\
  RenameStable (FImp (FEqual x y) (FImp (nd_subst x y p) p)).
Proof.
  intros Dist. induction p as [a b|a b|p IH|p IH q JH|z p IH]; intro NB.
  - cbn [nd_subst]. change
      (RenameStable (FImp (FEqual x y) (FImp (atom_of false a b)
        (atom_of false (subvar x y a) (subvar x y b)))) /\
       RenameStable (FImp (FEqual x y) (FImp
        (atom_of false (subvar x y a) (subvar x y b)) (atom_of false a b)))).
    split; apply sc_finish,sc_deduction,sc_deduction.
    + eapply sc_atom_substitute; apply sc_hyp; cbn; auto.
    + eapply sc_atom_unsubstitute; [exact Dist|apply sc_hyp; cbn; auto|apply sc_hyp; cbn; auto].
  - cbn [nd_subst]. change
      (RenameStable (FImp (FEqual x y) (FImp (atom_of true a b)
        (atom_of true (subvar x y a) (subvar x y b)))) /\
       RenameStable (FImp (FEqual x y) (FImp
        (atom_of true (subvar x y a) (subvar x y b)) (atom_of true a b)))).
    split; apply sc_finish,sc_deduction,sc_deduction.
    + eapply sc_atom_substitute; apply sc_hyp; cbn; auto.
    + eapply sc_atom_unsubstitute; [exact Dist|apply sc_hyp; cbn; auto|apply sc_hyp; cbn; auto].
  - cbn [nd_not_bound] in NB. specialize (IH NB). cbn [nd_subst].
    now apply stable_inst_neg_substitution.
  - cbn [nd_not_bound] in NB. apply andb_true_iff in NB as [NP NQ].
    specialize (IH NP). specialize (JH NQ). cbn [nd_subst].
    now apply stable_inst_imp_substitution.
  - cbn [nd_not_bound] in NB. apply andb_true_iff in NB as [ZY NP].
    apply negb_true_iff, Nat.eqb_neq in ZY.
    cbn [nd_subst]. destruct (Nat.eqb z x) eqn:ZX.
    + split; apply stable_logical,logical_weakening,logical_identity.
    + apply Nat.eqb_neq in ZX. specialize (IH NP). split; eapply stable_inst_all_substitution; try eassumption; tauto.
Qed.
Print Assumptions stable_inst_equality_substitution.

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
Theorem stable_inst_all_instantiate x y p : StableAllDistinctors -> nd_not_bound y p=true ->
  RenameStable (FImp (FAll x p) (nd_subst x y p)).
Proof.
  intros Dist NB. destruct (Nat.eq_dec x y) as [E|E].
  - subst y. rewrite nd_subst_self. apply stable_logical,logical_b5.
  - set (q := nd_subst x y p).
    assert (Fresh : ~occurs_free x q) by (unfold q; now apply nd_subst_fresh).
    assert (Sub : RenameStable (FImp (FEqual x y) (FImp p q))).
    { unfold q. exact (proj1 (stable_inst_equality_substitution x y p Dist NB)). }
    assert (Gen : RenameStable (FImp q (FAll x q))).
    { apply stable_fresh_C5_compat; [apply Dist|exact Fresh]. }
    assert (Lift : RenameStable (FImp p (FImp (FEqual x y) (FAll x q)))).
    { apply sc_finish,sc_deduction,sc_deduction. eapply sc_mp.
      - apply sc_theorem. exact Gen.
      - eapply sc_with_antecedent; [exact Sub|apply sc_hyp; cbn; auto|apply sc_hyp; cbn; auto]. }
    eapply (stable_syllogism (FAll x p) (FAll x (FImp (FEqual x y) (FAll x q))) q).
    + now apply stable_all_monotone.
    + apply stable_logical,logical_b10.
Qed.
Print Assumptions stable_inst_all_instantiate.

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

Theorem stable_inst_quantifier_alpha x y p : StableAllDistinctors ->
  nd_not_bound y p=true -> nd_free y p=false ->
  RenameStable (FImp (FAll y (FNeg (nd_subst x y p))) (FAll x (FNeg p))).
Proof.
  intros Dist NB NF. destruct (Nat.eq_dec x y) as [E|E].
  - subst y. rewrite nd_subst_self. apply stable_logical,logical_identity.
  - set (q:=nd_subst x y p).
    assert (FreshY : ~occurs_free y (FNeg p)).
    { unfold occurs_free. cbn [fresh_support]. apply nd_free_not_occurs. exact NF. }
    assert (Gen : RenameStable (FImp (FNeg p) (FAll y (FNeg p)))).
    { apply stable_fresh_C5_compat; [apply Dist|exact FreshY]. }
    assert (Sub : RenameStable (FImp (FEqual x y) (FImp (FNeg q) (FNeg p)))).
    { unfold q. pose proof (stable_inst_equality_substitution x y (FNeg p) Dist NB) as H.
      cbn [nd_subst] in H. exact (proj2 H). }
    assert (Point : RenameStable
      (FImp (FNeg q) (FImp (FEqual y x) (FAll y (FNeg p))))).
    { apply sc_finish,sc_deduction,sc_deduction.
      eapply sc_mp with (p:=FNeg p); [apply sc_theorem;exact Gen|].
      eapply sc_with_antecedent; [exact Sub| |apply sc_hyp; cbn; auto].
      eapply sc_mp; [apply sc_theorem,stable_inst_equality_sym,Dist|apply sc_hyp; cbn; auto]. }
    assert (First : RenameStable (FImp (FAll y (FNeg q)) (FNeg p))).
    { eapply (stable_syllogism (FAll y (FNeg q))
        (FAll y (FImp (FEqual y x) (FAll y (FNeg p)))) (FNeg p)).
      - now apply stable_all_monotone.
      - apply stable_logical,logical_b10. }
    apply stable_fresh_generalization_compat; [apply Dist| |exact First].
    unfold occurs_free. cbn [fresh_support].
    assert (XY : (x =? y)=false) by (now apply Nat.eqb_neq).
    rewrite XY. change (~occurs_free x q). unfold q. now apply nd_subst_fresh.
Qed.
Print Assumptions stable_inst_quantifier_alpha.

Corollary stable_all_instantiate x y p : nd_not_bound y p=true ->
  RenameStable (FImp (FAll x p) (nd_subst x y p)).
Proof. apply stable_inst_all_instantiate,stable_inst_all_distinctors. Qed.
Corollary stable_quantifier_alpha x y p : nd_not_bound y p=true -> nd_free y p=false ->
  RenameStable (FImp (FAll y (FNeg (nd_subst x y p))) (FAll x (FNeg p))).
Proof. apply stable_inst_quantifier_alpha,stable_inst_all_distinctors. Qed.
Corollary stable_equality_reflexive x : RenameStable (FEqual x x).
Proof. apply stable_inst_equality_reflexive,stable_inst_all_distinctors. Qed.
Corollary stable_equality_sym x y : RenameStable (FImp (FEqual x y) (FEqual y x)).
Proof. apply stable_inst_equality_sym,stable_inst_all_distinctors. Qed.
Print Assumptions stable_all_instantiate.
Print Assumptions stable_quantifier_alpha.
Print Assumptions stable_equality_reflexive.
Print Assumptions stable_equality_sym.
