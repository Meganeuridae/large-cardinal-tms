(** Capture-avoiding quantifier rules for the separate guarded-D calculus. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
From Berkeley Require Import Syntax TheorySchemas ProofFormula ProofPresentation LogicBridge LogicQuantifier LogicFresh
  TheoryIrreflexiveND AugmentedLogic AugmentedContext.
Import ListNotations.
Definition AugAllDistinctors := forall x y, x<>y -> AugProvable (distinctor x y).

Lemma aug_inst_all_distinctors : AugAllDistinctors.
Proof. intros x y E. now apply aug_distinctor. Qed.
Lemma aug_fresh_C5_compat x p : AugAllDistinctors -> ~occurs_free x p -> AugProvable (FImp p (FAll x p)).
Proof. intros _ H. now apply aug_fresh_C5. Qed.
Lemma aug_fresh_generalization_compat x p q : AugAllDistinctors -> ~occurs_free x p ->
  AugProvable (FImp p q) -> AugProvable (FImp p (FAll x q)).
Proof. intros _ H P. now apply aug_fresh_generalization. Qed.

Lemma aug_inst_contraposition p q : AugProvable (FImp p q) ->
  AugProvable (FImp (FNeg q) (FNeg p)).
Proof.
  intro H. apply ac_finish,ac_deduction,ac_neg_intro.
  eapply ac_explosion with (p:=q).
  - eapply ac_mp with (p:=p); [apply ac_theorem; exact H|apply ac_hyp; cbn; auto].
  - apply ac_hyp. cbn. auto.
Qed.
Lemma aug_inst_double_neg_elim p : AugProvable (FImp (FNeg (FNeg p)) p).
Proof. apply ac_finish,ac_deduction,ac_double_neg_elim,ac_hyp. cbn; auto. Qed.
Lemma aug_inst_double_neg_intro p : AugProvable (FImp p (FNeg (FNeg p))).
Proof. apply ac_finish,ac_deduction,ac_double_neg_intro,ac_hyp. cbn; auto. Qed.

Theorem aug_inst_exists_elim x p q : AugAllDistinctors -> ~occurs_free x q ->
  AugProvable (FImp p q) -> AugProvable (FImp (nd_ex x p) q).
Proof.
  intros Dist Fresh H.
  assert (A : AugProvable (FImp (FNeg q) (FNeg p))) by (now apply aug_inst_contraposition).
  assert (B : AugProvable (FImp (FNeg q) (FAll x (FNeg p)))).
  { apply aug_fresh_generalization_compat; [apply Dist| |exact A].
    unfold occurs_free in *. cbn [fresh_support]. exact Fresh. }
  assert (C : AugProvable (FImp (FNeg (FAll x (FNeg p))) (FNeg (FNeg q))))
    by (now apply aug_inst_contraposition).
  unfold nd_ex. eapply aug_syllogism; [exact C|apply aug_inst_double_neg_elim].
Qed.
Theorem aug_inst_equality_reflexive : AugAllDistinctors -> forall x, AugProvable (FEqual x x).
Proof.
  intros Dist x. set (w:=S x).
  assert (H : AugProvable (FImp (FEqual w x) (FEqual x x))).
  { apply ac_finish,ac_deduction. eapply ac_mp.
    - eapply ac_mp; [apply ac_logical,logical_b8|apply ac_hyp; now left].
    - apply ac_hyp. now left. }
  eapply aug_mp.
  - eapply (aug_inst_exists_elim w (FEqual w x) (FEqual x x)); [exact Dist| |exact H].
    unfold occurs_free, w. cbn [fresh_support]. intros [E|[E|[]]]; lia.
  - apply aug_logical,logical_equality_exists.
Qed.
Theorem aug_inst_equality_sym x y : AugAllDistinctors ->
  AugProvable (FImp (FEqual x y) (FEqual y x)).
Proof.
  intro Dist. apply ac_finish,ac_deduction.
  eapply ac_mp.
  - eapply ac_mp; [apply ac_logical,logical_b8|apply ac_hyp; now left].
  - apply ac_theorem. now apply aug_inst_equality_reflexive.
Qed.
Print Assumptions aug_inst_contraposition.
Print Assumptions aug_inst_exists_elim.
Print Assumptions aug_inst_equality_reflexive.
Print Assumptions aug_inst_equality_sym.

Definition atom_of (b:bool) x y := if b then FMember x y else FEqual x y.
Definition subvar x y z := if Nat.eqb z x then y else z.
Lemma ac_atom_left Γ b x y z : AugContext Γ (FEqual x y) ->
  AugContext Γ (atom_of b x z) -> AugContext Γ (atom_of b y z).
Proof.
  intros E H. destruct b; cbn [atom_of] in *.
  - eapply ac_mp; [eapply ac_mp; [apply ac_logical,logical_b12|exact E]|exact H].
  - eapply ac_mp; [eapply ac_mp; [apply ac_logical,logical_b8|exact E]|exact H].
Qed.
Lemma ac_atom_right Γ b x y z : AugContext Γ (FEqual x y) ->
  AugContext Γ (atom_of b z x) -> AugContext Γ (atom_of b z y).
Proof.
  intros E H. destruct b; cbn [atom_of] in *.
  - eapply ac_mp; [eapply ac_mp; [apply ac_logical,logical_b13|exact E]|exact H].
  - eapply ac_mp; [eapply ac_mp; [apply ac_logical,logical_equality_right|exact E]|exact H].
Qed.
Lemma ac_atom_substitute Γ b x y a c :
  AugContext Γ (FEqual x y) -> AugContext Γ (atom_of b a c) ->
  AugContext Γ (atom_of b (subvar x y a) (subvar x y c)).
Proof.
  intros E H. assert (L : AugContext Γ (atom_of b (subvar x y a) c)).
  { unfold subvar. destruct (Nat.eqb a x) eqn:A.
    - apply Nat.eqb_eq in A. subst a. eapply ac_atom_left; eassumption.
    - exact H. }
  unfold subvar at 2. destruct (Nat.eqb c x) eqn:C.
  - apply Nat.eqb_eq in C. subst c. eapply ac_atom_right; eassumption.
  - exact L.
Qed.
Lemma ac_atom_unsubstitute Γ b x y a c : AugAllDistinctors ->
  AugContext Γ (FEqual x y) -> AugContext Γ (atom_of b (subvar x y a) (subvar x y c)) ->
  AugContext Γ (atom_of b a c).
Proof.
  intros Dist E H. assert (S : AugContext Γ (FEqual y x)).
  { eapply ac_mp; [apply ac_theorem,aug_inst_equality_sym,Dist|exact E]. }
  assert (L : AugContext Γ (atom_of b (subvar x y a) c)).
  { unfold subvar in H. destruct (Nat.eqb c x) eqn:C.
    - apply Nat.eqb_eq in C. subst c. eapply ac_atom_right; eassumption.
    - exact H. }
  unfold subvar in L. destruct (Nat.eqb a x) eqn:A.
  - apply Nat.eqb_eq in A. subst a. eapply ac_atom_left; eassumption.
  - exact L.
Qed.

Lemma ac_with_antecedent Γ e p q : AugProvable (FImp e (FImp p q)) ->
  AugContext Γ e -> AugContext Γ p -> AugContext Γ q.
Proof. intros H E P. eapply ac_mp with (p:=p); [eapply ac_mp with (p:=e); [apply ac_theorem; exact H|exact E]|exact P]. Qed.

Lemma aug_inst_neg_substitution e p q :
  AugProvable (FImp e (FImp p q)) -> AugProvable (FImp e (FImp q p)) ->
  AugProvable (FImp e (FImp (FNeg p) (FNeg q))) /\
  AugProvable (FImp e (FImp (FNeg q) (FNeg p))).
Proof.
  intros F B. split; apply ac_finish,ac_deduction,ac_deduction,ac_neg_intro.
  - eapply ac_explosion with (p:=p).
    + eapply ac_with_antecedent; [exact B|apply ac_hyp; cbn; auto|apply ac_hyp; cbn; auto].
    + apply ac_hyp. cbn. auto.
  - eapply ac_explosion with (p:=q).
    + eapply ac_with_antecedent; [exact F|apply ac_hyp; cbn; auto|apply ac_hyp; cbn; auto].
    + apply ac_hyp. cbn. auto.
Qed.
Lemma aug_inst_imp_substitution e p p' q q' :
  AugProvable (FImp e (FImp p p')) -> AugProvable (FImp e (FImp p' p)) ->
  AugProvable (FImp e (FImp q q')) -> AugProvable (FImp e (FImp q' q)) ->
  AugProvable (FImp e (FImp (FImp p q) (FImp p' q'))) /\
  AugProvable (FImp e (FImp (FImp p' q') (FImp p q))).
Proof.
  intros PF PB QF QB. split; apply ac_finish,ac_deduction,ac_deduction,ac_deduction.
  - eapply ac_with_antecedent; [exact QF|apply ac_hyp; cbn; auto|].
    eapply ac_mp; [apply ac_hyp; cbn; auto|].
    eapply ac_with_antecedent; [exact PB|apply ac_hyp; cbn; auto|apply ac_hyp; cbn; auto].
  - eapply ac_with_antecedent; [exact QB|apply ac_hyp; cbn; auto|].
    eapply ac_mp; [apply ac_hyp; cbn; auto|].
    eapply ac_with_antecedent; [exact PF|apply ac_hyp; cbn; auto|apply ac_hyp; cbn; auto].
Qed.
Lemma aug_inst_all_substitution x y z p q : AugAllDistinctors -> z<>x -> z<>y ->
  AugProvable (FImp (FEqual x y) (FImp p q)) ->
  AugProvable (FImp (FEqual x y) (FImp (FAll z p) (FAll z q))).
Proof.
  intros Dist X Y H. eapply (aug_syllogism (FEqual x y) (FAll z (FImp p q))
    (FImp (FAll z p) (FAll z q))).
  - apply aug_fresh_generalization_compat; [apply Dist| |exact H].
    unfold occurs_free. cbn [fresh_support]. intros [E|[E|[]]]; congruence.
  - apply aug_logical,logical_all_distribution.
Qed.
Theorem aug_inst_equality_substitution x y p : AugAllDistinctors -> nd_not_bound y p=true ->
  AugProvable (FImp (FEqual x y) (FImp p (nd_subst x y p))) /\
  AugProvable (FImp (FEqual x y) (FImp (nd_subst x y p) p)).
Proof.
  intros Dist. induction p as [a b|a b|p IH|p IH q JH|z p IH]; intro NB.
  - cbn [nd_subst]. change
      (AugProvable (FImp (FEqual x y) (FImp (atom_of false a b)
        (atom_of false (subvar x y a) (subvar x y b)))) /\
       AugProvable (FImp (FEqual x y) (FImp
        (atom_of false (subvar x y a) (subvar x y b)) (atom_of false a b)))).
    split; apply ac_finish,ac_deduction,ac_deduction.
    + eapply ac_atom_substitute; apply ac_hyp; cbn; auto.
    + eapply ac_atom_unsubstitute; [exact Dist|apply ac_hyp; cbn; auto|apply ac_hyp; cbn; auto].
  - cbn [nd_subst]. change
      (AugProvable (FImp (FEqual x y) (FImp (atom_of true a b)
        (atom_of true (subvar x y a) (subvar x y b)))) /\
       AugProvable (FImp (FEqual x y) (FImp
        (atom_of true (subvar x y a) (subvar x y b)) (atom_of true a b)))).
    split; apply ac_finish,ac_deduction,ac_deduction.
    + eapply ac_atom_substitute; apply ac_hyp; cbn; auto.
    + eapply ac_atom_unsubstitute; [exact Dist|apply ac_hyp; cbn; auto|apply ac_hyp; cbn; auto].
  - cbn [nd_not_bound] in NB. specialize (IH NB). cbn [nd_subst].
    now apply aug_inst_neg_substitution.
  - cbn [nd_not_bound] in NB. apply andb_true_iff in NB as [NP NQ].
    specialize (IH NP). specialize (JH NQ). cbn [nd_subst].
    now apply aug_inst_imp_substitution.
  - cbn [nd_not_bound] in NB. apply andb_true_iff in NB as [ZY NP].
    apply negb_true_iff, Nat.eqb_neq in ZY.
    cbn [nd_subst]. destruct (Nat.eqb z x) eqn:ZX.
    + split; apply aug_logical,logical_weakening,logical_identity.
    + apply Nat.eqb_neq in ZX. specialize (IH NP). split; eapply aug_inst_all_substitution; try eassumption; tauto.
Qed.
Print Assumptions aug_inst_equality_substitution.

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
Theorem aug_inst_all_instantiate x y p : AugAllDistinctors -> nd_not_bound y p=true ->
  AugProvable (FImp (FAll x p) (nd_subst x y p)).
Proof.
  intros Dist NB. destruct (Nat.eq_dec x y) as [E|E].
  - subst y. rewrite nd_subst_self. apply aug_logical,logical_b5.
  - set (q := nd_subst x y p).
    assert (Fresh : ~occurs_free x q) by (unfold q; now apply nd_subst_fresh).
    assert (Sub : AugProvable (FImp (FEqual x y) (FImp p q))).
    { unfold q. exact (proj1 (aug_inst_equality_substitution x y p Dist NB)). }
    assert (Gen : AugProvable (FImp q (FAll x q))).
    { apply aug_fresh_C5_compat; [apply Dist|exact Fresh]. }
    assert (Lift : AugProvable (FImp p (FImp (FEqual x y) (FAll x q)))).
    { apply ac_finish,ac_deduction,ac_deduction. eapply ac_mp.
      - apply ac_theorem. exact Gen.
      - eapply ac_with_antecedent; [exact Sub|apply ac_hyp; cbn; auto|apply ac_hyp; cbn; auto]. }
    eapply (aug_syllogism (FAll x p) (FAll x (FImp (FEqual x y) (FAll x q))) q).
    + now apply aug_all_monotone.
    + apply aug_logical,logical_b10.
Qed.
Print Assumptions aug_inst_all_instantiate.

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

Theorem aug_inst_quantifier_alpha x y p : AugAllDistinctors ->
  nd_not_bound y p=true -> nd_free y p=false ->
  AugProvable (FImp (FAll y (FNeg (nd_subst x y p))) (FAll x (FNeg p))).
Proof.
  intros Dist NB NF. destruct (Nat.eq_dec x y) as [E|E].
  - subst y. rewrite nd_subst_self. apply aug_logical,logical_identity.
  - set (q:=nd_subst x y p).
    assert (FreshY : ~occurs_free y (FNeg p)).
    { unfold occurs_free. cbn [fresh_support]. apply nd_free_not_occurs. exact NF. }
    assert (Gen : AugProvable (FImp (FNeg p) (FAll y (FNeg p)))).
    { apply aug_fresh_C5_compat; [apply Dist|exact FreshY]. }
    assert (Sub : AugProvable (FImp (FEqual x y) (FImp (FNeg q) (FNeg p)))).
    { unfold q. pose proof (aug_inst_equality_substitution x y (FNeg p) Dist NB) as H.
      cbn [nd_subst] in H. exact (proj2 H). }
    assert (Point : AugProvable
      (FImp (FNeg q) (FImp (FEqual y x) (FAll y (FNeg p))))).
    { apply ac_finish,ac_deduction,ac_deduction.
      eapply ac_mp with (p:=FNeg p); [apply ac_theorem;exact Gen|].
      eapply ac_with_antecedent; [exact Sub| |apply ac_hyp; cbn; auto].
      eapply ac_mp; [apply ac_theorem,aug_inst_equality_sym,Dist|apply ac_hyp; cbn; auto]. }
    assert (First : AugProvable (FImp (FAll y (FNeg q)) (FNeg p))).
    { eapply (aug_syllogism (FAll y (FNeg q))
        (FAll y (FImp (FEqual y x) (FAll y (FNeg p)))) (FNeg p)).
      - now apply aug_all_monotone.
      - apply aug_logical,logical_b10. }
    apply aug_fresh_generalization_compat; [apply Dist| |exact First].
    unfold occurs_free. cbn [fresh_support].
    assert (XY : (x =? y)=false) by (now apply Nat.eqb_neq).
    rewrite XY. change (~occurs_free x q). unfold q. now apply nd_subst_fresh.
Qed.
Print Assumptions aug_inst_quantifier_alpha.

Corollary aug_all_instantiate x y p : nd_not_bound y p=true ->
  AugProvable (FImp (FAll x p) (nd_subst x y p)).
Proof. apply aug_inst_all_instantiate,aug_inst_all_distinctors. Qed.
Corollary aug_quantifier_alpha x y p : nd_not_bound y p=true -> nd_free y p=false ->
  AugProvable (FImp (FAll y (FNeg (nd_subst x y p))) (FAll x (FNeg p))).
Proof. apply aug_inst_quantifier_alpha,aug_inst_all_distinctors. Qed.
Corollary aug_equality_reflexive x : AugProvable (FEqual x x).
Proof. apply aug_inst_equality_reflexive,aug_inst_all_distinctors. Qed.
Corollary aug_equality_sym x y : AugProvable (FImp (FEqual x y) (FEqual y x)).
Proof. apply aug_inst_equality_sym,aug_inst_all_distinctors. Qed.
Print Assumptions aug_all_instantiate.
Print Assumptions aug_quantifier_alpha.
Print Assumptions aug_equality_reflexive.
Print Assumptions aug_equality_sym.
