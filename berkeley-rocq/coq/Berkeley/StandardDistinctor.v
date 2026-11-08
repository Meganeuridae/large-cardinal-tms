(** Derive the guarded distinction axiom in independent first-order ND from
    the literal Empty and Pairing source schemas. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
From Berkeley Require Import Syntax SyntaxData ProofFormula ProofPresentation LogicFresh TheoryIrreflexiveND
  AugmentedCapture StandardND StandardLogical.
Import ListNotations.
Definition standard_empty_body := FAll 1 (FNeg (FMember 1 0)).
Definition standard_singleton_body e := FAll 3 (nd_iff (FMember 3 2)
  (nd_or (FEqual 3 e) (FEqual 3 e))).
Definition standard_singleton e := nd_ex 2 (standard_singleton_body e).
Lemma std_empty_axiom Γ : StandardND Γ (nd_ex 0 standard_empty_body).
Proof.
  change (StandardND Γ (independent_instance (fun n=>n) (fun _=>FEqual 0 0)
    (nth 15 candidate_axioms (Hole 0)))).
  eapply std_nonlogical with (i:=15); [lia|reflexivity].
Qed.
Lemma std_pair_axiom Γ : StandardND Γ pair_axiom.
Proof.
  change (StandardND Γ (independent_instance (fun n=>n) (fun _=>FEqual 0 0)
    (nth 16 candidate_axioms (Hole 0)))).
  eapply std_nonlogical with (i:=16); [lia|reflexivity].
Qed.
Lemma std_pair_all : StandardND [] (FAll 0 (FAll 1 pair_axiom)).
Proof.
  do 2 (apply std_all_intro; [unfold nd_fresh; intros p []|]). apply std_pair_axiom.
Qed.
Lemma nd_not_bound_substitution x y z p : nd_not_bound z (nd_subst x y p)=nd_not_bound z p.
Proof.
  induction p as [a b|a b|p IH|p IH q JH|v p IH]; cbn [nd_not_bound nd_subst]; auto.
  - now rewrite IH,JH.
  - destruct (Nat.eqb v x); cbn [nd_not_bound]; [reflexivity|now rewrite IH].
Qed.
Lemma std_singleton_closed e : 3<e -> StandardND [] (standard_singleton e).
Proof.
  intro E.
  assert (B1 : (1=?e)=false) by (apply Nat.eqb_neq;lia).
  assert (B2 : (2=?e)=false) by (apply Nat.eqb_neq;lia).
  assert (B3 : (3=?e)=false) by (apply Nat.eqb_neq;lia).
  assert (E1 : (e=?1)=false) by (apply Nat.eqb_neq;lia).
  assert (F : StandardND [] (nd_subst 0 e (FAll 1 pair_axiom))).
  { eapply std_all_elim; [|apply std_pair_all].
    apply nd_not_bound_implies_safe. cbn [nd_not_bound pair_axiom nd_ex nd_iff nd_and nd_or].
    now rewrite B1,B2,B3. }
  change (StandardND [] (FAll 1 (nd_subst 0 e pair_axiom))) in F.
  assert (G : StandardND [] (nd_subst 1 e (nd_subst 0 e pair_axiom))).
  { eapply std_all_elim; [|exact F]. apply nd_not_bound_implies_safe.
    rewrite nd_not_bound_substitution. cbn [nd_not_bound pair_axiom nd_ex nd_iff nd_and nd_or].
    now rewrite B2,B3. }
  cbv [nd_subst pair_axiom standard_singleton standard_singleton_body nd_ex nd_iff nd_and nd_or Nat.eqb] in G |- *.
  cbv [Nat.eqb] in E1. now rewrite E1 in G.
Qed.
Definition standard_empty_at e := FAll 1 (FNeg (FMember 1 e)).
Definition standard_singleton_at e b := FAll 3 (nd_iff (FMember 3 b)
  (nd_or (FEqual 3 e) (FEqual 3 e))).
Lemma std_empty_self Γ e : 1<e -> StandardND Γ (standard_empty_at e) -> StandardND Γ (FNeg (FMember e e)).
Proof.
  intros E H. replace (FNeg (FMember e e)) with (nd_subst 1 e (FNeg (FMember 1 e))).
  - eapply std_all_elim; [reflexivity|exact H].
  - cbn [nd_subst]. rewrite Nat.eqb_refl. assert ((e=?1)=false) by (apply Nat.eqb_neq;lia). now rewrite H0.
Qed.
Lemma std_singleton_member Γ e b : 3<e -> 3<b -> StandardND Γ (standard_singleton_at e b) -> StandardND Γ (FMember e b).
Proof.
  intros E B H.
  assert (Info : StandardND Γ (nd_iff (FMember e b) (nd_or (FEqual e e) (FEqual e e)))).
  { replace (nd_iff (FMember e b) (nd_or (FEqual e e) (FEqual e e))) with
      (nd_subst 3 e (nd_iff (FMember 3 b) (nd_or (FEqual 3 e) (FEqual 3 e)))).
    - eapply std_all_elim; [reflexivity|exact H].
    - cbn [nd_subst nd_iff nd_and nd_or]. rewrite Nat.eqb_refl.
      assert ((e=?3)=false) by (apply Nat.eqb_neq;lia).
      assert ((b=?3)=false) by (apply Nat.eqb_neq;lia). now rewrite H0,H1. }
  unfold nd_iff in Info. eapply std_imp_elim.
  - eapply std_and_right. exact Info.
  - apply std_or_left,std_eq_refl.
Qed.
Lemma standard_singleton_subst e b : 2<e ->
  nd_subst 2 b (standard_singleton_body e) = standard_singleton_at e b.
Proof.
  intro E. assert (B : (e=?2)=false) by (apply Nat.eqb_neq;lia).
  cbv [standard_singleton_body standard_singleton_at nd_subst nd_iff nd_and nd_or Nat.eqb].
  cbv [Nat.eqb] in B. now rewrite B.
Qed.
Theorem std_distinctor x y : x<>y -> StandardND [] (distinctor x y).
Proof.
  intro XY. set (e := S (Nat.max (Nat.max x y) 3)). set (b:=S e).
  assert (Ex : x<e) by (unfold e; pose proof (Nat.le_max_l x y); pose proof (Nat.le_max_l (Nat.max x y) 3); lia).
  assert (Ey : y<e) by (unfold e; pose proof (Nat.le_max_r x y); pose proof (Nat.le_max_l (Nat.max x y) 3); lia).
  assert (E3 : 3<e) by (unfold e; pose proof (Nat.le_max_r (Nat.max x y) 3); lia).
  assert (Eb : e<b) by (unfold b;lia).
  set (A:=FAll x (FEqual x y)).
  change (StandardND [] (FNeg A)). apply std_neg_intro.
  eapply (std_ex_elim [A] 0 e standard_empty_body nd_false).
  - cbn [safe_subst standard_empty_body]. assert ((1=?e)=false) by (apply Nat.eqb_neq;lia). now rewrite H.
  - right. cbn [nd_free standard_empty_body].
    assert ((e=?1)=false) by (apply Nat.eqb_neq;lia).
    assert ((e=?0)=false) by (apply Nat.eqb_neq;lia). now rewrite H,H0.
  - unfold nd_fresh. intros f [E|[]]. subst f. unfold A. cbn [nd_free].
    assert ((e=?x)=false) by (apply Nat.eqb_neq;lia).
    assert ((e=?y)=false) by (apply Nat.eqb_neq;lia). now rewrite H,H0.
  - unfold nd_false,nd_true. cbn [nd_free]. assert ((e=?0)=false) by (apply Nat.eqb_neq;lia). now rewrite H.
  - apply std_empty_axiom.
  - change (StandardND [nd_subst 0 e standard_empty_body; A] nd_false).
    assert (EmptyBody : nd_subst 0 e standard_empty_body = standard_empty_at e) by reflexivity.
    rewrite EmptyBody.
    eapply (std_ex_elim [standard_empty_at e;A] 2 b (standard_singleton_body e) nd_false).
    + cbn [safe_subst standard_singleton_body nd_iff nd_and nd_or].
      assert ((3=?b)=false) by (apply Nat.eqb_neq;lia). now rewrite H.
    + right. cbn [nd_free standard_singleton_body nd_iff nd_and nd_or].
      assert ((b=?3)=false) by (apply Nat.eqb_neq;lia).
      assert ((b=?2)=false) by (apply Nat.eqb_neq;lia).
      assert ((b=?e)=false) by (apply Nat.eqb_neq;lia). now rewrite H,H0,H1.
    + unfold nd_fresh. intros f [E|[E|[]]]; subst f; unfold standard_empty_at,A; cbn [nd_free].
      * assert ((b=?1)=false) by (apply Nat.eqb_neq;lia).
        assert ((b=?e)=false) by (apply Nat.eqb_neq;lia). now rewrite H,H0.
      * assert ((b=?x)=false) by (apply Nat.eqb_neq;lia).
        assert ((b=?y)=false) by (apply Nat.eqb_neq;lia). now rewrite H,H0.
    + unfold nd_false,nd_true. cbn [nd_free]. assert ((b=?0)=false) by (apply Nat.eqb_neq;lia). now rewrite H.
    + apply std_closed,std_singleton_closed. exact E3.
    + rewrite standard_singleton_subst by lia.
      assert (Mem : StandardND [standard_singleton_at e b;standard_empty_at e;A] (FMember e b)).
      { eapply std_singleton_member; [lia|lia|apply std_hyp;now left]. }
      assert (Empty : StandardND [standard_singleton_at e b;standard_empty_at e;A] (FNeg (FMember e e))).
      { eapply std_empty_self; [lia|apply std_hyp;cbn;auto]. }
      assert (Ey0 : StandardND [standard_singleton_at e b;standard_empty_at e;A] (FEqual e y)).
      { eapply (std_specialize_equal _ x y e); [exact XY|apply std_hyp;cbn;auto]. }
      assert (By0 : StandardND [standard_singleton_at e b;standard_empty_at e;A] (FEqual b y)).
      { eapply (std_specialize_equal _ x y b); [exact XY|apply std_hyp;cbn;auto]. }
      assert (BE : StandardND [standard_singleton_at e b;standard_empty_at e;A] (FEqual b e)).
      { eapply std_eq_trans; [exact By0|apply std_eq_sym;exact Ey0]. }
      eapply std_exfalso with (p:=FMember e e); [|exact Empty].
      eapply std_mem_right; eassumption.
Qed.
Print Assumptions std_distinctor.
