(** Relational interpretation of bijections in the generated cardinal clause. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxBase BerkeleySyntaxInterpretation BerkeleySyntaxPairs
  BerkeleySyntaxFunction FormulaSemantics.
Import ListNotations.

Definition bijection_surj_builder f a b :=
  b_ain b (fun y => b_ein a (fun x => b_rel f x y)).
Definition bijection_inj_core f x z y :=
  b_imp (b_and (b_rel f x y) (b_rel f z y)) (b_eq x z).
Definition bijection_inj_builder f a b :=
  b_ain a (fun x => b_ain a (fun z => b_ain b (fun y => bijection_inj_core f x z y))).

Definition RelSurjective {D} (R:D->D->Prop) f a b :=
  forall y, R y b -> exists x, R x a /\ RelGraph R f x y.
Definition RelInjective {D} (R:D->D->Prop) f a b :=
  forall x z y, R x a -> R z a -> R y b ->
    RelGraph R f x y -> RelGraph R f z y -> x=z.
Definition RelBijection {D} (R:D->D->Prop) f a b :=
  RelFunction R f a b /\ RelSurjective R f a b /\ RelInjective R f a b.

Lemma b_good_function_total f a b : b_good (function_total_builder f a b).
Proof.
  unfold function_total_builder. apply b_good_ain. intro x. apply b_good_ein. intro y.
  unfold b_and. apply b_good_binary; [apply b_good_rel|]. apply b_good_ain. intro z.
  unfold b_imp. apply b_good_binary; [apply b_good_rel|apply b_good_eq].
Qed.
Lemma b_good_function f a b : b_good (b_function f a b).
Proof.
  unfold b_function. change (b_good (b_and (function_graph_builder f a b) (function_total_builder f a b))).
  unfold b_and. apply b_good_binary; [apply b_good_function_graph|apply b_good_function_total].
Qed.
Lemma b_good_bijection_surj f a b : b_good (bijection_surj_builder f a b).
Proof. unfold bijection_surj_builder. apply b_good_ain. intro y. apply b_good_ein. intro x. apply b_good_rel. Qed.

Section BijectionSemantics.
Variable EM : forall P:Prop, P \/ ~P.
Variable D : Type.
Variable R : D->D->Prop.

Theorem bijection_surj_builder_holds rho f a b n : f<n -> a<n -> b<n ->
  (b_holds R rho (bijection_surj_builder f a b) n <-> RelSurjective R (rho f) (rho a) (rho b)).
Proof.
  intros F A B. unfold bijection_surj_builder,RelSurjective. rewrite b_holds_ain by exact B. split.
  - intros H y Y. specialize (H y Y). rewrite (b_holds_ein EM) in H by lia.
    destruct H as [x [X G]]. rewrite (relation_builder_holds EM) in G by lia.
    rewrite update_variable_neq in X by lia.
    set (sigma := update_variable (update_variable rho n y) (S n) x) in G.
    assert (Sf : sigma f=rho f) by (unfold sigma; rewrite !update_variable_neq by lia; reflexivity).
    assert (Sx : sigma (S n)=x) by (unfold sigma; apply update_variable_eq).
    assert (Sy : sigma n=y) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    rewrite Sf,Sx,Sy in G. exists x. auto.
  - intros H y Y. specialize (H y Y). destruct H as [x [X G]].
    rewrite (b_holds_ein EM) by lia. exists x. split.
    + rewrite update_variable_neq by lia. exact X.
    + rewrite (relation_builder_holds EM) by lia.
      set (sigma := update_variable (update_variable rho n y) (S n) x).
      change (RelGraph R (sigma f) (sigma (S n)) (sigma n)).
      assert (Sf : sigma f=rho f) by (unfold sigma; rewrite !update_variable_neq by lia; reflexivity).
      assert (Sx : sigma (S n)=x) by (unfold sigma; apply update_variable_eq).
      assert (Sy : sigma n=y) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
      now rewrite Sf,Sx,Sy.
Qed.

Lemma bijection_inj_core_holds rho f x z y n : f<n -> x<n -> z<n -> y<n ->
  (b_holds R rho (bijection_inj_core f x z y) n <->
   (RelGraph R (rho f) (rho x) (rho y) /\ RelGraph R (rho f) (rho z) (rho y) -> rho x=rho z)).
Proof.
  intros F X Z Y. unfold bijection_inj_core. rewrite b_holds_imp, (b_holds_and EM), b_holds_eq.
  assert (K : n <= b_next (b_rel f x y) n) by apply b_good_rel.
  rewrite !(relation_builder_holds EM) by lia. reflexivity.
Qed.

Theorem bijection_inj_builder_holds rho f a b n : f<n -> a<n -> b<n ->
  (b_holds R rho (bijection_inj_builder f a b) n <-> RelInjective R (rho f) (rho a) (rho b)).
Proof.
  intros F A B. unfold bijection_inj_builder,RelInjective. rewrite b_holds_ain by exact A. split.
  - intros H x z y X Z Y G1 G2. specialize (H x X).
    rewrite b_holds_ain in H by lia. specialize (H z).
    rewrite update_variable_neq in H by lia. specialize (H Z).
    rewrite b_holds_ain in H by lia. specialize (H y).
    repeat rewrite update_variable_neq in H by lia. specialize (H Y).
    rewrite bijection_inj_core_holds in H by lia.
    set (sigma := update_variable (update_variable (update_variable rho n x) (S n) z) (S(S n)) y) in H.
    assert (Sf : sigma f=rho f) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sx : sigma n=x) by (unfold sigma; repeat rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sz : sigma (S n)=z) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sy : sigma (S(S n))=y) by (unfold sigma; apply update_variable_eq).
    rewrite Sf,Sx,Sz,Sy in H. now apply H.
  - intros H x X. rewrite b_holds_ain by lia. intros z Z.
    rewrite update_variable_neq in Z by lia.
    rewrite b_holds_ain by lia. intros y Y. repeat rewrite update_variable_neq in Y by lia.
    rewrite bijection_inj_core_holds by lia.
    set (sigma := update_variable (update_variable (update_variable rho n x) (S n) z) (S(S n)) y).
    change ((RelGraph R (sigma f) (sigma n) (sigma (S(S n))) /\
             RelGraph R (sigma f) (sigma (S n)) (sigma (S(S n)))) -> sigma n=sigma (S n)).
    assert (Sf : sigma f=rho f) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sx : sigma n=x) by (unfold sigma; repeat rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sz : sigma (S n)=z) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sy : sigma (S(S n))=y) by (unfold sigma; apply update_variable_eq).
    rewrite Sf,Sx,Sz,Sy. intros [G1 G2]. now apply H with (y:=y).
Qed.

Theorem bijection_builder_holds rho f a b n : f<n -> a<n -> b<n ->
  (b_holds R rho (b_bijection f a b) n <-> RelBijection R (rho f) (rho a) (rho b)).
Proof.
  intros F A B. unfold b_bijection,RelBijection,b_and3.
  change (b_holds R rho (b_and (b_and (b_function f a b) (bijection_surj_builder f a b))
    (bijection_inj_builder f a b)) n <->
    RelFunction R (rho f) (rho a) (rho b) /\
    RelSurjective R (rho f) (rho a) (rho b) /\ RelInjective R (rho f) (rho a) (rho b)).
  rewrite !(b_holds_and EM).
  assert (K1 : n <= b_next (b_function f a b) n) by apply b_good_function.
  assert (K2 : n <= b_next (b_and (b_function f a b) (bijection_surj_builder f a b)) n).
  { unfold b_and. apply b_good_binary; [apply b_good_function|apply b_good_bijection_surj]. }
  rewrite (function_builder_holds EM) by lia.
  rewrite (bijection_surj_builder_holds) by lia.
  rewrite (bijection_inj_builder_holds) by lia. tauto.
Qed.
End BijectionSemantics.

Print Assumptions bijection_surj_builder_holds.
Print Assumptions bijection_inj_builder_holds.
Print Assumptions bijection_builder_holds.
