(** Relational semantics of the total-function graph clauses. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxBase BerkeleySyntaxInterpretation BerkeleySyntaxPairs FormulaSemantics.
Import ListNotations.

Definition function_graph_builder f a b :=
  b_ain f (fun p => b_ein a (fun x => b_ein b (fun y => b_pair p x y))).
Definition function_total_builder f a b :=
  b_ain a (fun x => b_ein b (fun y => b_and (b_rel f x y)
    (b_ain b (fun z => b_imp (b_rel f x z) (b_eq z y))))).
Definition function_unique_builder f x y b :=
  b_ain b (fun z => b_imp (b_rel f x z) (b_eq z y)).

Definition RelFunctionGraph {D} (R:D->D->Prop) f a b :=
  forall p, R p f -> exists x y, R x a /\ R y b /\ RelPair R p x y.
Definition RelFunctionTotal {D} (R:D->D->Prop) f a b :=
  forall x, R x a -> exists y, R y b /\ RelGraph R f x y /\
    forall z, R z b -> RelGraph R f x z -> z=y.
Definition RelFunction {D} (R:D->D->Prop) f a b :=
  RelFunctionGraph R f a b /\ RelFunctionTotal R f a b.
Definition RelFunctionUnique {D} (R:D->D->Prop) f x y b :=
  forall z, R z b -> RelGraph R f x z -> z=y.

Lemma b_good_pair p x y : b_good (b_pair p x y).
Proof. intro n. rewrite b_next_pair. lia. Qed.
Lemma b_good_rel f x y : b_good (b_rel f x y).
Proof.
  unfold b_rel. apply b_good_ex. intro p. unfold b_and.
  apply b_good_binary; [apply b_good_pair|apply b_good_mem].
Qed.
Lemma b_good_function_graph f a b : b_good (function_graph_builder f a b).
Proof.
  unfold function_graph_builder. apply b_good_ain. intro p. apply b_good_ein. intro x.
  apply b_good_ein. intro y. apply b_good_pair.
Qed.

Section FunctionSemantics.
Variable EM : forall P:Prop, P \/ ~P.
Variable D : Type.
Variable R : D->D->Prop.

Theorem function_graph_builder_holds rho f a b n : f<n -> a<n -> b<n ->
  (b_holds R rho (function_graph_builder f a b) n <->
   RelFunctionGraph R (rho f) (rho a) (rho b)).
Proof.
  intros F A B. unfold function_graph_builder,RelFunctionGraph.
  rewrite b_holds_ain by exact F. split.
  - intros H p P. specialize (H p P). rewrite (b_holds_ein EM) in H by lia.
    destruct H as [x [X H]]. rewrite (b_holds_ein EM) in H by lia.
    destruct H as [y [Y H]].
    rewrite (pair_builder_holds EM) in H by lia.
    set (sigma := update_variable (update_variable (update_variable rho n p) (S n) x) (S(S n)) y) in H.
    assert (Sp : sigma n=p) by (unfold sigma; repeat rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sx : sigma (S n)=x) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sy : sigma (S(S n))=y) by (unfold sigma; apply update_variable_eq).
    rewrite Sp,Sx,Sy in H. repeat rewrite update_variable_neq in X by lia.
    repeat rewrite update_variable_neq in Y by lia. exists x,y. auto.
  - intros H p P. specialize (H p P). destruct H as [x [y [X [Y Pair]]]].
    rewrite (b_holds_ein EM) by lia. exists x. split.
    + rewrite update_variable_neq by lia. exact X.
    + rewrite (b_holds_ein EM) by lia. exists y. split.
      * repeat rewrite update_variable_neq by lia. exact Y.
      * rewrite (pair_builder_holds EM) by lia.
        set (sigma := update_variable (update_variable (update_variable rho n p) (S n) x) (S(S n)) y).
        change (RelPair R (sigma n) (sigma (S n)) (sigma (S(S n)))).
        assert (Sp : sigma n=p) by (unfold sigma; repeat rewrite update_variable_neq by lia; apply update_variable_eq).
        assert (Sx : sigma (S n)=x) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
        assert (Sy : sigma (S(S n))=y) by (unfold sigma; apply update_variable_eq).
        now rewrite Sp,Sx,Sy.
Qed.

Theorem function_unique_builder_holds rho f x y b n : f<n -> x<n -> y<n -> b<n ->
  (b_holds R rho (function_unique_builder f x y b) n <->
   RelFunctionUnique R (rho f) (rho x) (rho y) (rho b)).
Proof.
  intros F X Y B. unfold function_unique_builder,RelFunctionUnique.
  rewrite b_holds_ain by exact B. split; intros H z Z; specialize (H z Z).
  - rewrite b_holds_imp in H. rewrite (relation_builder_holds EM) in H by lia.
    rewrite b_holds_eq in H. rewrite update_variable_eq in H.
    repeat rewrite update_variable_neq in H by lia. exact H.
  - rewrite b_holds_imp. rewrite (relation_builder_holds EM) by lia.
    rewrite b_holds_eq. rewrite update_variable_eq.
    repeat rewrite update_variable_neq by lia. exact H.
Qed.

Theorem function_total_builder_holds rho f a b n : f<n -> a<n -> b<n ->
  (b_holds R rho (function_total_builder f a b) n <->
   RelFunctionTotal R (rho f) (rho a) (rho b)).
Proof.
  intros F A B. unfold function_total_builder,RelFunctionTotal. rewrite b_holds_ain by exact A.
  split.
  - intros H x X. specialize (H x X). rewrite (b_holds_ein EM) in H by lia.
    destruct H as [y [Y H]]. apply (proj1 (b_holds_and EM _ _ _ _ _)) in H as [Graph Unique].
    assert (K : S(S n) <= b_next (b_rel f n (S n)) (S(S n))) by apply b_good_rel.
    rewrite (relation_builder_holds EM) in Graph by lia.
    change (b_holds R (update_variable (update_variable rho n x) (S n) y)
      (function_unique_builder f n (S n) b) (b_next (b_rel f n (S n)) (S(S n)))) in Unique.
    rewrite (function_unique_builder_holds) in Unique by lia.
    rewrite update_variable_neq in Y by lia.
    set (sigma := update_variable (update_variable rho n x) (S n) y) in Graph,Unique.
    assert (Sf : sigma f=rho f) by (unfold sigma; rewrite !update_variable_neq by lia; reflexivity).
    assert (Sb : sigma b=rho b) by (unfold sigma; rewrite !update_variable_neq by lia; reflexivity).
    assert (Sx : sigma n=x) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sy : sigma (S n)=y) by (unfold sigma; apply update_variable_eq).
    rewrite Sf,Sx,Sy in Graph. rewrite Sf,Sx,Sy,Sb in Unique.
    unfold RelFunctionUnique in Unique. exists y. auto.
  - intros H x X. specialize (H x X). destruct H as [y [Y [Graph Unique]]].
    rewrite (b_holds_ein EM) by lia. exists y. split.
    + rewrite update_variable_neq by lia. exact Y.
    + apply (proj2 (b_holds_and EM _ _ _ _ _)). split.
      * rewrite (relation_builder_holds EM) by lia.
        rewrite update_variable_eq. repeat rewrite update_variable_neq by lia.
        rewrite update_variable_eq. repeat rewrite update_variable_neq by lia. exact Graph.
      * assert (K : S(S n) <= b_next (b_rel f n (S n)) (S(S n))) by apply b_good_rel.
        change (b_holds R (update_variable (update_variable rho n x) (S n) y)
          (function_unique_builder f n (S n) b) (b_next (b_rel f n (S n)) (S(S n)))).
        rewrite (function_unique_builder_holds) by lia.
        unfold RelFunctionUnique. intros z Z G.
        rewrite update_variable_eq in *.
        repeat rewrite update_variable_neq in * by lia.
        rewrite update_variable_eq in *. repeat rewrite update_variable_neq in * by lia.
        now apply Unique.
Qed.

Theorem function_builder_holds rho f a b n : f<n -> a<n -> b<n ->
  (b_holds R rho (b_function f a b) n <-> RelFunction R (rho f) (rho a) (rho b)).
Proof.
  intros F A B. unfold b_function,RelFunction.
  change (b_holds R rho (b_and (function_graph_builder f a b) (function_total_builder f a b)) n <->
    RelFunctionGraph R (rho f) (rho a) (rho b) /\ RelFunctionTotal R (rho f) (rho a) (rho b)).
  rewrite (b_holds_and EM). rewrite (function_graph_builder_holds rho f a b n F A B).
  assert (K : n <= b_next (function_graph_builder f a b) n) by apply b_good_function_graph.
  rewrite (function_total_builder_holds) by lia. reflexivity.
Qed.
End FunctionSemantics.

Print Assumptions function_graph_builder_holds.
Print Assumptions function_unique_builder_holds.
Print Assumptions function_total_builder_holds.
Print Assumptions function_builder_holds.
