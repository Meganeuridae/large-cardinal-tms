(** Relational semantics of the closure and least-formula-set clauses. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxBase BerkeleySyntaxSatisfaction BerkeleySyntaxInterpretation
  BerkeleySyntaxSets BerkeleySyntaxPairs BerkeleySyntaxFunction FormulaSemantics.
Import ListNotations.

Definition node_closure_builder f a b tag :=
  b_ain a (fun x => b_ain b (fun y => b_ein f (fun z => b_node2 z tag x y))).
Definition unary_closure_builder f tag := b_ain f (fun p => b_ein f (fun q => b_pair q tag p)).
Definition RelNodeClosure {D} (R:D->D->Prop) f a b tag :=
  forall x y, R x a -> R y b -> exists z, R z f /\ RelNode2 R z tag x y.
Definition RelUnaryClosure {D} (R:D->D->Prop) f tag :=
  forall p, R p f -> exists q, R q f /\ RelPair R q tag p.
Definition RelClosedFormulas {D} (R:D->D->Prop) f w te tm tn ti ta :=
  RelNodeClosure R f w w te /\ RelNodeClosure R f w w tm /\ RelUnaryClosure R f tn /\
  RelNodeClosure R f f f ti /\ RelNodeClosure R f w f ta.
Definition RelFormulas {D} (R:D->D->Prop) f w te tm tn ti ta :=
  RelClosedFormulas R f w te tm tn ti ta /\
  forall g, RelClosedFormulas R g w te tm tn ti ta -> RelSubset R f g.

Lemma b_good_node2 p tag x y : b_good (b_node2 p tag x y).
Proof. unfold b_node2. apply b_good_ex. intro q. unfold b_and. apply b_good_binary; apply b_good_pair. Qed.
Lemma b_good_node_closure f a b tag : b_good (node_closure_builder f a b tag).
Proof.
  unfold node_closure_builder. apply b_good_ain. intro x. apply b_good_ain. intro y.
  apply b_good_ein. intro z. apply b_good_node2.
Qed.
Lemma b_good_unary_closure f tag : b_good (unary_closure_builder f tag).
Proof. unfold unary_closure_builder. apply b_good_ain. intro p. apply b_good_ein. intro q. apply b_good_pair. Qed.
Lemma b_good_and p q : b_good p -> b_good q -> b_good (b_and p q).
Proof. unfold b_and. apply b_good_binary. Qed.
Lemma b_good_closed_formulas f w te tm tn ti ta : b_good (b_closed_formulas f w te tm tn ti ta).
Proof.
  unfold b_closed_formulas,b_and5,b_and4,b_and3.
  change (b_good (b_and (b_and (b_and (b_and
    (node_closure_builder f w w te) (node_closure_builder f w w tm))
    (unary_closure_builder f tn)) (node_closure_builder f f f ti)) (node_closure_builder f w f ta))).
  repeat apply b_good_and; try apply b_good_node_closure; apply b_good_unary_closure.
Qed.

Section FormulaSetSemantics.
Variable EM : forall P:Prop, P \/ ~P.
Variable D : Type.
Variable R : D->D->Prop.

Theorem node_closure_builder_holds rho f a b tag n : f<n -> a<n -> b<n -> tag<n ->
  (b_holds R rho (node_closure_builder f a b tag) n <->
   RelNodeClosure R (rho f) (rho a) (rho b) (rho tag)).
Proof.
  intros F A B Tag. unfold node_closure_builder,RelNodeClosure. rewrite b_holds_ain by exact A. split.
  - intros H x y X Y. specialize (H x X). rewrite b_holds_ain in H by lia.
    specialize (H y). rewrite update_variable_neq in H by lia. specialize (H Y).
    rewrite (b_holds_ein EM) in H by lia. destruct H as [z [Z Node]].
    rewrite (node2_builder_holds EM) in Node by lia.
    repeat rewrite update_variable_neq in Z by lia.
    set (sigma := update_variable (update_variable (update_variable rho n x) (S n) y) (S(S n)) z) in Node.
    assert (St : sigma tag=rho tag) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sx : sigma n=x) by (unfold sigma; repeat rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sy : sigma (S n)=y) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sz : sigma (S(S n))=z) by (unfold sigma; apply update_variable_eq).
    rewrite St,Sx,Sy,Sz in Node. exists z. auto.
  - intros H x X. rewrite b_holds_ain by lia. intros y Y. rewrite update_variable_neq in Y by lia.
    destruct (H x y X Y) as [z [Z Node]]. rewrite (b_holds_ein EM) by lia. exists z. split.
    + repeat rewrite update_variable_neq by lia. exact Z.
    + rewrite (node2_builder_holds EM) by lia.
      set (sigma := update_variable (update_variable (update_variable rho n x) (S n) y) (S(S n)) z).
      change (RelNode2 R (sigma (S(S n))) (sigma tag) (sigma n) (sigma (S n))).
      assert (St : sigma tag=rho tag) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
      assert (Sx : sigma n=x) by (unfold sigma; repeat rewrite update_variable_neq by lia; apply update_variable_eq).
      assert (Sy : sigma (S n)=y) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
      assert (Sz : sigma (S(S n))=z) by (unfold sigma; apply update_variable_eq).
      now rewrite St,Sx,Sy,Sz.
Qed.

Theorem unary_closure_builder_holds rho f tag n : f<n -> tag<n ->
  (b_holds R rho (unary_closure_builder f tag) n <-> RelUnaryClosure R (rho f) (rho tag)).
Proof.
  intros F Tag. unfold unary_closure_builder,RelUnaryClosure. rewrite b_holds_ain by exact F. split.
  - intros H p P. specialize (H p P). rewrite (b_holds_ein EM) in H by lia.
    destruct H as [q [Q Pair]]. rewrite (pair_builder_holds EM) in Pair by lia.
    rewrite update_variable_neq in Q by lia.
    set (sigma := update_variable (update_variable rho n p) (S n) q) in Pair.
    assert (St : sigma tag=rho tag) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sp : sigma n=p) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sq : sigma (S n)=q) by (unfold sigma; apply update_variable_eq).
    rewrite St,Sp,Sq in Pair. exists q. auto.
  - intros H p P. destruct (H p P) as [q [Q Pair]]. rewrite (b_holds_ein EM) by lia.
    exists q. split; [rewrite update_variable_neq by lia; exact Q|].
    rewrite (pair_builder_holds EM) by lia.
    set (sigma := update_variable (update_variable rho n p) (S n) q).
    change (RelPair R (sigma (S n)) (sigma tag) (sigma n)).
    assert (St : sigma tag=rho tag) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sp : sigma n=p) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sq : sigma (S n)=q) by (unfold sigma; apply update_variable_eq).
    now rewrite St,Sp,Sq.
Qed.

Theorem closed_formulas_builder_holds rho f w te tm tn ti ta n :
  f<n -> w<n -> te<n -> tm<n -> tn<n -> ti<n -> ta<n ->
  (b_holds R rho (b_closed_formulas f w te tm tn ti ta) n <->
   RelClosedFormulas R (rho f) (rho w) (rho te) (rho tm) (rho tn) (rho ti) (rho ta)).
Proof.
  intros F W E M N I A. unfold b_closed_formulas,RelClosedFormulas,b_and5,b_and4,b_and3.
  change (b_holds R rho (b_and (b_and (b_and (b_and
    (node_closure_builder f w w te) (node_closure_builder f w w tm))
    (unary_closure_builder f tn)) (node_closure_builder f f f ti)) (node_closure_builder f w f ta)) n <->
    RelNodeClosure R (rho f) (rho w) (rho w) (rho te) /\
    RelNodeClosure R (rho f) (rho w) (rho w) (rho tm) /\
    RelUnaryClosure R (rho f) (rho tn) /\ RelNodeClosure R (rho f) (rho f) (rho f) (rho ti) /\
    RelNodeClosure R (rho f) (rho w) (rho f) (rho ta)).
  rewrite !(b_holds_and EM).
  assert (K1 : n <= b_next (node_closure_builder f w w te) n) by apply b_good_node_closure.
  assert (K2 : n <= b_next (b_and (node_closure_builder f w w te)
    (node_closure_builder f w w tm)) n) by (apply b_good_and; apply b_good_node_closure).
  assert (K3 : n <= b_next (b_and (b_and (node_closure_builder f w w te)
    (node_closure_builder f w w tm)) (unary_closure_builder f tn)) n)
    by (repeat apply b_good_and; try apply b_good_node_closure; apply b_good_unary_closure).
  assert (K4 : n <= b_next (b_and (b_and (b_and (node_closure_builder f w w te)
    (node_closure_builder f w w tm)) (unary_closure_builder f tn)) (node_closure_builder f f f ti)) n)
    by (repeat apply b_good_and; try apply b_good_node_closure; apply b_good_unary_closure).
  rewrite !node_closure_builder_holds by lia. rewrite unary_closure_builder_holds by lia. tauto.
Qed.

Theorem formulas_builder_holds rho f w te tm tn ti ta n :
  f<n -> w<n -> te<n -> tm<n -> tn<n -> ti<n -> ta<n ->
  (b_holds R rho (b_formulas f w te tm tn ti ta) n <->
   RelFormulas R (rho f) (rho w) (rho te) (rho tm) (rho tn) (rho ti) (rho ta)).
Proof.
  intros F W E M N I A. unfold b_formulas,RelFormulas. rewrite (b_holds_and EM),closed_formulas_builder_holds by lia.
  assert (K : n <= b_next (b_closed_formulas f w te tm tn ti ta) n) by apply b_good_closed_formulas.
  rewrite b_holds_all. split; intros [Closed H]; split; try assumption; intros g.
  - specialize (H g). rewrite b_holds_imp in H. rewrite closed_formulas_builder_holds in H by lia.
    assert (J : S (b_next (b_closed_formulas f w te tm tn ti ta) n) <=
      b_next (b_closed_formulas (b_next (b_closed_formulas f w te tm tn ti ta) n) w te tm tn ti ta)
        (S (b_next (b_closed_formulas f w te tm tn ti ta) n))) by apply b_good_closed_formulas.
    rewrite subset_builder_holds in H by lia. rewrite update_variable_eq in H.
    repeat rewrite update_variable_neq in H by lia. exact H.
  - specialize (H g). rewrite b_holds_imp. rewrite closed_formulas_builder_holds by lia.
    assert (J : S (b_next (b_closed_formulas f w te tm tn ti ta) n) <=
      b_next (b_closed_formulas (b_next (b_closed_formulas f w te tm tn ti ta) n) w te tm tn ti ta)
        (S (b_next (b_closed_formulas f w te tm tn ti ta) n))) by apply b_good_closed_formulas.
    rewrite subset_builder_holds by lia. rewrite update_variable_eq.
    repeat rewrite update_variable_neq by lia. exact H.
Qed.
End FormulaSetSemantics.

Print Assumptions node_closure_builder_holds.
Print Assumptions unary_closure_builder_holds.
Print Assumptions closed_formulas_builder_holds.
Print Assumptions formulas_builder_holds.
