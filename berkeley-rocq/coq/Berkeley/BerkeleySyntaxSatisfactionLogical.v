(** Relational meaning of negation and implication recursion clauses. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxBase BerkeleySyntaxInterpretation BerkeleySyntaxPairs
  BerkeleySyntaxFunction BerkeleySyntaxFormulaSet FormulaSemantics.
Import ListNotations.

Definition neg_core_builder s sat tag p q :=
  b_imp (b_pair q tag p) (b_iff (b_rel sat q s) (b_not (b_rel sat p s))).
Definition neg_clause_builder s sat f tag :=
  b_ain f (fun p => b_all (fun q => neg_core_builder s sat tag p q)).
Definition RelNegClause {D} (R:D->D->Prop) s sat f tag :=
  forall p q, R p f -> RelPair R q tag p ->
    (RelGraph R sat q s <-> ~ RelGraph R sat p s).
Definition imp_core_builder s sat tag p q r :=
  b_imp (b_node2 r tag p q) (b_iff (b_rel sat r s) (b_imp (b_rel sat p s) (b_rel sat q s))).
Definition imp_clause_builder s sat f tag :=
  b_ain f (fun p => b_ain f (fun q => b_all (fun r => imp_core_builder s sat tag p q r))).
Definition RelImpClause {D} (R:D->D->Prop) s sat f tag :=
  forall p q r, R p f -> R q f -> RelNode2 R r tag p q ->
    (RelGraph R sat r s <-> (RelGraph R sat p s -> RelGraph R sat q s)).

Lemma b_good_neg_core s sat tag p q : b_good (neg_core_builder s sat tag p q).
Proof.
  unfold neg_core_builder,b_imp,b_iff. apply b_good_binary; [apply b_good_pair|].
  apply b_good_binary; [apply b_good_rel|apply b_good_not,b_good_rel].
Qed.
Lemma b_good_neg_clause s sat f tag : b_good (neg_clause_builder s sat f tag).
Proof. unfold neg_clause_builder. apply b_good_ain. intro p. apply b_good_all. intro q. apply b_good_neg_core. Qed.
Lemma b_good_imp_core s sat tag p q r : b_good (imp_core_builder s sat tag p q r).
Proof.
  unfold imp_core_builder,b_imp,b_iff. apply b_good_binary; [apply b_good_node2|].
  apply b_good_binary; [apply b_good_rel|apply b_good_binary; apply b_good_rel].
Qed.
Lemma b_good_imp_clause s sat f tag : b_good (imp_clause_builder s sat f tag).
Proof.
  unfold imp_clause_builder. apply b_good_ain. intro p. apply b_good_ain. intro q.
  apply b_good_all. intro r. apply b_good_imp_core.
Qed.

Section LogicalSemantics.
Variable EM : forall P:Prop, P \/ ~P.
Variable D : Type.
Variable R : D->D->Prop.

Lemma neg_core_builder_holds rho s sat tag p q n :
  s<n -> sat<n -> tag<n -> p<n -> q<n ->
  (b_holds R rho (neg_core_builder s sat tag p q) n <->
   (RelPair R (rho q) (rho tag) (rho p) ->
    (RelGraph R (rho sat) (rho q) (rho s) <-> ~ RelGraph R (rho sat) (rho p) (rho s)))).
Proof.
  intros S0 Sat Tag P Q. unfold neg_core_builder. rewrite b_holds_imp,(b_holds_iff EM),b_holds_not.
  assert (K1 : n <= b_next (b_pair q tag p) n) by apply b_good_pair.
  assert (K2 : b_next (b_pair q tag p) n <= b_next (b_rel sat q s) (b_next (b_pair q tag p) n)) by apply b_good_rel.
  rewrite (pair_builder_holds EM),!(relation_builder_holds EM) by lia. reflexivity.
Qed.

Theorem neg_clause_builder_holds rho s sat f tag n :
  s<n -> sat<n -> f<n -> tag<n ->
  (b_holds R rho (neg_clause_builder s sat f tag) n <->
   RelNegClause R (rho s) (rho sat) (rho f) (rho tag)).
Proof.
  intros S0 Sat F Tag. unfold neg_clause_builder,RelNegClause. rewrite b_holds_ain by exact F. split.
  - intros H p q P Pair. specialize (H p P). rewrite b_holds_all in H. specialize (H q).
    rewrite neg_core_builder_holds in H by lia.
    set (sigma := update_variable (update_variable rho n p) (S n) q) in H.
    assert (A : sigma s=rho s) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (B : sigma sat=rho sat) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (C : sigma tag=rho tag) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (D0 : sigma n=p) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (E : sigma (S n)=q) by (unfold sigma; apply update_variable_eq).
    rewrite A,B,C,D0,E in H. now apply H.
  - intros H p P. rewrite b_holds_all. intro q. rewrite neg_core_builder_holds by lia.
    set (sigma := update_variable (update_variable rho n p) (S n) q).
    change (RelPair R (sigma (S n)) (sigma tag) (sigma n) ->
      (RelGraph R (sigma sat) (sigma (S n)) (sigma s) <-> ~RelGraph R (sigma sat) (sigma n) (sigma s))).
    assert (A : sigma s=rho s) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (B : sigma sat=rho sat) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (C : sigma tag=rho tag) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (D0 : sigma n=p) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (E : sigma (S n)=q) by (unfold sigma; apply update_variable_eq).
    rewrite A,B,C,D0,E. now apply H.
Qed.

Lemma imp_core_builder_holds rho s sat tag p q r n :
  s<n -> sat<n -> tag<n -> p<n -> q<n -> r<n ->
  (b_holds R rho (imp_core_builder s sat tag p q r) n <->
   (RelNode2 R (rho r) (rho tag) (rho p) (rho q) ->
    (RelGraph R (rho sat) (rho r) (rho s) <->
      (RelGraph R (rho sat) (rho p) (rho s) -> RelGraph R (rho sat) (rho q) (rho s))))).
Proof.
  intros S0 Sat Tag P Q R0. unfold imp_core_builder. rewrite b_holds_imp,(b_holds_iff EM),b_holds_imp.
  assert (K1 : n <= b_next (b_node2 r tag p q) n) by apply b_good_node2.
  assert (K2 : b_next (b_node2 r tag p q) n <= b_next (b_rel sat r s) (b_next (b_node2 r tag p q) n)) by apply b_good_rel.
  assert (K3 : b_next (b_rel sat r s) (b_next (b_node2 r tag p q) n) <=
    b_next (b_rel sat p s) (b_next (b_rel sat r s) (b_next (b_node2 r tag p q) n))) by apply b_good_rel.
  rewrite (node2_builder_holds EM),!(relation_builder_holds EM) by lia. reflexivity.
Qed.

Theorem imp_clause_builder_holds rho s sat f tag n :
  s<n -> sat<n -> f<n -> tag<n ->
  (b_holds R rho (imp_clause_builder s sat f tag) n <->
   RelImpClause R (rho s) (rho sat) (rho f) (rho tag)).
Proof.
  intros S0 Sat F Tag. unfold imp_clause_builder,RelImpClause. rewrite b_holds_ain by exact F. split.
  - intros H p q r P Q Node. specialize (H p P). rewrite b_holds_ain in H by lia.
    specialize (H q). rewrite update_variable_neq in H by lia. specialize (H Q).
    rewrite b_holds_all in H. specialize (H r). rewrite imp_core_builder_holds in H by lia.
    set (sigma := update_variable (update_variable (update_variable rho n p) (S n) q) (S(S n)) r) in H.
    assert (A : sigma s=rho s) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (B : sigma sat=rho sat) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (C : sigma tag=rho tag) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (P0 : sigma n=p) by (unfold sigma; repeat rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Q0 : sigma (S n)=q) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (R0 : sigma (S(S n))=r) by (unfold sigma; apply update_variable_eq).
    rewrite A,B,C,P0,Q0,R0 in H. now apply H.
  - intros H p P. rewrite b_holds_ain by lia. intros q Q. rewrite update_variable_neq in Q by lia.
    rewrite b_holds_all. intro r. rewrite imp_core_builder_holds by lia.
    set (sigma := update_variable (update_variable (update_variable rho n p) (S n) q) (S(S n)) r).
    change (RelNode2 R (sigma (S(S n))) (sigma tag) (sigma n) (sigma (S n)) ->
      (RelGraph R (sigma sat) (sigma (S(S n))) (sigma s) <->
       (RelGraph R (sigma sat) (sigma n) (sigma s) -> RelGraph R (sigma sat) (sigma (S n)) (sigma s)))).
    assert (A : sigma s=rho s) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (B : sigma sat=rho sat) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (C : sigma tag=rho tag) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (P0 : sigma n=p) by (unfold sigma; repeat rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Q0 : sigma (S n)=q) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (R0 : sigma (S(S n))=r) by (unfold sigma; apply update_variable_eq).
    rewrite A,B,C,P0,Q0,R0. now apply H.
Qed.
End LogicalSemantics.

Print Assumptions neg_clause_builder_holds.
Print Assumptions imp_clause_builder_holds.
