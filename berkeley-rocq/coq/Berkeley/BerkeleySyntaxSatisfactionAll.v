(** Relational meaning of the universal-quantifier recursion clause. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxBase BerkeleySyntaxSatisfaction BerkeleySyntaxInterpretation
  BerkeleySyntaxPairs BerkeleySyntaxFunction BerkeleySyntaxFormulaSet BerkeleySyntaxEnvironment FormulaSemantics.
Import ListNotations.

Definition all_rhs_builder s sat e w m u p :=
  b_ain e (fun t => b_imp (b_update s t u w m) (b_rel sat p t)).
Definition all_core_builder s sat e w m tag u p q :=
  b_imp (b_node2 q tag u p) (b_iff (b_rel sat q s) (all_rhs_builder s sat e w m u p)).
Definition all_clause_builder s sat e f w m tag :=
  b_ain w (fun u => b_ain f (fun p => b_all (fun q => all_core_builder s sat e w m tag u p q))).
Definition RelAllClause {D} (R:D->D->Prop) s sat e f w m tag :=
  forall u p q, R u w -> R p f -> RelNode2 R q tag u p ->
    (RelGraph R sat q s <-> forall t, R t e -> RelUpdate R s t u w m -> RelGraph R sat p t).

Lemma b_good_update s t u w m : b_good (b_update s t u w m).
Proof.
  unfold b_update. apply b_good_ain. intro v. unfold b_or. apply b_good_binary; [apply b_good_eq|].
  apply b_good_ain. intro x. unfold b_iff. apply b_good_binary; apply b_good_rel.
Qed.
Lemma b_good_all_rhs s sat e w m u p : b_good (all_rhs_builder s sat e w m u p).
Proof.
  unfold all_rhs_builder. apply b_good_ain. intro t. unfold b_imp.
  apply b_good_binary; [apply b_good_update|apply b_good_rel].
Qed.
Lemma b_good_all_core s sat e w m tag u p q : b_good (all_core_builder s sat e w m tag u p q).
Proof.
  unfold all_core_builder,b_imp,b_iff. apply b_good_binary; [apply b_good_node2|].
  apply b_good_binary; [apply b_good_rel|apply b_good_all_rhs].
Qed.
Lemma b_good_all_clause s sat e f w m tag : b_good (all_clause_builder s sat e f w m tag).
Proof.
  unfold all_clause_builder. apply b_good_ain. intro u. apply b_good_ain. intro p.
  apply b_good_all. intro q. apply b_good_all_core.
Qed.

Section AllSemantics.
Variable EM : forall P:Prop, P \/ ~P.
Variable D : Type.
Variable R : D->D->Prop.

Lemma all_rhs_builder_holds rho s sat e w m u p n :
  s<n -> sat<n -> e<n -> w<n -> m<n -> u<n -> p<n ->
  (b_holds R rho (all_rhs_builder s sat e w m u p) n <->
   forall t, R t (rho e) -> RelUpdate R (rho s) t (rho u) (rho w) (rho m) -> RelGraph R (rho sat) (rho p) t).
Proof.
  intros S0 Sat E W M U P. unfold all_rhs_builder. rewrite b_holds_ain by exact E. split; intros H t T; specialize (H t T).
  - rewrite b_holds_imp in H.
    assert (K : S n <= b_next (b_update s n u w m) (S n)) by apply b_good_update.
    rewrite (update_builder_holds EM),(relation_builder_holds EM) in H by lia.
    rewrite update_variable_eq in H. repeat rewrite update_variable_neq in H by lia. exact H.
  - rewrite b_holds_imp.
    assert (K : S n <= b_next (b_update s n u w m) (S n)) by apply b_good_update.
    rewrite (update_builder_holds EM),(relation_builder_holds EM) by lia.
    rewrite update_variable_eq. repeat rewrite update_variable_neq by lia. exact H.
Qed.

Lemma all_core_builder_holds rho s sat e w m tag u p q n :
  s<n -> sat<n -> e<n -> w<n -> m<n -> tag<n -> u<n -> p<n -> q<n ->
  (b_holds R rho (all_core_builder s sat e w m tag u p q) n <->
   (RelNode2 R (rho q) (rho tag) (rho u) (rho p) ->
    (RelGraph R (rho sat) (rho q) (rho s) <->
      forall t, R t (rho e) -> RelUpdate R (rho s) t (rho u) (rho w) (rho m) -> RelGraph R (rho sat) (rho p) t))).
Proof.
  intros S0 Sat E W M Tag U P Q. unfold all_core_builder. rewrite b_holds_imp,(b_holds_iff EM).
  assert (K1 : n <= b_next (b_node2 q tag u p) n) by apply b_good_node2.
  assert (K2 : b_next (b_node2 q tag u p) n <= b_next (b_rel sat q s) (b_next (b_node2 q tag u p) n)) by apply b_good_rel.
  rewrite (node2_builder_holds EM),(relation_builder_holds EM),all_rhs_builder_holds by lia. reflexivity.
Qed.

Theorem all_clause_builder_holds rho s sat e f w m tag n :
  s<n -> sat<n -> e<n -> f<n -> w<n -> m<n -> tag<n ->
  (b_holds R rho (all_clause_builder s sat e f w m tag) n <->
   RelAllClause R (rho s) (rho sat) (rho e) (rho f) (rho w) (rho m) (rho tag)).
Proof.
  intros S0 Sat E F W M Tag. unfold all_clause_builder,RelAllClause. rewrite b_holds_ain by exact W. split.
  - intros H u p q U P Node. specialize (H u U). rewrite b_holds_ain in H by lia.
    specialize (H p). rewrite update_variable_neq in H by lia. specialize (H P).
    rewrite b_holds_all in H. specialize (H q). rewrite all_core_builder_holds in H by lia.
    set (sigma := update_variable (update_variable (update_variable rho n u) (S n) p) (S(S n)) q) in H.
    assert (A : sigma s=rho s) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (B : sigma sat=rho sat) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (C : sigma e=rho e) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (D0 : sigma w=rho w) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (F0 : sigma m=rho m) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (G : sigma tag=rho tag) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (U0 : sigma n=u) by (unfold sigma; repeat rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (P0 : sigma (S n)=p) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Q0 : sigma (S(S n))=q) by (unfold sigma; apply update_variable_eq).
    rewrite A,B,C,D0,F0,G,U0,P0,Q0 in H. now apply H.
  - intros H u U. rewrite b_holds_ain by lia. intros p P. rewrite update_variable_neq in P by lia.
    rewrite b_holds_all. intro q. rewrite all_core_builder_holds by lia.
    set (sigma := update_variable (update_variable (update_variable rho n u) (S n) p) (S(S n)) q).
    change (RelNode2 R (sigma (S(S n))) (sigma tag) (sigma n) (sigma (S n)) ->
      (RelGraph R (sigma sat) (sigma (S(S n))) (sigma s) <->
       forall t, R t (sigma e) -> RelUpdate R (sigma s) t (sigma n) (sigma w) (sigma m) -> RelGraph R (sigma sat) (sigma (S n)) t)).
    assert (A : sigma s=rho s) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (B : sigma sat=rho sat) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (C : sigma e=rho e) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (D0 : sigma w=rho w) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (F0 : sigma m=rho m) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (G : sigma tag=rho tag) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (U0 : sigma n=u) by (unfold sigma; repeat rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (P0 : sigma (S n)=p) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Q0 : sigma (S(S n))=q) by (unfold sigma; apply update_variable_eq).
    rewrite A,B,C,D0,F0,G,U0,P0,Q0. now apply H.
Qed.
End AllSemantics.

Print Assumptions all_rhs_builder_holds.
Print Assumptions all_clause_builder_holds.
