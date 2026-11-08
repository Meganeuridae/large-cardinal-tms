(** Exact relational interpretation of the five finite Tarski clauses.
    This characterizes the assertion; it does not assert existence of a truth set. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxBase BerkeleySyntaxSatisfaction BerkeleySyntaxInterpretation
  BerkeleySyntaxPairs BerkeleySyntaxFunction BerkeleySyntaxFormulaSet BerkeleySyntaxEnvironment
  BerkeleySyntaxSatisfactionAtomic BerkeleySyntaxSatisfactionLogical BerkeleySyntaxSatisfactionAll FormulaSemantics.
Import ListNotations.

Definition satisfaction_clauses_builder s sat e f w m te tm tn ti ta := b_and5
  (atomic_clause_builder false s sat w m te)
  (atomic_clause_builder true s sat w m tm)
  (neg_clause_builder s sat f tn)
  (imp_clause_builder s sat f ti)
  (all_clause_builder s sat e f w m ta).
Definition RelSatisfactionClauses {D} (R:D->D->Prop) s sat e f w m te tm tn ti ta :=
  RelAtomicClause R false s sat w m te /\ RelAtomicClause R true s sat w m tm /\
  RelNegClause R s sat f tn /\ RelImpClause R s sat f ti /\ RelAllClause R s sat e f w m ta.
Definition RelSatisfaction {D} (R:D->D->Prop) sat e f w m te tm tn ti ta :=
  forall s, R s e -> RelSatisfactionClauses R s sat e f w m te tm tn ti ta.

Lemma b_good_satisfaction_clauses s sat e f w m te tm tn ti ta :
  b_good (satisfaction_clauses_builder s sat e f w m te tm tn ti ta).
Proof.
  unfold satisfaction_clauses_builder,b_and5,b_and4,b_and3.
  apply b_good_and; [|apply b_good_all_clause].
  apply b_good_and; [|apply b_good_imp_clause].
  apply b_good_and; [|apply b_good_neg_clause].
  apply b_good_and; apply b_good_atomic_clause.
Qed.
Lemma b_good_satisfaction sat e f w m te tm tn ti ta : b_good (b_satisfaction sat e f w m te tm tn ti ta).
Proof.
  unfold b_satisfaction. apply b_good_ain. intro s.
  change (b_good (satisfaction_clauses_builder s sat e f w m te tm tn ti ta)).
  apply b_good_satisfaction_clauses.
Qed.

Section SatisfactionSemantics.
Variable EM : forall P:Prop, P \/ ~P.
Variable D : Type.
Variable R : D->D->Prop.

Theorem satisfaction_clauses_builder_holds rho s sat e f w m te tm tn ti ta n :
  s<n -> sat<n -> e<n -> f<n -> w<n -> m<n -> te<n -> tm<n -> tn<n -> ti<n -> ta<n ->
  (b_holds R rho (satisfaction_clauses_builder s sat e f w m te tm tn ti ta) n <->
   RelSatisfactionClauses R (rho s) (rho sat) (rho e) (rho f) (rho w) (rho m)
     (rho te) (rho tm) (rho tn) (rho ti) (rho ta)).
Proof.
  intros S0 Sat E F W M Te Tm Tn Ti Ta.
  unfold satisfaction_clauses_builder,RelSatisfactionClauses,b_and5,b_and4,b_and3.
  rewrite !(b_holds_and EM).
  assert (K1 : n <= b_next (atomic_clause_builder false s sat w m te) n) by apply b_good_atomic_clause.
  assert (K2 : n <= b_next (b_and (atomic_clause_builder false s sat w m te)
    (atomic_clause_builder true s sat w m tm)) n) by (apply b_good_and; apply b_good_atomic_clause).
  assert (K3 : n <= b_next (b_and (b_and (atomic_clause_builder false s sat w m te)
    (atomic_clause_builder true s sat w m tm)) (neg_clause_builder s sat f tn)) n)
    by (apply b_good_and; [apply b_good_and; apply b_good_atomic_clause|apply b_good_neg_clause]).
  assert (K4 : n <= b_next (b_and (b_and (b_and (atomic_clause_builder false s sat w m te)
    (atomic_clause_builder true s sat w m tm)) (neg_clause_builder s sat f tn)) (imp_clause_builder s sat f ti)) n)
    by (apply b_good_and; [apply b_good_and; [apply b_good_and; apply b_good_atomic_clause|apply b_good_neg_clause]|apply b_good_imp_clause]).
  rewrite !(atomic_clause_builder_holds EM), (neg_clause_builder_holds EM),
    (imp_clause_builder_holds EM), (all_clause_builder_holds EM) by lia. tauto.
Qed.

Theorem satisfaction_builder_holds rho sat e f w m te tm tn ti ta n :
  sat<n -> e<n -> f<n -> w<n -> m<n -> te<n -> tm<n -> tn<n -> ti<n -> ta<n ->
  (b_holds R rho (b_satisfaction sat e f w m te tm tn ti ta) n <->
   RelSatisfaction R (rho sat) (rho e) (rho f) (rho w) (rho m)
     (rho te) (rho tm) (rho tn) (rho ti) (rho ta)).
Proof.
  intros Sat E F W M Te Tm Tn Ti Ta. unfold b_satisfaction,RelSatisfaction.
  change (b_holds R rho (b_ain e (fun s => satisfaction_clauses_builder s sat e f w m te tm tn ti ta)) n <->
    forall s, R s (rho e) -> RelSatisfactionClauses R s (rho sat) (rho e) (rho f) (rho w) (rho m)
      (rho te) (rho tm) (rho tn) (rho ti) (rho ta)).
  rewrite b_holds_ain by exact E. split; intros H s S0; specialize (H s S0).
  - rewrite satisfaction_clauses_builder_holds in H by lia.
    rewrite update_variable_eq in H. repeat rewrite update_variable_neq in H by lia. exact H.
  - rewrite satisfaction_clauses_builder_holds by lia.
    rewrite update_variable_eq. repeat rewrite update_variable_neq by lia. exact H.
Qed.
End SatisfactionSemantics.

Print Assumptions satisfaction_clauses_builder_holds.
Print Assumptions satisfaction_builder_holds.
