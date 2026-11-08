(** Relational meaning of the equality and membership Tarski clauses. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxBase BerkeleySyntaxInterpretation BerkeleySyntaxPairs
  BerkeleySyntaxFunction BerkeleySyntaxFormulaSet BerkeleySyntaxScope FormulaSemantics.
Import ListNotations.

Definition atom_truth {D} (R:D->D->Prop) (member:bool) (x y:D) := if member then R x y else x=y.
Definition atomic_core_builder (member:bool) s sat tag u v x y p :=
  b_imp (b_and3 (b_rel s u x) (b_rel s v y) (b_node2 p tag u v))
    (b_iff (b_rel sat p s) (if member then b_mem x y else b_eq x y)).
Definition atomic_clause_builder member s sat w m tag :=
  b_ain w (fun u => b_ain w (fun v => b_ain m (fun x => b_ain m (fun y => b_all (fun p =>
    atomic_core_builder member s sat tag u v x y p))))).
Definition RelAtomicClause {D} (R:D->D->Prop) member s sat w m tag :=
  forall u v x y p, R u w -> R v w -> R x m -> R y m ->
    RelGraph R s u x -> RelGraph R s v y -> RelNode2 R p tag u v ->
    (RelGraph R sat p s <-> atom_truth R member x y).

Lemma b_good_atomic_core member s sat tag u v x y p :
  b_good (atomic_core_builder member s sat tag u v x y p).
Proof.
  unfold atomic_core_builder,b_imp,b_and3,b_and,b_iff.
  apply b_good_binary.
  - apply b_good_binary; [apply b_good_binary; apply b_good_rel|apply b_good_node2].
  - apply b_good_binary; [apply b_good_rel|destruct member; [apply b_good_mem|apply b_good_eq]].
Qed.
Lemma b_good_atomic_clause member s sat w m tag : b_good (atomic_clause_builder member s sat w m tag).
Proof.
  unfold atomic_clause_builder. apply b_good_ain. intro u. apply b_good_ain. intro v.
  apply b_good_ain. intro x. apply b_good_ain. intro y. apply b_good_all. intro p.
  apply b_good_atomic_core.
Qed.

Section AtomicSemantics.
Variable EM : forall P:Prop, P \/ ~P.
Variable D : Type.
Variable R : D->D->Prop.

Lemma atomic_core_builder_holds member rho s sat tag u v x y p n :
  s<n -> sat<n -> tag<n -> u<n -> v<n -> x<n -> y<n -> p<n ->
  (b_holds R rho (atomic_core_builder member s sat tag u v x y p) n <->
   ((RelGraph R (rho s) (rho u) (rho x) /\ RelGraph R (rho s) (rho v) (rho y)) /\
       RelNode2 R (rho p) (rho tag) (rho u) (rho v) ->
    (RelGraph R (rho sat) (rho p) (rho s) <-> atom_truth R member (rho x) (rho y)))).
Proof.
  intros S0 Sat Tag U V X Y P. unfold atomic_core_builder,b_and3.
  rewrite b_holds_imp,!(b_holds_and EM),(b_holds_iff EM).
  assert (K1 : n <= b_next (b_rel s u x) n) by apply b_good_rel.
  assert (K2 : n <= b_next (b_and (b_rel s u x) (b_rel s v y)) n) by (apply b_good_and; apply b_good_rel).
  assert (K3 : n <= b_next (b_and (b_and (b_rel s u x) (b_rel s v y)) (b_node2 p tag u v)) n)
    by (apply b_good_and; [apply b_good_and; apply b_good_rel|apply b_good_node2]).
  assert (K4 : b_next (b_and (b_and (b_rel s u x) (b_rel s v y)) (b_node2 p tag u v)) n <=
    b_next (b_rel sat p s) (b_next (b_and (b_and (b_rel s u x) (b_rel s v y)) (b_node2 p tag u v)) n))
    by apply b_good_rel.
  rewrite !(relation_builder_holds EM), (node2_builder_holds EM) by lia.
  destruct member; cbn [atom_truth]; [rewrite b_holds_mem|rewrite b_holds_eq]; reflexivity.
Qed.

Theorem atomic_clause_builder_holds member rho s sat w m tag n :
  s<n -> sat<n -> w<n -> m<n -> tag<n ->
  (b_holds R rho (atomic_clause_builder member s sat w m tag) n <->
   RelAtomicClause R member (rho s) (rho sat) (rho w) (rho m) (rho tag)).
Proof.
  intros S0 Sat W M Tag. unfold atomic_clause_builder,RelAtomicClause. rewrite b_holds_ain by exact W. split.
  - intros H u v x y p U V X Y G1 G2 Node.
    specialize (H u U). rewrite b_holds_ain in H by lia. specialize (H v).
    rewrite update_variable_neq in H by lia. specialize (H V).
    rewrite b_holds_ain in H by lia. specialize (H x). repeat rewrite update_variable_neq in H by lia. specialize (H X).
    rewrite b_holds_ain in H by lia. specialize (H y). repeat rewrite update_variable_neq in H by lia. specialize (H Y).
    rewrite b_holds_all in H. specialize (H p). rewrite atomic_core_builder_holds in H by lia.
    change (((RelGraph R (push_environment rho n [u;v;x;y;p] s) (push_environment rho n [u;v;x;y;p] n)
      (push_environment rho n [u;v;x;y;p] (S(S n))) /\
      RelGraph R (push_environment rho n [u;v;x;y;p] s) (push_environment rho n [u;v;x;y;p] (S n))
      (push_environment rho n [u;v;x;y;p] (S(S(S n))))) /\
      RelNode2 R (push_environment rho n [u;v;x;y;p] (S(S(S(S n)))))
        (push_environment rho n [u;v;x;y;p] tag) (push_environment rho n [u;v;x;y;p] n)
        (push_environment rho n [u;v;x;y;p] (S n))) ->
      (RelGraph R (push_environment rho n [u;v;x;y;p] sat)
        (push_environment rho n [u;v;x;y;p] (S(S(S(S n))))) (push_environment rho n [u;v;x;y;p] s) <->
       atom_truth R member (push_environment rho n [u;v;x;y;p] (S(S n)))
        (push_environment rho n [u;v;x;y;p] (S(S(S n)))))) in H.
    assert (Old : forall i, i<n -> push_environment rho n [u;v;x;y;p] i = rho i) by (intros; now apply push_environment_old).
    assert (U0 : push_environment rho n [u;v;x;y;p] n=u)
      by (pose proof (@push_environment_at D rho n [u;v;x;y;p] 0 u eq_refl) as T; now rewrite Nat.add_0_r in T).
    assert (V0 : push_environment rho n [u;v;x;y;p] (S n)=v)
      by (replace (S n) with (n+1) by lia; eapply push_environment_at; reflexivity).
    assert (X0 : push_environment rho n [u;v;x;y;p] (S(S n))=x)
      by (replace (S(S n)) with (n+2) by lia; eapply push_environment_at; reflexivity).
    assert (Y0 : push_environment rho n [u;v;x;y;p] (S(S(S n)))=y)
      by (replace (S(S(S n))) with (n+3) by lia; eapply push_environment_at; reflexivity).
    assert (P0 : push_environment rho n [u;v;x;y;p] (S(S(S(S n))))=p)
      by (replace (S(S(S(S n)))) with (n+4) by lia; eapply push_environment_at; reflexivity).
    rewrite (Old s S0), (Old sat Sat), (Old tag Tag) in H. rewrite U0,V0,X0,Y0,P0 in H. now apply H.
  - intros H u U. rewrite b_holds_ain by lia. intros v V. rewrite update_variable_neq in V by lia.
    rewrite b_holds_ain by lia. intros x X. repeat rewrite update_variable_neq in X by lia.
    rewrite b_holds_ain by lia. intros y Y. repeat rewrite update_variable_neq in Y by lia.
    rewrite b_holds_all. intro p. rewrite atomic_core_builder_holds by lia.
    change (((RelGraph R (push_environment rho n [u;v;x;y;p] s) (push_environment rho n [u;v;x;y;p] n)
      (push_environment rho n [u;v;x;y;p] (S(S n))) /\
      RelGraph R (push_environment rho n [u;v;x;y;p] s) (push_environment rho n [u;v;x;y;p] (S n))
      (push_environment rho n [u;v;x;y;p] (S(S(S n))))) /\
      RelNode2 R (push_environment rho n [u;v;x;y;p] (S(S(S(S n)))))
        (push_environment rho n [u;v;x;y;p] tag) (push_environment rho n [u;v;x;y;p] n)
        (push_environment rho n [u;v;x;y;p] (S n))) ->
      (RelGraph R (push_environment rho n [u;v;x;y;p] sat)
        (push_environment rho n [u;v;x;y;p] (S(S(S(S n))))) (push_environment rho n [u;v;x;y;p] s) <->
       atom_truth R member (push_environment rho n [u;v;x;y;p] (S(S n)))
        (push_environment rho n [u;v;x;y;p] (S(S(S n)))))).
    assert (Old : forall i, i<n -> push_environment rho n [u;v;x;y;p] i = rho i) by (intros; now apply push_environment_old).
    assert (U0 : push_environment rho n [u;v;x;y;p] n=u)
      by (pose proof (@push_environment_at D rho n [u;v;x;y;p] 0 u eq_refl) as T; now rewrite Nat.add_0_r in T).
    assert (V0 : push_environment rho n [u;v;x;y;p] (S n)=v)
      by (replace (S n) with (n+1) by lia; eapply push_environment_at; reflexivity).
    assert (X0 : push_environment rho n [u;v;x;y;p] (S(S n))=x)
      by (replace (S(S n)) with (n+2) by lia; eapply push_environment_at; reflexivity).
    assert (Y0 : push_environment rho n [u;v;x;y;p] (S(S(S n)))=y)
      by (replace (S(S(S n))) with (n+3) by lia; eapply push_environment_at; reflexivity).
    assert (P0 : push_environment rho n [u;v;x;y;p] (S(S(S(S n))))=p)
      by (replace (S(S(S(S n)))) with (n+4) by lia; eapply push_environment_at; reflexivity).
    rewrite (Old s S0), (Old sat Sat), (Old tag Tag). rewrite U0,V0,X0,Y0,P0. intros [[G1 G2] Node]. now apply H with (u:=u) (v:=v).
Qed.
End AtomicSemantics.

Print Assumptions atomic_core_builder_holds.
Print Assumptions atomic_clause_builder_holds.
