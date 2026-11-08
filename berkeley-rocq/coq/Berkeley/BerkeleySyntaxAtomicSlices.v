(** Equality and membership truth rows, built by specific first-order
    Separation instances and evaluated using function-graph uniqueness. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import ProofFormula FormulaSemantics BerkeleySyntaxBase BerkeleySyntaxInterpretation BerkeleySyntaxPairs
  BerkeleySyntaxFunction BerkeleySyntaxFunctionFacts BerkeleySyntaxFormulaSet BerkeleySyntaxEnvironment
  BerkeleySyntaxSatisfactionAtomic BerkeleySyntaxZFBase BerkeleySyntaxZFSeparation.
Import ListNotations.

Definition atomic_value_core_builder (member:bool) s u v x y :=
  b_and3 (b_rel s u x) (b_rel s v y) (if member then b_mem x y else b_eq x y).
Definition atomic_value_builder (member:bool) s u v m := b_ein m (fun x => b_ein m (fun y =>
  atomic_value_core_builder member s u v x y)).
Definition RelAtomicValue {D} (R:D->D->Prop) (member:bool) s u v m :=
  exists x y, R x m /\ R y m /\ RelGraph R s u x /\ RelGraph R s v y /\ atom_truth R member x y.
Definition atomic_truth_formula member :=
  instantiate_formula (fun _=>0) (fst (atomic_value_builder member 2 3 4 5 6)).
Lemma atomic_truth_output_fresh member : fol_free 1 (atomic_truth_formula member)=false.
Proof. destruct member; vm_compute; reflexivity. Qed.

Section AtomicRows.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Lemma atomic_value_core_holds member rho s u v x y n : s<n -> u<n -> v<n -> x<n -> y<n ->
  (b_holds R rho (atomic_value_core_builder member s u v x y) n <->
    RelGraph R (rho s) (rho u) (rho x) /\ RelGraph R (rho s) (rho v) (rho y) /\ atom_truth R member (rho x) (rho y)).
Proof.
  intros S0 U V X Y. unfold atomic_value_core_builder,b_and3. rewrite !(b_holds_and EM).
  assert (K1 : n <= b_next (b_rel s u x) n) by apply b_good_rel.
  assert (K2 : n <= b_next (b_and (b_rel s u x) (b_rel s v y)) n)
    by (apply b_good_and; apply b_good_rel).
  rewrite !(relation_builder_holds EM) by lia. destruct member; cbn [atom_truth];
    [rewrite b_holds_mem|rewrite b_holds_eq]; tauto.
Qed.

Lemma atomic_value_builder_holds member rho s u v m n : s<n -> u<n -> v<n -> m<n ->
  (b_holds R rho (atomic_value_builder member s u v m) n <->
   RelAtomicValue R member (rho s) (rho u) (rho v) (rho m)).
Proof.
  intros S0 U V M. unfold atomic_value_builder,RelAtomicValue. rewrite (b_holds_ein EM) by exact M. split.
  - intros [x [X H]]. rewrite (b_holds_ein EM) in H by lia. destruct H as [y [Y H]].
    rewrite atomic_value_core_holds in H by lia. rewrite update_variable_neq in Y by lia.
    set (sigma := update_variable (update_variable rho n x) (S n) y) in H.
    assert (Ss : sigma s=rho s) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Su : sigma u=rho u) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sv : sigma v=rho v) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sx : sigma n=x) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sy : sigma (S n)=y) by (unfold sigma; apply update_variable_eq).
    rewrite Ss,Su,Sv,Sx,Sy in H. exists x,y. tauto.
  - intros [x [y [X [Y H]]]]. exists x. split; [exact X|]. rewrite (b_holds_ein EM) by lia.
    exists y. split; [rewrite update_variable_neq by lia; exact Y|]. rewrite atomic_value_core_holds by lia.
    set (sigma := update_variable (update_variable rho n x) (S n) y).
    change (RelGraph R (sigma s) (sigma u) (sigma n) /\ RelGraph R (sigma s) (sigma v) (sigma (S n)) /\
      atom_truth R member (sigma n) (sigma (S n))).
    assert (Ss : sigma s=rho s) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Su : sigma u=rho u) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sv : sigma v=rho v) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sx : sigma n=x) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sy : sigma (S n)=y) by (unfold sigma; apply update_variable_eq).
    now rewrite Ss,Su,Sv,Sx,Sy.
Qed.

Lemma atomic_truth_formula_holds member rho : FolHolds R rho (atomic_truth_formula member) <->
  RelAtomicValue R member (rho 2) (rho 3) (rho 4) (rho 5).
Proof.
  change (b_holds R rho (atomic_value_builder member 2 3 4 5) 6 <->
    RelAtomicValue R member (rho 2) (rho 3) (rho 4) (rho 5)).
  rewrite atomic_value_builder_holds by lia. reflexivity.
Qed.

Theorem zf_atomic_truth_slice member e m u v : exists slice, forall s,
  R s slice <-> R s e /\ RelAtomicValue R member s u v m.
Proof.
  set (rho := update_variable (update_variable (update_variable (fun _ : nat => e) 3 u) 4 v) 5 m).
  destruct (zf_prefix_formula_separation R EM Model (atomic_truth_formula member) rho
    (atomic_truth_output_fresh member)) as [slice H]. exists slice. intro s. specialize (H s).
  rewrite atomic_truth_formula_holds in H. unfold rho in H. cbv [update_variable Nat.eqb] in H. exact H.
Qed.

Theorem atomic_value_matches_function member s w m u v a b :
  RelFunction R s w m -> R a m -> R b m -> RelGraph R s u a -> RelGraph R s v b ->
  (RelAtomicValue R member s u v m <-> atom_truth R member a b).
Proof.
  intros Func A B Ga Gb. unfold RelAtomicValue. split.
  - intros [x [y [X [Y [Gx [Gy Truth]]]]]].
    assert (x=a) by (eapply relational_function_graph_unique; [exact Func|exact Gx|exact Ga]).
    assert (y=b) by (eapply relational_function_graph_unique; [exact Func|exact Gy|exact Gb]). now subst.
  - intro Truth. exists a,b. tauto.
Qed.
End AtomicRows.

Print Assumptions zf_atomic_truth_slice.
Print Assumptions atomic_value_matches_function.
