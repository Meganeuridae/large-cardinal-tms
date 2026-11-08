(** Add a first-order definable row of truth values to a partial graph. The
    row graph is obtained by a single explicit Replacement instance. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import ProofFormula FormulaSemantics BerkeleySyntaxBase BerkeleySyntaxInterpretation BerkeleySyntaxPairs
  BerkeleySyntaxPairInject BerkeleySyntaxRepresentations BerkeleySyntaxSets BerkeleySyntaxZFBase BerkeleySyntaxZFUnion
  BerkeleySyntaxZFSeparation BerkeleySyntaxZFReplacement BerkeleySyntaxPartialUnion.
Import ListNotations.

Definition truth_row_formula := instantiate_formula (fun _=>0) (fst (b_pair 2 4 3 5)).
Lemma truth_row_output_fresh : fol_free 1 truth_row_formula=false.
Proof. vm_compute. reflexivity. Qed.

Section TruthSlice.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Lemma truth_row_formula_holds rho : FolHolds R rho truth_row_formula <->
  RelPair R (rho 2) (rho 4) (rho 3).
Proof.
  change (b_holds R rho (b_pair 2 4 3) 5 <-> RelPair R (rho 2) (rho 4) (rho 3)).
  rewrite (pair_builder_holds EM) by lia. reflexivity.
Qed.

Lemma zf_truth_row_membership p slice : exists h,
  forall z, R z h <-> exists s, R s slice /\ RelPair R z p s.
Proof.
  set (rho := update_variable (fun _ : nat => p) 0 slice).
  assert (Func : forall input, exists out, forall z,
    FolHolds R (update_variable (update_variable rho 3 input) 2 z) truth_row_formula -> z=out).
  { intro input. destruct (zf_prefix_kuratowski_pair_exists R EM Model p input) as [out Pair]. exists out.
    intros z H. rewrite truth_row_formula_holds in H. unfold rho in H. cbv [update_variable Nat.eqb] in H.
    eapply relational_pair_unique; [apply (zf_prefix_extensional R EM Model)|exact H|exact Pair]. }
  destruct (zf_prefix_formula_replacement R EM Model truth_row_formula rho truth_row_output_fresh Func) as [h H].
  exists h. intro z. specialize (H z). unfold rho in H. cbv [update_variable Nat.eqb] in H. split.
  - intro Z. destruct (proj1 H Z) as [s [S Pair]]. exists s. split; [exact S|].
    rewrite truth_row_formula_holds in Pair. cbv [update_variable Nat.eqb] in Pair. exact Pair.
  - intros [s [S Pair]]. apply (proj2 H). exists s. split; [exact S|].
    rewrite truth_row_formula_holds. cbv [update_variable Nat.eqb]. exact Pair.
Qed.

Lemma zf_truth_row_graph p slice : exists h, forall q s,
  RelGraph R h q s <-> q=p /\ R s slice.
Proof.
  destruct (zf_truth_row_membership p slice) as [h H]. exists h. intros q s. split.
  - intros [z [Pair In]]. apply (proj1 (H z)) in In. destruct In as [t [T Other]].
    destruct (relational_pair_components R z q s p t Pair Other) as [Q S]. subst t. now split.
  - intros [Q S]. subst q. destruct (zf_prefix_kuratowski_pair_exists R EM Model p s) as [z Pair].
    exists z. split; [exact Pair|]. apply (proj2 (H z)). now exists s.
Qed.

Theorem zf_add_truth_slice h g e p slice : RelTruthGraphBound R h g e -> ~R p g -> RelSubset R slice e ->
  exists g' h',
    (forall q, R q g' <-> R q g \/ q=p) /\
    (forall q s, RelGraph R h' q s <-> RelGraph R h q s \/ (q=p /\ R s slice)) /\
    (forall q s, R q g -> (RelGraph R h' q s <-> RelGraph R h q s)) /\
    (forall s, RelGraph R h' p s <-> R s slice) /\ RelTruthGraphBound R h' g' e.
Proof.
  intros Bound NotIn Slice. destruct (zf_prefix_singleton_exists R EM Model p) as [one One].
  destruct (zf_prefix_binary_union_exists R EM Model g one) as [g' G].
  destruct (zf_truth_row_graph p slice) as [row Row].
  destruct (zf_prefix_binary_union_exists R EM Model h row) as [h' H].
  assert (G' : forall q, R q g' <-> R q g \/ q=p) by (intro q; rewrite (G q),(One q); reflexivity).
  assert (H' : forall q s, RelGraph R h' q s <-> RelGraph R h q s \/ (q=p /\ R s slice)).
  { intros q s. rewrite (graph_of_binary_union R h' h row H),(Row q s). reflexivity. }
  exists g',h'. split; [exact G'|]. split; [exact H'|]. split.
  - intros q s In. rewrite (H' q s). split; [|now left]. intros [Old|[Eq _]]; [exact Old|].
    subst q. contradiction.
  - split.
    + intro s. rewrite (H' p s). split; [|intro S; right; now split].
      intros [Old|[_ S]]; [exfalso; apply NotIn; exact (proj1 (Bound p s Old))|exact S].
    + intros q s At. apply (proj1 (H' q s)) in At. destruct At as [Old|[Eq S]].
      * destruct (Bound q s Old) as [Q Se]. split; [apply (proj2 (G' q)); now left|exact Se].
      * split; [apply (proj2 (G' q)); now right|now apply Slice].
Qed.
End TruthSlice.

Print Assumptions zf_truth_row_graph.
Print Assumptions zf_add_truth_slice.
