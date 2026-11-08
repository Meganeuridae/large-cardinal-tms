(** Constant function graphs from a specific first-order Replacement instance. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import ProofFormula FormulaSemantics BerkeleySyntaxBase BerkeleySyntaxInterpretation
  BerkeleySyntaxPairs BerkeleySyntaxPairInject BerkeleySyntaxRepresentations BerkeleySyntaxFunction
  BerkeleySyntaxZFBase BerkeleySyntaxZFSeparation BerkeleySyntaxZFReplacement.
Import ListNotations.

Definition constant_graph_formula := instantiate_formula (fun _=>0) (fst (b_pair 2 3 4 5)).
Lemma constant_graph_formula_output_fresh : fol_free 1 constant_graph_formula=false.
Proof. vm_compute. reflexivity. Qed.

Section ConstantGraph.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Lemma constant_graph_formula_holds rho : FolHolds R rho constant_graph_formula <->
  RelPair R (rho 2) (rho 3) (rho 4).
Proof.
  change (b_holds R rho (b_pair 2 3 4) 5 <-> RelPair R (rho 2) (rho 3) (rho 4)).
  rewrite (pair_builder_holds EM) by lia. reflexivity.
Qed.

Lemma zf_constant_graph_membership w a : exists t,
  forall z, R z t <-> exists x, R x w /\ RelPair R z x a.
Proof.
  set (rho := update_variable (fun _ : nat => a) 0 w).
  assert (Func : forall input, exists out, forall z,
    FolHolds R (update_variable (update_variable rho 3 input) 2 z) constant_graph_formula -> z=out).
  { intro input. destruct (zf_prefix_kuratowski_pair_exists R EM Model input a) as [out Pair]. exists out.
    intros z H. rewrite constant_graph_formula_holds in H. unfold rho in H. cbn [update_variable] in H.
    eapply relational_pair_unique; [apply (zf_prefix_extensional R EM Model)|exact H|exact Pair]. }
  destruct (zf_prefix_formula_replacement R EM Model constant_graph_formula rho
    constant_graph_formula_output_fresh Func) as [t T]. exists t. intro z. specialize (T z).
  unfold rho in T. cbn [update_variable] in T. split.
  - intro H. destruct (proj1 T H) as [x [X P]]. exists x. split; [exact X|].
    rewrite constant_graph_formula_holds in P. cbn [update_variable] in P. exact P.
  - intros [x [X P]]. apply (proj2 T). exists x. split; [exact X|].
    rewrite constant_graph_formula_holds. cbn [update_variable]. exact P.
Qed.

Lemma constant_graph_characterization t w a :
  (forall z, R z t <-> exists x, R x w /\ RelPair R z x a) ->
  forall x y, RelGraph R t x y <-> R x w /\ y=a.
Proof.
  intros Mem x y. split.
  - intros [p [Pair In]]. apply (proj1 (Mem p)) in In. destruct In as [z [Z Other]].
    destruct (relational_pair_components R p x y z a Pair Other) as [X Y]. subst z. auto.
  - intros [X Y]. subst y. destruct (zf_prefix_kuratowski_pair_exists R EM Model x a) as [p P].
    exists p. split; [exact P|]. apply (proj2 (Mem p)). now exists x.
Qed.

Theorem zf_prefix_constant_graph w m a : R a m ->
  exists t, RelFunction R t w m /\ forall x, R x w -> RelGraph R t x a.
Proof.
  intro A. destruct (zf_constant_graph_membership w a) as [t Mem].
  pose proof (constant_graph_characterization t w a Mem) as G.
  exists t. split.
  - split.
    + intros p P. apply (proj1 (Mem p)) in P. destruct P as [x [X Pair]]. exists x,a. tauto.
    + intros x X. exists a. split; [exact A|]. split.
      * apply (proj2 (G x a)). auto.
      * intros y Y At. apply (proj1 (G x y)) in At. tauto.
  - intros x X. apply (proj2 (G x a)). auto.
Qed.
End ConstantGraph.

Print Assumptions zf_prefix_constant_graph.
