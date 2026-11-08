(** Function composition via one explicit first-order Replacement instance. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import ProofFormula FormulaSemantics BerkeleySyntaxPairs BerkeleySyntaxPairInject BerkeleySyntaxRepresentations
  BerkeleySyntaxFunction BerkeleySyntaxFunctionFacts BerkeleySyntaxElementary BerkeleySyntaxZFBase BerkeleySyntaxZFReplacement
  BerkeleySyntaxZFCompositionFormula.
Import ListNotations.

Section Composition.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Lemma zf_composition_membership s j w m : RelFunction R s w m -> RelFunction R j m m ->
  exists t, forall z, R z t <-> exists input mid y,
    R input w /\ RelGraph R s input mid /\ RelGraph R j mid y /\ RelPair R z input y.
Proof.
  intros S J.
  set (rho := update_variable (update_variable (update_variable (update_variable (fun _ : nat => m) 0 w) 4 s) 5 j) 6 w).
  assert (Func : forall input, exists out, forall z,
    FolHolds R (update_variable (update_variable rho 3 input) 2 z) composition_formula -> z=out).
  { intro input. destruct (EM (R input w)) as [In|NotIn].
    - destruct S as [Sgraph Stotal]. destruct (Stotal input In) as [mid [M [Sval _]]].
      destruct J as [Jgraph Jtotal]. destruct (Jtotal mid M) as [y [Y [Jval _]]].
      destruct (zf_prefix_kuratowski_pair_exists R EM Model input y) as [out Pair]. exists out. intros z H.
      rewrite (composition_formula_holds R EM) in H. unfold rho in H. cbv [update_variable Nat.eqb] in H.
      destruct H as [_ [mid' [y' [Sval' [Jval' Pair']]]]].
      assert (mid'=mid) by (exact (@relational_function_graph_unique D R s w m input mid' mid (conj Sgraph Stotal) Sval' Sval)).
      subst mid'. assert (y'=y) by (exact (@relational_function_graph_unique D R j m m mid y' y (conj Jgraph Jtotal) Jval' Jval)).
      subst y'. eapply relational_pair_unique; [apply (zf_prefix_extensional R EM Model)|exact Pair'|exact Pair].
    - exists w. intros z H. rewrite (composition_formula_holds R EM) in H. unfold rho in H.
      cbv [update_variable Nat.eqb] in H. tauto. }
  destruct (zf_prefix_formula_replacement R EM Model composition_formula rho
    composition_formula_output_fresh Func) as [t T]. exists t. intro z. specialize (T z).
  unfold rho in T. cbv [update_variable Nat.eqb] in T. split.
  - intro H. destruct (proj1 T H) as [u [U C]]. rewrite (composition_formula_holds R EM) in C.
    cbv [update_variable Nat.eqb] in C. destruct C as [_ [mid [y [A [B P]]]]]. exists u,mid,y. tauto.
  - intros [u [mid [y [U [A [B P]]]]]]. apply (proj2 T). exists u. split; [exact U|].
    rewrite (composition_formula_holds R EM). cbv [update_variable Nat.eqb]. split; [exact U|]. now exists mid,y.
Qed.

Lemma composition_graph_characterization t s j w m : RelFunction R s w m -> RelFunction R j m m ->
  (forall z, R z t <-> exists input mid y,
    R input w /\ RelGraph R s input mid /\ RelGraph R j mid y /\ RelPair R z input y) ->
  forall x y, RelGraph R t x y <-> R x w /\ exists mid, RelGraph R s x mid /\ RelGraph R j mid y.
Proof.
  intros S J Mem x y. split.
  - intros [p [Pair In]]. apply (proj1 (Mem p)) in In. destruct In as [u [mid [v [U [A [B Other]]]]]].
    destruct (relational_pair_components R p x y u v Pair Other) as [X Y]. subst u v. split; [exact U|]. now exists mid.
  - intros [X [mid [A B]]]. destruct (zf_prefix_kuratowski_pair_exists R EM Model x y) as [p Pair].
    exists p. split; [exact Pair|]. apply (proj2 (Mem p)). now exists x,mid,y.
Qed.

Theorem zf_prefix_graph_composition s j w m : RelFunction R s w m -> RelFunction R j m m ->
  exists t, RelFunction R t w m /\ RelImageEnvironment R j s t w m.
Proof.
  intros S J. destruct (zf_composition_membership s j w m S J) as [t Mem].
  pose proof (composition_graph_characterization t s j w m S J Mem) as G.
  exists t. split.
  - split.
    + intros p P. apply (proj1 (Mem p)) in P. destruct P as [x [mid [y [X [Sval [Jval Pair]]]]]].
      pose proof (relational_function_graph_range R j m m mid y J Jval) as [_ Y]. now exists x,y.
    + intros x X. destruct S as [Sgraph Stotal]. destruct (Stotal x X) as [mid [M [Sval _]]].
      destruct J as [Jgraph Jtotal]. destruct (Jtotal mid M) as [y [Y [Jval _]]]. exists y. split; [exact Y|]. split.
      * apply (proj2 (G x y)). split; [exact X|]. now exists mid.
      * intros z Z At. apply (proj1 (G x z)) in At. destruct At as [_ [mid' [Sval' Jval']]].
        assert (mid'=mid) by (exact (@relational_function_graph_unique D R s w m x mid' mid (conj Sgraph Stotal) Sval' Sval)).
        subst mid'. exact (@relational_function_graph_unique D R j m m mid z y (conj Jgraph Jtotal) Jval' Jval).
  - intros x mid y X M Y Sval Jval. apply (proj2 (G x y)). split; [exact X|]. now exists mid.
Qed.
End Composition.

Print Assumptions zf_prefix_graph_composition.
