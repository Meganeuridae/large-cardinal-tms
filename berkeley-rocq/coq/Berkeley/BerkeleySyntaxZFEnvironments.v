(** Existence of the set of all internal assignment functions. The bound is
    obtained by three Powersets of a binary Union; Separation is instantiated
    with the specific first-order formula defining a total function graph. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import ProofFormula FormulaSemantics BerkeleySyntaxBase BerkeleySyntaxInterpretation BerkeleySyntaxPairs
  BerkeleySyntaxSets BerkeleySyntaxFunction BerkeleySyntaxBijection BerkeleySyntaxEnvironment BerkeleySyntaxZFBase
  BerkeleySyntaxZFUnion BerkeleySyntaxZFPowerset BerkeleySyntaxZFSeparation.
Import ListNotations.

Definition environment_filter_formula := instantiate_formula (fun _=>0) (fst (b_function 2 3 4 5)).
Lemma environment_filter_output_fresh : fol_free 1 environment_filter_formula=false.
Proof. vm_compute. reflexivity. Qed.

Section EnvironmentSet.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Lemma environment_filter_holds rho : FolHolds R rho environment_filter_formula <->
  RelFunction R (rho 2) (rho 3) (rho 4).
Proof.
  change (b_holds R rho (b_function 2 3 4) 5 <-> RelFunction R (rho 2) (rho 3) (rho 4)).
  rewrite (function_builder_holds EM) by lia. reflexivity.
Qed.

Lemma pair_in_powerset_bound a b bound p1 p2 x y q :
  RelBinaryUnion R bound a b -> RelPowerset R p1 bound -> RelPowerset R p2 p1 ->
  R x a -> R y b -> RelPair R q x y -> R q p2.
Proof.
  intros B P1 P2 X Y [u [v [U [V Q]]]]. apply (proj2 (P2 q)). intros t T.
  apply (proj1 (Q t)) in T. destruct T as [T|T]; subst t.
  - apply (proj2 (P1 u)). intros z Z. apply (proj1 (U z)) in Z. subst z.
    apply (proj2 (B x)). now left.
  - apply (proj2 (P1 v)). intros z Z. apply (proj1 (V z)) in Z. destruct Z as [Z|Z]; subst z.
    + apply (proj2 (B x)). now left.
    + apply (proj2 (B y)). now right.
Qed.

Theorem zf_prefix_environments_exist w m : exists e, RelEnvironments R e w m.
Proof.
  destruct (zf_prefix_binary_union_exists R EM Model w m) as [bound B].
  destruct (zf_prefix_powerset_exists R EM Model bound) as [p1 P1].
  destruct (zf_prefix_powerset_exists R EM Model p1) as [p2 P2].
  destruct (zf_prefix_powerset_exists R EM Model p2) as [p3 P3].
  assert (AllBound : forall f, RelFunction R f w m -> R f p3).
  { intros f [Graph Total]. apply (proj2 (P3 f)). intros q Q.
    destruct (Graph q Q) as [x [y [X [Y Pair]]]].
    eapply pair_in_powerset_bound; eassumption. }
  set (rho := update_variable (update_variable (update_variable (fun _ : nat => m) 0 p3) 3 w) 4 m).
  destruct (zf_prefix_formula_separation R EM Model environment_filter_formula rho environment_filter_output_fresh) as [e E].
  exists e. intro f. specialize (E f). rewrite environment_filter_holds in E. unfold rho in E.
  cbv [update_variable Nat.eqb] in E. split.
  - intro In. exact (proj2 (proj1 E In)).
  - intro Func. apply (proj2 E). split; [now apply AllBound|exact Func].
Qed.
End EnvironmentSet.

Print Assumptions zf_prefix_environments_exist.
