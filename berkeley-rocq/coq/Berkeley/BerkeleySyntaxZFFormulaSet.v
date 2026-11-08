(** First-order construction of the least formula set from an internally
    closed bound. Existence of that bound remains a separate obligation. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import ProofFormula FormulaSemantics BerkeleySyntaxBase
  BerkeleySyntaxSatisfaction BerkeleySyntaxInterpretation BerkeleySyntaxSets
  BerkeleySyntaxPairs BerkeleySyntaxFormulaSet BerkeleySyntaxRepresentations
  BerkeleySyntaxZFBase BerkeleySyntaxZFSeparation.
Import ListNotations.

Definition formula_intersection_builder := b_all (fun g =>
  b_imp (b_closed_formulas g 3 4 5 6 7 8) (b_mem 2 g)).
Definition formula_intersection_formula := instantiate_formula (fun _=>0)
  (fst (formula_intersection_builder 9)).
Lemma formula_intersection_fresh : fol_free 1 formula_intersection_formula=false.
Proof. vm_compute. reflexivity. Qed.

Section LeastFormulaSet.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Lemma formula_intersection_holds rho :
  FolHolds R rho formula_intersection_formula <->
  forall g, RelClosedFormulas R g (rho 3) (rho 4) (rho 5) (rho 6) (rho 7) (rho 8) -> R (rho 2) g.
Proof.
  change (FolHolds R rho formula_intersection_formula) with (b_holds R rho formula_intersection_builder 9).
  unfold formula_intersection_builder. rewrite b_holds_all.
  setoid_rewrite b_holds_imp.
  setoid_rewrite (closed_formulas_builder_holds EM D R) at 1.
  all: try lia.
  setoid_rewrite b_holds_mem.
  cbv [update_variable Nat.eqb]. reflexivity.
Qed.

Theorem zf_prefix_formula_set_from_closed bound w te tm tn ti ta :
  RelClosedFormulas R bound w te tm tn ti ta ->
  exists f, RelFormulas R f w te tm tn ti ta.
Proof.
  intro Closed.
  set (rho := fun n => match n with
    | 0 => bound | 3 => w | 4 => te | 5 => tm | 6 => tn | 7 => ti | _ => ta end).
  destruct (zf_prefix_formula_separation R EM Model formula_intersection_formula rho
    formula_intersection_fresh) as [f F].
  assert (Spec : forall z, R z f <-> R z bound /\
    forall g, RelClosedFormulas R g w te tm tn ti ta -> R z g).
  { intro z. specialize (F z). rewrite formula_intersection_holds in F.
    cbv [rho update_variable Nat.eqb] in F. exact F. }
  assert (Sub : forall g, RelClosedFormulas R g w te tm tn ti ta -> RelSubset R f g).
  { intros g G z Z. exact (proj2 (proj1 (Spec z) Z) g G). }
  assert (InBound : RelSubset R f bound) by now apply Sub.
  pose proof (zf_prefix_extensional R EM Model) as Ext.
  destruct Closed as [BE [BM [BN [BI BA]]]].
  exists f. split; [|exact Sub]. unfold RelClosedFormulas.
  split.
  - intros x y X Y. destruct (BE x y X Y) as [z [Z Node]]. exists z. split; [|exact Node].
    apply (proj2 (Spec z)). split; [exact Z|]. intros g [GE _].
    destruct (GE x y X Y) as [z' [Z' Node']].
    assert (z=z') by (eapply relational_node_unique; eassumption). now subst z'.
  - split.
    + intros x y X Y. destruct (BM x y X Y) as [z [Z Node]]. exists z. split; [|exact Node].
      apply (proj2 (Spec z)). split; [exact Z|]. intros g [_ [GM _]].
      destruct (GM x y X Y) as [z' [Z' Node']].
      assert (z=z') by (eapply relational_node_unique; eassumption). now subst z'.
    + split.
      * intros p P. destruct (BN p (InBound p P)) as [q [Q Pair]]. exists q. split; [|exact Pair].
        apply (proj2 (Spec q)). split; [exact Q|]. intros g G.
        pose proof (Sub g G p P) as GP. destruct G as [_ [_ [GN _]]].
        destruct (GN p GP) as [q' [Q' Pair']].
        assert (q=q') by (eapply relational_pair_unique; eassumption). now subst q'.
      * split.
        -- intros x y X Y. destruct (BI x y (InBound x X) (InBound y Y)) as [z [Z Node]].
           exists z. split; [|exact Node]. apply (proj2 (Spec z)). split; [exact Z|]. intros g G.
           pose proof (Sub g G x X) as GX. pose proof (Sub g G y Y) as GY.
           destruct G as [_ [_ [_ [GI _]]]]. destruct (GI x y GX GY) as [z' [Z' Node']].
           assert (z=z') by (eapply relational_node_unique; eassumption). now subst z'.
        -- intros x y X Y. destruct (BA x y X (InBound y Y)) as [z [Z Node]].
           exists z. split; [|exact Node]. apply (proj2 (Spec z)). split; [exact Z|]. intros g G.
           pose proof (Sub g G y Y) as GY. destruct G as [_ [_ [_ [_ GA]]]].
           destruct (GA x y X GY) as [z' [Z' Node']].
           assert (z=z') by (eapply relational_node_unique; eassumption). now subst z'.
Qed.
End LeastFormulaSet.

Print Assumptions formula_intersection_holds.
Print Assumptions zf_prefix_formula_set_from_closed.
