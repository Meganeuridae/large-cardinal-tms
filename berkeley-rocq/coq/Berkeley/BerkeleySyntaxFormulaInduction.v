(** Induction over all internal formula objects for any *first-order definable*
    property. The proof uses one instance of the literal Separation schema and
    the least-closure clause, not external well-foundedness or arbitrary
    higher-order comprehension. *)
From Stdlib Require Import Lists.List Arith.Arith.
From Berkeley Require Import ProofFormula FormulaSemantics BerkeleySyntaxPairs BerkeleySyntaxFormulaSet
  BerkeleySyntaxZFBase BerkeleySyntaxZFSeparation.
Import ListNotations.

Definition RelFormulaProperty {D} (R:D->D->Prop) (p:fol_formula) rho z :=
  FolHolds R (update_variable rho 2 z) p.

Section DefinableInduction.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Theorem zf_internal_formula_induction f w te tm tn ti ta (property:fol_formula) rho :
  rho 0=f -> fol_free 1 property=false -> RelFormulas R f w te tm tn ti ta ->
  (forall x y p, R x w -> R y w -> R p f -> RelNode2 R p te x y -> RelFormulaProperty R property rho p) ->
  (forall x y p, R x w -> R y w -> R p f -> RelNode2 R p tm x y -> RelFormulaProperty R property rho p) ->
  (forall q p, R q f -> RelFormulaProperty R property rho q -> R p f -> RelPair R p tn q -> RelFormulaProperty R property rho p) ->
  (forall q r p, R q f -> RelFormulaProperty R property rho q -> R r f -> RelFormulaProperty R property rho r ->
    R p f -> RelNode2 R p ti q r -> RelFormulaProperty R property rho p) ->
  (forall x q p, R x w -> R q f -> RelFormulaProperty R property rho q -> R p f ->
    RelNode2 R p ta x q -> RelFormulaProperty R property rho p) ->
  forall p, R p f -> RelFormulaProperty R property rho p.
Proof.
  intros Base Fresh [[CE [CM [CN [CI CA]]]] Least] PE PM PN PI PA.
  destruct (zf_prefix_formula_separation R EM Model property rho Fresh) as [g Sep].
  assert (S : forall p, R p g <-> R p f /\ RelFormulaProperty R property rho p).
  { intro p. specialize (Sep p). rewrite Base in Sep. exact Sep. }
  assert (Closed : RelClosedFormulas R g w te tm tn ti ta).
  { unfold RelClosedFormulas,RelNodeClosure,RelUnaryClosure. split.
    - intros x y X Y. destruct (CE x y X Y) as [p [Pf Node]]. exists p. split; [|exact Node].
      apply (proj2 (S p)). split; [exact Pf|]. exact (PE x y p X Y Pf Node).
    - split.
      + intros x y X Y. destruct (CM x y X Y) as [p [Pf Node]]. exists p. split; [|exact Node].
        apply (proj2 (S p)). split; [exact Pf|]. exact (PM x y p X Y Pf Node).
      + split.
        * intros q Q. pose proof (proj1 (S q) Q) as [Qf Qp]. destruct (CN q Qf) as [p [Pf Pair]].
          exists p. split; [|exact Pair]. apply (proj2 (S p)). split; [exact Pf|]. exact (PN q p Qf Qp Pf Pair).
        * split.
          -- intros q r Q T. pose proof (proj1 (S q) Q) as [Qf Qp].
             pose proof (proj1 (S r) T) as [Rf Rp]. destruct (CI q r Qf Rf) as [p [Pf Node]].
             exists p. split; [|exact Node]. apply (proj2 (S p)). split; [exact Pf|]. exact (PI q r p Qf Qp Rf Rp Pf Node).
          -- intros x q X Q. pose proof (proj1 (S q) Q) as [Qf Qp].
             destruct (CA x q X Qf) as [p [Pf Node]]. exists p. split; [|exact Node].
             apply (proj2 (S p)). split; [exact Pf|]. exact (PA x q p X Qf Qp Pf Node). }
  intros p Pf. specialize (Least g Closed p Pf). exact (proj2 (proj1 (S p) Least)).
Qed.
End DefinableInduction.

Print Assumptions zf_internal_formula_induction.
