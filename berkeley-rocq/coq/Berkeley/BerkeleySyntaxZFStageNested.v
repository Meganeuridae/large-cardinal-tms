(** Monotonicity of a fixed internal stage history. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxSets BerkeleySyntaxPairs BerkeleySyntaxFunction BerkeleySyntaxFunctionFacts
  BerkeleySyntaxOmega BerkeleySyntaxZFBase BerkeleySyntaxZFOmega BerkeleySyntaxZFOmegaOrder
  BerkeleySyntaxZFPairStage BerkeleySyntaxZFFiniteGraph BerkeleySyntaxZFStageRun BerkeleySyntaxZFStageAgreement.
Import ListNotations.
Definition RelNestedAt {D} (R:D->D->Prop) h k n := RelAtOrBefore R n k ->
  forall i a b, R i n -> RelGraph R h i a -> RelGraph R h n b -> RelSubset R a b.
Section Nested.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.
Theorem zf_nested_empty h k e : RelEmpty R e -> RelNestedAt R h k e.
Proof. intros Empty Before i a b I. exfalso. exact (Empty i I). Qed.
Theorem zf_nested_successor w seed k h x y : RelOmega R w -> R k w -> RelPairStageRun R h k seed ->
  R x w -> RelSuccessor R y x -> RelNestedAt R h k x -> RelNestedAt R h k y.
Proof.
  intros Omega K [dom [SD [[cod [Graph Total]] [Start Edges]]]] X Next IH Before i a b I Gi Gy.
  assert (Ydom:R y dom) by (eapply successor_contains_at;eassumption).
  assert (DomW:R dom w) by (exact (omega_successor_is_member R EM Model w k dom Omega K SD)).
  assert (Trans:RelTransitive R dom).
  { pose proof (zf_internal_natural_strong_ordinal R EM Model w Omega dom DomW) as [[T _] _]. exact T. }
  assert (Xy:R x y) by (apply (proj2 (Next x));now right).
  assert (Xdom:R x dom) by (eapply Trans;eassumption).
  destruct (Total x Xdom) as [middle [M [Gx U]]].
  assert (Stage:RelPairStage R middle b) by (exact (Edges x y middle b Xdom Ydom Next Gx Gy)).
  assert (Sub:RelSubset R middle b) by (now apply (pair_stage_monotone R middle b)).
  apply (proj1 (Next i)) in I. destruct I as [Ix|Eq].
  - assert (BeforeX:RelAtOrBefore R x k).
    { apply (proj1 (SD x)) in Xdom. unfold RelAtOrBefore. tauto. }
    assert (AM:RelSubset R a middle) by (eapply IH;eassumption).
    intros v V. apply Sub,AM,V.
  - subst i. assert (a=middle) by (exact (relational_function_graph_unique R h dom cod x a middle (conj Graph Total) Gi Gx)).
    now subst a.
Qed.
End Nested.
Print Assumptions zf_nested_empty.
Print Assumptions zf_nested_successor.
