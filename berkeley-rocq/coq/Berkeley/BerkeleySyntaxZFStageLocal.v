(** Agreement for any two fixed internal histories, a first-order property
    with those histories and endpoints as parameters. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxSets BerkeleySyntaxPairs BerkeleySyntaxFunction BerkeleySyntaxFunctionFacts
  BerkeleySyntaxOmega BerkeleySyntaxZFBase BerkeleySyntaxZFOmega BerkeleySyntaxZFOmegaOrder
  BerkeleySyntaxZFPairStage BerkeleySyntaxZFFiniteGraph BerkeleySyntaxZFStageRun BerkeleySyntaxZFStageAgreement.
Import ListNotations.
Definition RelLocalAgreement {D} (R:D->D->Prop) h1 h2 k1 k2 n :=
  RelAtOrBefore R n k1 -> RelAtOrBefore R n k2 ->
  forall a b, RelGraph R h1 n a -> RelGraph R h2 n b -> a=b.
Section LocalAgreement.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.
Theorem zf_local_agreement_empty seed k1 k2 h1 h2 e :
  RelEmpty R e -> RelPairStageRun R h1 k1 seed -> RelPairStageRun R h2 k2 seed ->
  RelLocalAgreement R h1 h2 k1 k2 e.
Proof.
  intros Empty [d1 [D1 [[c1 F1] [Z1 E1]]]] [d2 [D2 [[c2 F2] [Z2 E2]]]] B1 B2 a b G1 G2.
  assert (A:RelGraph R h1 e seed) by now apply Z1.
  assert (B:RelGraph R h2 e seed) by now apply Z2.
  assert (a=seed) by (exact (relational_function_graph_unique R h1 d1 c1 e a seed F1 G1 A)).
  assert (b=seed) by (exact (relational_function_graph_unique R h2 d2 c2 e b seed F2 G2 B)). congruence.
Qed.
Theorem zf_local_agreement_successor w seed k1 k2 h1 h2 x y :
  RelOmega R w -> R k1 w -> R k2 w -> RelPairStageRun R h1 k1 seed -> RelPairStageRun R h2 k2 seed ->
  R x w -> RelSuccessor R y x -> RelLocalAgreement R h1 h2 k1 k2 x -> RelLocalAgreement R h1 h2 k1 k2 y.
Proof.
  intros Omega K1 K2 [d1 [D1 [[c1 F1] [Z1 E1]]]] [d2 [D2 [[c2 F2] [Z2 E2]]]] X Next Agree Before1 Before2 a b G1 G2.
  assert (Y1:R y d1) by (eapply successor_contains_at;eassumption).
  assert (Y2:R y d2) by (eapply successor_contains_at;eassumption).
  assert (Dy1:R d1 w) by (exact (omega_successor_is_member R EM Model w k1 d1 Omega K1 D1)).
  assert (Dy2:R d2 w) by (exact (omega_successor_is_member R EM Model w k2 d2 Omega K2 D2)).
  assert (Trans1:RelTransitive R d1).
  { pose proof (zf_internal_natural_strong_ordinal R EM Model w Omega d1 Dy1) as [[T _] _]. exact T. }
  assert (Trans2:RelTransitive R d2).
  { pose proof (zf_internal_natural_strong_ordinal R EM Model w Omega d2 Dy2) as [[T _] _]. exact T. }
  assert (Xy:R x y) by (apply (proj2 (Next x));now right).
  assert (X1:R x d1) by (eapply Trans1;eassumption).
  assert (X2:R x d2) by (eapply Trans2;eassumption).
  destruct F1 as [Graph1 Total1]. destruct F2 as [Graph2 Total2].
  destruct (Total1 x X1) as [u [U [Gx1 _]]]. destruct (Total2 x X2) as [v [V [Gx2 _]]].
  assert (B1:RelAtOrBefore R x k1).
  { apply (proj1 (D1 x)) in X1. unfold RelAtOrBefore. tauto. }
  assert (B2:RelAtOrBefore R x k2).
  { apply (proj1 (D2 x)) in X2. unfold RelAtOrBefore. tauto. }
  assert (Eq:u=v) by (exact (Agree B1 B2 u v Gx1 Gx2)). subst v.
  assert (Stage1:RelPairStage R u a).
  { eapply E1; [apply (proj2 (D1 x)); unfold RelAtOrBefore in B1;tauto|exact Y1|exact Next|exact Gx1|exact G1]. }
  assert (Stage2:RelPairStage R u b).
  { eapply E2; [apply (proj2 (D2 x)); unfold RelAtOrBefore in B2;tauto|exact Y2|exact Next|exact Gx2|exact G2]. }
  destruct (zf_pair_stage_exists_unique R EM Model u) as [stage [Exists Unique]].
  assert (a=stage) by (now apply Unique). assert (b=stage) by (now apply Unique). congruence.
Qed.
End LocalAgreement.
Print Assumptions zf_local_agreement_empty.
Print Assumptions zf_local_agreement_successor.
