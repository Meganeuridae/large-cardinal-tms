(** Pointwise agreement of internal pair-stage histories: mathematical base
    and successor steps. The induction predicate is separately coded as a
    first-order formula before it is applied to internal omega. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxSets BerkeleySyntaxPairs BerkeleySyntaxFunction BerkeleySyntaxFunctionFacts
  BerkeleySyntaxOmega BerkeleySyntaxZFBase BerkeleySyntaxZFOmega BerkeleySyntaxZFOmegaOrder
  BerkeleySyntaxZFPairStage BerkeleySyntaxZFFiniteGraph BerkeleySyntaxZFStageRun.
Import ListNotations.
Definition RelAtOrBefore {D} (R:D->D->Prop) n k := n=k \/ R n k.
Definition RelStageAgreement {D} (R:D->D->Prop) w seed n :=
  forall k1 k2 h1 h2 a b, R k1 w -> R k2 w ->
  RelPairStageRun R h1 k1 seed -> RelPairStageRun R h2 k2 seed ->
  RelAtOrBefore R n k1 -> RelAtOrBefore R n k2 ->
  RelGraph R h1 n a -> RelGraph R h2 n b -> a=b.
Section Agreement.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.
Lemma successor_contains_at n k dom : RelSuccessor R dom k -> RelAtOrBefore R n k -> R n dom.
Proof. intros S [E|E]; apply (proj2 (S n)); [now right|now left]. Qed.
Lemma omega_successor_is_member w n dom : RelOmega R w -> R n w -> RelSuccessor R dom n -> R dom w.
Proof.
  intros [[Zero Succ] Least] N S. destruct (Succ n N) as [v [V T]].
  assert (dom=v) by (eapply zf_successor_unique; eassumption). now subst dom.
Qed.
Theorem zf_history_agreement_empty w seed e : RelEmpty R e -> RelStageAgreement R w seed e.
Proof.
  intros Empty k1 k2 h1 h2 a b K1 K2 [d1 [D1 [P1 [Z1 E1]]]] [d2 [D2 [P2 [Z2 E2]]]] A1 A2 G1 G2.
  destruct P1 as [c1 F1]. destruct P2 as [c2 F2].
  assert (A:RelGraph R h1 e seed) by now apply Z1.
  assert (B:RelGraph R h2 e seed) by now apply Z2.
  assert (a=seed) by (exact (relational_function_graph_unique R h1 d1 c1 e a seed F1 G1 A)).
  assert (b=seed) by (exact (relational_function_graph_unique R h2 d2 c2 e b seed F2 G2 B)). congruence.
Qed.
Theorem zf_history_agreement_successor w seed x y : RelOmega R w -> R x w -> RelSuccessor R y x ->
  RelStageAgreement R w seed x -> RelStageAgreement R w seed y.
Proof.
  intros Omega X Next Agree k1 k2 h1 h2 a b K1 K2 Run1 Run2 Before1 Before2 G1 G2.
  destruct Run1 as [d1 [D1 [P1 [Z1 E1]]]]. destruct Run2 as [d2 [D2 [P2 [Z2 E2]]]].
  assert (Y1:R y d1) by (eapply successor_contains_at;eassumption).
  assert (Y2:R y d2) by (eapply successor_contains_at;eassumption).
  assert (Dy1:R d1 w) by (exact (omega_successor_is_member w k1 d1 Omega K1 D1)).
  assert (Dy2:R d2 w) by (exact (omega_successor_is_member w k2 d2 Omega K2 D2)).
  assert (Trans1:RelTransitive R d1).
  { pose proof (zf_internal_natural_strong_ordinal R EM Model w Omega d1 Dy1) as [[T _] _]. exact T. }
  assert (Trans2:RelTransitive R d2).
  { pose proof (zf_internal_natural_strong_ordinal R EM Model w Omega d2 Dy2) as [[T _] _]. exact T. }
  assert (Xy:R x y) by (apply (proj2 (Next x));now right).
  assert (X1:R x d1) by (eapply Trans1;eassumption).
  assert (X2:R x d2) by (eapply Trans2;eassumption).
  destruct P1 as [c1 F1]. destruct P2 as [c2 F2].
  destruct F1 as [Graph1 Total1]. destruct F2 as [Graph2 Total2].
  destruct (Total1 x X1) as [u [U [Gx1 _]]]. destruct (Total2 x X2) as [v [V [Gx2 _]]].
  assert (B1:RelAtOrBefore R x k1).
  { apply (proj1 (D1 x)) in X1. unfold RelAtOrBefore. tauto. }
  assert (B2:RelAtOrBefore R x k2).
  { apply (proj1 (D2 x)) in X2. unfold RelAtOrBefore. tauto. }
  assert (Run1 : RelPairStageRun R h1 k1 seed).
  { exists d1. split; [exact D1|]. split; [exists c1;now split|]. now split. }
  assert (Run2 : RelPairStageRun R h2 k2 seed).
  { exists d2. split; [exact D2|]. split; [exists c2;now split|]. now split. }
  assert (Eq:u=v) by (exact (Agree k1 k2 h1 h2 u v K1 K2 Run1 Run2 B1 B2 Gx1 Gx2)).
  subst v.
  assert (Stage1:RelPairStage R u a).
  { eapply E1; [apply (proj2 (D1 x)); unfold RelAtOrBefore in B1;tauto|exact Y1|exact Next|exact Gx1|exact G1]. }
  assert (Stage2:RelPairStage R u b).
  { eapply E2; [apply (proj2 (D2 x)); unfold RelAtOrBefore in B2;tauto|exact Y2|exact Next|exact Gx2|exact G2]. }
  destruct (zf_pair_stage_exists_unique R EM Model u) as [stage [Exists Unique]].
  assert (a=stage) by (now apply Unique). assert (b=stage) by (now apply Unique). congruence.
Qed.
End Agreement.
Print Assumptions zf_history_agreement_empty.
Print Assumptions zf_history_agreement_successor.
