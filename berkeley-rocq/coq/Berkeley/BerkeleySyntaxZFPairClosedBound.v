(** First-order ZF constructs a pair-closed bound by internal omega iteration,
    Replacement of uniquely determined stages, and Union. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxSets BerkeleySyntaxPairs BerkeleySyntaxFunction BerkeleySyntaxFunctionFacts
  BerkeleySyntaxOmega BerkeleySyntaxCardinal BerkeleySyntaxZFBase BerkeleySyntaxZFUnion BerkeleySyntaxZFOmega
  BerkeleySyntaxZFOrdinalOrder BerkeleySyntaxZFFormulaBound BerkeleySyntaxZFPairStage BerkeleySyntaxZFFiniteGraph
  BerkeleySyntaxZFStageRun BerkeleySyntaxZFStageAgreement BerkeleySyntaxZFStageLocal
  BerkeleySyntaxZFStageUniqueness BerkeleySyntaxZFStageNested BerkeleySyntaxZFStageNesting BerkeleySyntaxZFStageCollection.
Import ListNotations.
Section PairClosedBound.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.
Lemma zf_stage_end_increases w seed n m a b : RelOmega R w -> R n w -> R m w ->
  RelAtOrBefore R n m -> RelPairStageEnd R seed n a -> RelPairStageEnd R seed m b -> RelSubset R a b.
Proof.
  intros Omega N M [Eq|Before] EndA EndB.
  - subst m. assert (a=b) by (eapply zf_pair_stage_end_unique;eassumption). now subst a.
  - destruct EndA as [h1 [Run1 A]]. destruct EndB as [h2 [Run2 B]].
    pose proof Run2 as Run2Copy. destruct Run2 as [dom [SD [[cod [Graph Total]] [Start Edges]]]].
    assert (Ndom:R n dom) by (apply (proj2 (SD n));now left).
    destruct (Total n Ndom) as [a' [A' [At Unique]]].
    pose proof (zf_history_runs_agree R EM Model w seed n m h1 h2 Omega N M Run1 Run2Copy n N) as Agree.
    assert (Same:a=a') by (apply (Agree (or_introl eq_refl) (or_intror Before) a a' A At)). subst a'.
    pose proof (zf_history_nested R EM Model w seed m h2 Omega M Run2Copy m M) as Nested.
    apply (Nested (or_introl eq_refl) n a b Before At B).
Qed.
Lemma zf_stage_end_successor w seed n next a b : RelOmega R w -> R n w -> RelSuccessor R next n ->
  RelPairStageEnd R seed n a -> RelPairStageEnd R seed next b -> RelPairStage R a b.
Proof.
  intros Omega N Next [h1 [Run1 A]] [h2 [Run2 B]].
  assert (NextW:R next w) by (eapply omega_successor_is_member;eassumption).
  pose proof Run2 as Run2Copy. destruct Run2 as [dom [SD [[cod [Graph Total]] [Start Edges]]]].
  assert (Nnext:R n next) by (apply (proj2 (Next n));now right).
  assert (Ndom:R n dom) by (apply (proj2 (SD n));now left).
  assert (NextDom:R next dom) by (apply (proj2 (SD next));now right).
  destruct (Total n Ndom) as [a' [A' [At Unique]]].
  pose proof (zf_history_runs_agree R EM Model w seed n next h1 h2 Omega N NextW Run1 Run2Copy n N) as Agree.
  assert (Same:a=a') by (apply (Agree (or_introl eq_refl) (or_intror Nnext) a a' A At)). subst a'.
  exact (Edges n next a b Ndom NextDom Next At B).
Qed.
Theorem zf_pair_closed_bound_exists w seed : RelOmega R w ->
  exists bound, RelPairClosed R bound /\ RelSubset R seed bound.
Proof.
  intro Omega. destruct (zf_pair_stage_collection_exists R EM Model w seed Omega) as [stages Stages].
  destruct (zf_prefix_union_exists R EM Model stages) as [bound Bound].
  assert (SeedIn:R seed stages).
  { destruct Omega as [[[zero [ZeroW Zero]] Succ] Least].
    destruct (zf_stage_run_base R EM Model zero seed Zero) as [h Run].
    apply (proj2 (Stages seed)). exists zero. split; [exact ZeroW|]. exists h. split; [exact Run|].
    destruct Run as [dom [S [P [Start Edges]]]]. now apply Start. }
  exists bound. split.
  - intros x y X Y. apply (proj1 (Bound x)) in X. apply (proj1 (Bound y)) in Y.
    destruct X as [a [A Xa]]. destruct Y as [b [B Yb]].
    apply (proj1 (Stages a)) in A as [n [N EndA]].
    apply (proj1 (Stages b)) in B as [m [M EndB]].
    pose proof (zf_internal_omega_linear R EM Model w Omega n m N M) as Order.
    assert (Common : exists k stage, R k w /\ RelPairStageEnd R seed k stage /\ R x stage /\ R y stage).
    { destruct Order as [[Before|Eq]|Before].
      - exists m,b. repeat split; try assumption. eapply zf_stage_end_increases; [exact Omega|exact N|exact M|now right|exact EndA|exact EndB|exact Xa].
      - subst m. exists n,a. repeat split; try assumption.
        assert (a=b) by (eapply zf_pair_stage_end_unique;eassumption). now subst b.
      - exists n,a. repeat split; try assumption. eapply zf_stage_end_increases; [exact Omega|exact M|exact N|now right|exact EndB|exact EndA|exact Yb]. }
    destruct Common as [k [stage [K [End [Xs Ys]]]]].
    destruct Omega as [[[zero [ZeroW Zero]] Succ] Least].
    destruct (Succ k K) as [next [NextW Next]].
    destruct (zf_pair_stage_end_exists R EM Model w seed next (conj (conj (ex_intro _ zero (conj ZeroW Zero)) Succ) Least) NextW)
      as [out EndOut].
    assert (Stage : RelPairStage R stage out).
    { eapply zf_stage_end_successor; [exact (conj (conj (ex_intro _ zero (conj ZeroW Zero)) Succ) Least)|exact K|exact Next|exact End|exact EndOut]. }
    destruct (zf_prefix_kuratowski_pair_exists R EM Model x y) as [pair Pair]. exists pair. split; [|exact Pair].
    apply (proj2 (Bound pair)). exists out. split.
    + apply (proj2 (Stages out)). now exists next.
    + exact (pair_stage_contains_pair R stage out x y pair Stage Xs Ys Pair).
  - intros x X. apply (proj2 (Bound x)). now exists seed.
Qed.
End PairClosedBound.
Print Assumptions zf_stage_end_increases.
Print Assumptions zf_stage_end_successor.
Print Assumptions zf_pair_closed_bound_exists.
