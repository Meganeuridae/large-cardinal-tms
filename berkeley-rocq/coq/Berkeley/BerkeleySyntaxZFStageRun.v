(** Finite stage-run semantics and local induction steps. The later existence
    theorem will apply first-order internal omega induction to a formula coding
    this relation; no external induction over internal elements is used here. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxSets BerkeleySyntaxPairs BerkeleySyntaxFunction BerkeleySyntaxFunctionFacts
  BerkeleySyntaxZFBase BerkeleySyntaxZFUnion BerkeleySyntaxZFFoundation BerkeleySyntaxZFPaths BerkeleySyntaxZFOmega
  BerkeleySyntaxZFPairStage BerkeleySyntaxZFFiniteGraph.
Import ListNotations.
Definition RelPairStageRun {D} (R:D->D->Prop) h n seed := exists dom,
  RelSuccessor R dom n /\ RelPartialFunction R h dom /\
  (forall zero, RelEmpty R zero -> RelGraph R h zero seed) /\
  (forall i j a b, R i dom -> R j dom -> RelSuccessor R j i ->
    RelGraph R h i a -> RelGraph R h j b -> RelPairStage R a b).
Section StageRuns.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.
Lemma zf_successor_exists a : exists b, RelSuccessor R b a.
Proof.
  destruct (zf_prefix_singleton_exists R EM Model a) as [one One].
  destruct (zf_prefix_binary_union_exists R EM Model a one) as [b B]. exists b. intro x.
  rewrite (B x),(One x). reflexivity.
Qed.
Lemma zf_successor_injective a b s : RelSuccessor R s a -> RelSuccessor R s b -> a=b.
Proof.
  intros A B. destruct (EM (a=b)) as [E|N]; [exact E|].
  assert (Ab : R a b).
  { assert (R a s) by (apply (proj2 (A a)); now right). apply (proj1 (B a)) in H. destruct H; [assumption|congruence]. }
  assert (Ba : R b a).
  { assert (R b s) by (apply (proj2 (B b)); now right). apply (proj1 (A b)) in H. destruct H; [assumption|congruence]. }
  exfalso. eapply (zf_no_finite_membership_cycle R EM Model 2 a); [lia|].
  eapply path_step; [exact Ab|]. eapply path_step; [exact Ba|constructor].
Qed.
Lemma zf_stage_run_base zero seed : RelEmpty R zero -> exists h, RelPairStageRun R h zero seed.
Proof.
  intro Empty. destruct (zf_prefix_singleton_exists R EM Model zero) as [dom Dom].
  assert (Succ : RelSuccessor R dom zero).
  { intro x. rewrite (Dom x). specialize (Empty x). tauto. }
  destruct (zf_prefix_kuratowski_pair_exists R EM Model zero seed) as [p Pair].
  destruct (zf_prefix_singleton_exists R EM Model p) as [h Hmem].
  destruct (zf_prefix_singleton_exists R EM Model seed) as [cod Cod].
  assert (Function : RelFunction R h dom cod).
  { split.
    - intros q Q. apply (proj1 (Hmem q)) in Q. subst q. exists zero,seed. repeat split; try assumption;
        [apply (proj2 (Dom zero))|apply (proj2 (Cod seed))]; reflexivity.
    - intros x X. apply (proj1 (Dom x)) in X. subst x. exists seed. split; [apply (proj2 (Cod seed));reflexivity|].
      split; [exists p;split;[exact Pair|apply (proj2 (Hmem p));reflexivity]|].
      intros y Y _. now apply (proj1 (Cod y)). }
  exists h,dom. split; [exact Succ|]. split; [exists cod;exact Function|]. split.
  - intros other Other. assert (other=zero) by (eapply zf_empty_unique; eassumption). subst other.
    exists p. split; [exact Pair|apply (proj2 (Hmem p));reflexivity].
  - intros i j a b I J Step _ _. apply (proj1 (Dom i)) in I. apply (proj1 (Dom j)) in J. subst i j.
    exfalso. apply (Empty zero),(proj2 (Step zero)). now right.
Qed.
Theorem zf_stage_run_extend h n next seed :
  RelPairStageRun R h n seed -> RelSuccessor R next n ->
  exists h', RelPairStageRun R h' next seed.
Proof.
  intros [dom [SD [PF [Start Edges]]]] Next.
  assert (DomEq : dom=next) by (eapply zf_successor_unique; eassumption). subst dom.
  destruct PF as [cod F]. destruct F as [Graph Total].
  assert (Nin : R n next) by (apply (proj2 (Next n));now right).
  destruct (Total n Nin) as [a [A [At Unique]]].
  destruct (zf_pair_stage_exists_unique R EM Model a) as [value [Stage UniqueStage]].
  destruct (zf_successor_exists next) as [newdom NewDom].
  destruct (zf_function_extend_successor R EM Model h next cod newdom value (conj Graph Total) NewDom)
    as [h' [cod' [F' G]]].
  assert (Nonself : ~R next next) by apply (zf_prefix_membership_irreflexive R EM Model).
  assert (OldOnly : forall i v, R i next -> RelGraph R h' i v -> RelGraph R h i v).
  { intros i v I V. apply (proj1 (G i v)) in V. destruct V as [V|[Eq _]]; [exact V|subst;contradiction]. }
  assert (NewOnly : forall v, RelGraph R h' next v -> v=value).
  { intros v V. apply (proj1 (G next v)) in V. destruct V as [V|[_ Eq]]; [|exact Eq].
    destruct (relational_function_graph_range R h next cod next v (conj Graph Total) V) as [Bad _]. contradiction. }
  exists h',newdom. split; [exact NewDom|]. split; [now exists cod'|]. split.
  - intros zero Zero. apply (proj2 (G zero seed)). left. now apply Start.
  - intros i j u v I J Step Gi Gj. apply (proj1 (NewDom i)) in I. apply (proj1 (NewDom j)) in J.
    destruct I as [I|I], J as [J|J].
    + eapply Edges; [exact I|exact J|exact Step|eapply OldOnly; eassumption|eapply OldOnly; eassumption].
    + subst j. assert (i=n) by (eapply zf_successor_injective; [exact Step|exact Next]). subst i.
      assert (u=a) by (eapply relational_function_graph_unique; [split;eassumption|eapply OldOnly;eassumption|exact At]).
      assert (v=value) by now apply NewOnly. now subst u v.
    + subst i. exfalso. assert (Ninj : R next j) by (apply (proj2 (Step next));now right).
      eapply (zf_no_finite_membership_cycle R EM Model 2 next); [lia|].
      eapply path_step; [exact Ninj|]. eapply path_step; [exact J|constructor].
    + subst i j. exfalso. apply Nonself,(proj2 (Step next)). now right.
Qed.
End StageRuns.
Print Assumptions zf_successor_injective.
Print Assumptions zf_stage_run_base.
Print Assumptions zf_stage_run_extend.
