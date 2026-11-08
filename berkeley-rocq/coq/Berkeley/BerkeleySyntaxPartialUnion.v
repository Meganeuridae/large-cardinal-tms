(** Finite union of compatible downward-closed partial truth graphs. The
    overlap agreement comes from first-order definable internal induction. *)
From Stdlib Require Import Lists.List Arith.Arith.
From Berkeley Require Import BerkeleySyntaxPairs BerkeleySyntaxSets BerkeleySyntaxFormulaSet BerkeleySyntaxEnvironment
  BerkeleySyntaxZFBase BerkeleySyntaxZFUnion BerkeleySyntaxPartialTruth.
Import ListNotations.

Definition RelTruthGraphBound {D} (R:D->D->Prop) h g e :=
  forall p s, RelGraph R h p s -> R p g /\ R s e.
Definition RelPartialEvaluation {D} (R:D->D->Prop) h g e f w m te tm tn ti ta :=
  RelSubset R g f /\ RelPartialDownward R g f tn ti ta /\ RelPartialTruth R h g e f w m te tm tn ti ta /\
  RelTruthGraphBound R h g e.

Lemma graph_of_binary_union {D} (R:D->D->Prop) h h1 h2 : RelBinaryUnion R h h1 h2 ->
  forall p s, RelGraph R h p s <-> RelGraph R h1 p s \/ RelGraph R h2 p s.
Proof.
  intros U p s. split.
  - intros [q [Pair In]]. apply (proj1 (U q)) in In. destruct In as [In|In]; [left|right]; now exists q.
  - intros [[q [Pair In]]|[q [Pair In]]]; exists q; split; [exact Pair|apply (proj2 (U q)); now left|
      exact Pair|apply (proj2 (U q)); now right].
Qed.

Section PartialUnion.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Theorem zf_partial_evaluations_union f w m e te tm tn ti ta g1 g2 h1 h2 :
  RelFormulas R f w te tm tn ti ta -> RelEnvironments R e w m ->
  RelPartialEvaluation R h1 g1 e f w m te tm tn ti ta ->
  RelPartialEvaluation R h2 g2 e f w m te tm tn ti ta ->
  exists g h, RelPartialEvaluation R h g e f w m te tm tn ti ta /\
    RelBinaryUnion R g g1 g2 /\ RelBinaryUnion R h h1 h2.
Proof.
  intros Formulas Env [Sub1 [Down1 [Truth1 Bound1]]] [Sub2 [Down2 [Truth2 Bound2]]].
  destruct (zf_prefix_binary_union_exists R EM Model g1 g2) as [g G].
  destruct (zf_prefix_binary_union_exists R EM Model h1 h2) as [h H].
  pose proof (graph_of_binary_union R h h1 h2 H) as GraphU.
  pose proof (zf_partial_truth_agrees_on_overlap R EM Model f w m e te tm tn ti ta g1 g2 h1 h2
    Formulas Env Down1 Down2 Truth1 Truth2) as Agree.
  assert (Safe1 : forall p s, R p f -> R p g1 -> R s e ->
    (RelGraph R h p s <-> RelGraph R h1 p s)).
  { intros p s Pf P1 S. rewrite (GraphU p s). split.
    - intros [A|B]; [exact A|]. destruct (Bound2 p s B) as [P2 _]. apply (proj2 (Agree p s Pf P1 P2 S)),B.
    - intro A. now left. }
  assert (Safe2 : forall p s, R p f -> R p g2 -> R s e ->
    (RelGraph R h p s <-> RelGraph R h2 p s)).
  { intros p s Pf P2 S. rewrite (GraphU p s). split.
    - intros [A|B]; [|exact B]. destruct (Bound1 p s A) as [P1 _]. apply (proj1 (Agree p s Pf P1 P2 S)),A.
    - intro A. now right. }
  destruct Down1 as [NDown1 [IDown1 ADown1]]. destruct Down2 as [NDown2 [IDown2 ADown2]].
  exists g,h. split; [|now split]. unfold RelPartialEvaluation. split.
  - intros p P. apply (proj1 (G p)) in P. destruct P; [now apply Sub1|now apply Sub2].
  - split.
    + unfold RelPartialDownward. split.
      * intros p q P Q Pair. apply (proj1 (G p)) in P. apply (proj2 (G q)). destruct P as [P|P];
          [left; eapply NDown1|right; eapply NDown2]; eassumption.
      * split.
        -- intros p q r P Q T Node. apply (proj1 (G p)) in P. destruct P as [P|P].
           ++ destruct (IDown1 p q r P Q T Node) as [A B]. split; apply (proj2 (G _)); now left.
           ++ destruct (IDown2 p q r P Q T Node) as [A B]. split; apply (proj2 (G _)); now right.
        -- intros p x q P Q Node. apply (proj1 (G p)) in P. apply (proj2 (G q)). destruct P as [P|P];
             [left; eapply ADown1|right; eapply ADown2]; eassumption.
    + split.
      * intros s S. specialize (Truth1 s S). specialize (Truth2 s S).
        destruct Truth1 as [E1 [M1 [N1 [I1 A1]]]]. destruct Truth2 as [E2 [M2 [N2 [I2 A2]]]].
        split.
        -- intros x y a b p P X Y A B Ga Gb Node. apply (proj1 (G p)) in P. destruct P as [P|P].
           ++ rewrite (Safe1 p s (Sub1 p P) P S). exact (E1 x y a b p P X Y A B Ga Gb Node).
           ++ rewrite (Safe2 p s (Sub2 p P) P S). exact (E2 x y a b p P X Y A B Ga Gb Node).
        -- split.
           ++ intros x y a b p P X Y A B Ga Gb Node. apply (proj1 (G p)) in P. destruct P as [P|P].
              ** rewrite (Safe1 p s (Sub1 p P) P S). exact (M1 x y a b p P X Y A B Ga Gb Node).
              ** rewrite (Safe2 p s (Sub2 p P) P S). exact (M2 x y a b p P X Y A B Ga Gb Node).
           ++ split.
              ** intros q p P Qf Pair. apply (proj1 (G p)) in P. destruct P as [P|P].
                 --- pose proof (NDown1 p q P Qf Pair) as Q1.
                     rewrite (Safe1 p s (Sub1 p P) P S),(Safe1 q s Qf Q1 S). exact (N1 q p P Qf Pair).
                 --- pose proof (NDown2 p q P Qf Pair) as Q2.
                     rewrite (Safe2 p s (Sub2 p P) P S),(Safe2 q s Qf Q2 S). exact (N2 q p P Qf Pair).
              ** split.
                 --- intros q r p P Qf Rf Node. apply (proj1 (G p)) in P. destruct P as [P|P].
                     +++ destruct (IDown1 p q r P Qf Rf Node) as [Q1 R1].
                         rewrite (Safe1 p s (Sub1 p P) P S),(Safe1 q s Qf Q1 S),(Safe1 r s Rf R1 S). exact (I1 q r p P Qf Rf Node).
                     +++ destruct (IDown2 p q r P Qf Rf Node) as [Q2 R2].
                         rewrite (Safe2 p s (Sub2 p P) P S),(Safe2 q s Qf Q2 S),(Safe2 r s Rf R2 S). exact (I2 q r p P Qf Rf Node).
                 --- intros x q p P X Qf Node. apply (proj1 (G p)) in P. destruct P as [P|P].
                     +++ pose proof (ADown1 p x q P Qf Node) as Q1. rewrite (Safe1 p s (Sub1 p P) P S),(A1 x q p P X Qf Node).
                         split; intros Cond t T Up.
                         *** apply (proj2 (Safe1 q t Qf Q1 T)),Cond; assumption.
                         *** apply (proj1 (Safe1 q t Qf Q1 T)),Cond; assumption.
                     +++ pose proof (ADown2 p x q P Qf Node) as Q2. rewrite (Safe2 p s (Sub2 p P) P S),(A2 x q p P X Qf Node).
                         split; intros Cond t T Up.
                         *** apply (proj2 (Safe2 q t Qf Q2 T)),Cond; assumption.
                         *** apply (proj1 (Safe2 q t Qf Q2 T)),Cond; assumption.
      * intros p s P. apply (proj1 (GraphU p s)) in P. destruct P as [P|P].
        -- destruct (Bound1 p s P) as [A B]. split; [apply (proj2 (G p)); now left|exact B].
        -- destruct (Bound2 p s P) as [A B]. split; [apply (proj2 (G p)); now right|exact B].
Qed.
End PartialUnion.

Print Assumptions zf_partial_evaluations_union.
