(** First-order finite-function graph infrastructure. The successor extension
    is a local stage and does not presuppose an external iteration. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import ProofFormula FormulaSemantics BerkeleySyntaxBase BerkeleySyntaxInterpretation
  BerkeleySyntaxSets BerkeleySyntaxPairs BerkeleySyntaxPairInject BerkeleySyntaxFunction BerkeleySyntaxFunctionFacts
  BerkeleySyntaxZFBase BerkeleySyntaxZFUnion BerkeleySyntaxZFFoundation.
Import ListNotations.
Definition RelPartialFunction {D} (R:D->D->Prop) s dom := exists range, RelFunction R s dom range.
Definition b_partial_function s dom := b_ex (fun cod => b_function s dom cod).
Section FiniteGraphs.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.
Theorem partial_function_builder_holds rho s dom n : s<n -> dom<n ->
  (b_holds R rho (b_partial_function s dom) n <-> RelPartialFunction R (rho s) (rho dom)).
Proof.
  intros S Dom. unfold b_partial_function,RelPartialFunction. rewrite (b_holds_ex EM). split.
  - intros [cod H]. rewrite (function_builder_holds EM) in H by lia.
    rewrite update_variable_eq in H. repeat rewrite update_variable_neq in H by lia. now exists cod.
  - intros [cod H]. exists cod. rewrite (function_builder_holds EM) by lia.
    rewrite update_variable_eq. repeat rewrite update_variable_neq by lia. exact H.
Qed.
Lemma appended_graph_characterization s t p dom value : RelPair R p dom value ->
  (forall z, R z t <-> R z s \/ z=p) ->
  forall u v, RelGraph R t u v <-> RelGraph R s u v \/ (u=dom /\ v=value).
Proof.
  intros P T u v. split.
  - intros [q [Pair In]]. apply (proj1 (T q)) in In. destruct In as [Old|Eq].
    + left. now exists q.
    + subst q. right. now apply (relational_pair_components R p u v dom value Pair P).
  - intros [[q [Pair In]]|[Eq1 Eq2]].
    + exists q. split; [exact Pair|apply (proj2 (T q));now left].
    + subst u v. exists p. split; [exact P|apply (proj2 (T p));now right].
Qed.
Theorem zf_function_extend_successor s dom cod dom' value :
  RelFunction R s dom cod -> RelSuccessor R dom' dom ->
  exists t cod', RelFunction R t dom' cod' /\
    forall u v, RelGraph R t u v <-> RelGraph R s u v \/ (u=dom /\ v=value).
Proof.
  intros F Next.
  destruct (zf_prefix_kuratowski_pair_exists R EM Model dom value) as [p P].
  destruct (zf_prefix_singleton_exists R EM Model p) as [one One].
  destruct (zf_prefix_binary_union_exists R EM Model s one) as [t T].
  destruct (zf_prefix_singleton_exists R EM Model value) as [valset Val].
  destruct (zf_prefix_binary_union_exists R EM Model cod valset) as [cod' C].
  assert (TM : forall z, R z t <-> R z s \/ z=p).
  { intro z. rewrite (T z),(One z). reflexivity. }
  pose proof (appended_graph_characterization s t p dom value P TM) as G.
  assert (Nonself : ~R dom dom) by apply (zf_prefix_membership_irreflexive R EM Model).
  exists t,cod'. split; [|exact G]. destruct F as [Graph Total]. split.
  - intros q In. apply (proj1 (TM q)) in In. destruct In as [Old|New].
    + destruct (Graph q Old) as [x [y [X [Y Pair]]]]. exists x,y. repeat split; try assumption.
      * apply (proj2 (Next x)). now left.
      * apply (proj2 (C y)). now left.
    + subst q. exists dom,value. repeat split; try assumption.
      * apply (proj2 (Next dom)). now right.
      * apply (proj2 (C value)). right. apply (proj2 (Val value)). reflexivity.
  - intros u U. apply (proj1 (Next u)) in U. destruct U as [Old|New].
    + destruct (Total u Old) as [v [V [At Unique]]]. exists v. split.
      * apply (proj2 (C v)). now left.
      * split.
        -- apply (proj2 (G u v)). now left.
        -- intros z Z At'. apply (proj1 (G u z)) in At'. destruct At' as [OldAt|[Eq _]].
           ++ eapply relational_function_graph_unique; [split; eassumption|exact OldAt|exact At].
           ++ subst u. contradiction.
    + subst u. exists value. split.
      * apply (proj2 (C value)). right. apply (proj2 (Val value)). reflexivity.
      * split.
        -- apply (proj2 (G dom value)). now right.
        -- intros z Z At'. apply (proj1 (G dom z)) in At'. destruct At' as [OldAt|[_ Eq]]; [|exact Eq].
           destruct (relational_function_graph_range R s dom cod dom z (conj Graph Total) OldAt) as [Bad _]. contradiction.
Qed.
Corollary zf_partial_function_extend_successor s dom dom' value :
  RelPartialFunction R s dom -> RelSuccessor R dom' dom ->
  exists t, RelPartialFunction R t dom' /\
    forall u v, RelGraph R t u v <-> RelGraph R s u v \/ (u=dom /\ v=value).
Proof.
  intros [cod F] Next. destruct (zf_function_extend_successor s dom cod dom' value F Next) as [t [cod' [T G]]].
  exists t. split; [now exists cod'|exact G].
Qed.
End FiniteGraphs.
Print Assumptions partial_function_builder_holds.
Print Assumptions appended_graph_characterization.
Print Assumptions zf_function_extend_successor.
Print Assumptions zf_partial_function_extend_successor.
