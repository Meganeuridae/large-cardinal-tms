(** Recover source DAG subroutine contexts from checked finite unfoldings. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerReverse.
From Repair Require Import CompilerData CompilerReverse ConstructorGraph SourceExecution.
Import ListNotations.
Local Opaque source_graph.

Inductive constructor_tree_prefix : constructor_tree -> list bool -> constructor_tree -> Prop :=
| constructor_tree_prefix_nil t : constructor_tree_prefix t [] t
| constructor_tree_prefix_left l r bits t : constructor_tree_prefix l bits t ->
    constructor_tree_prefix (CTSeq l r) (false::bits) t
| constructor_tree_prefix_right l r bits t : constructor_tree_prefix r bits t ->
    constructor_tree_prefix (CTSeq l r) (true::bits) t.

Lemma tree_prefix_sequence t bits a b : constructor_tree_prefix t bits (CTSeq a b) ->
  exists l r, t = CTSeq l r.
Proof. intro P. inversion P; subst; eauto. Qed.

Lemma unfold_with_more_fuel lookup fuel : forall extra atom tree,
  unfold_with lookup fuel atom = Some tree ->
  unfold_with lookup (fuel+extra) atom = Some tree.
Proof.
  induction fuel as [|fuel IH]; intros extra atom tree H; [discriminate|].
  destruct atom as [i|r|r| |k|k]; cbn [unfold_with] in *; try assumption.
  destruct (lookup i) as [[l r]|] eqn:E; [|discriminate].
  destruct (unfold_with lookup fuel l) as [a|] eqn:L; [|discriminate].
  destruct (unfold_with lookup fuel r) as [b|] eqn:R; [|discriminate].
  inversion H; subst. change (unfold_with lookup (S (fuel+extra)) (SNode i) = Some (CTSeq a b)).
  cbn [unfold_with]. rewrite E, (IH extra l a L), (IH extra r b R). reflexivity.
Qed.

Theorem source_prefix_from_tree fuel root tree bits a b :
  unfold_with (nth_error source_graph) fuel (SNode root) = Some tree ->
  constructor_tree_prefix tree bits (CTSeq a b) ->
  exists child remaining, SourcePrefix source_graph root bits child /\ remaining <= fuel /\
    unfold_with (nth_error source_graph) remaining (SNode child) = Some (CTSeq a b).
Proof.
  revert fuel root tree a b. induction bits as [|bit bits IH]; intros fuel root tree a b U P.
  - inversion P; subst. exists root,fuel. repeat split; try constructor; assumption.
  - destruct fuel as [|fuel]; [discriminate|]. cbn [unfold_with] in U.
    destruct (nth_error source_graph root) as [[l r]|] eqn:E; [|discriminate].
    destruct (unfold_with (nth_error source_graph) fuel l) as [lt|] eqn:L; [|discriminate].
    destruct (unfold_with (nth_error source_graph) fuel r) as [rt|] eqn:R; [|discriminate].
    inversion U; subst tree. destruct bit.
    + inversion P; subst. pose proof (tree_prefix_sequence _ _ _ _ H3) as [x [y T]].
      destruct r as [next|n|n| |n|n]; try (destruct fuel; [discriminate|cbn [unfold_with] in R; inversion R; subst; discriminate]).
      destruct (IH fuel next rt a b R H3) as [child [remaining [Pref [Bound F]]]].
      exists child,remaining. split; [eapply source_prefix_cons; [exact E|reflexivity|exact Pref]|].
      split; [lia|exact F].
    + inversion P; subst. pose proof (tree_prefix_sequence _ _ _ _ H3) as [x [y T]].
      destruct l as [next|n|n| |n|n]; try (destruct fuel; [discriminate|cbn [unfold_with] in L; inversion L; subst; discriminate]).
      destruct (IH fuel next lt a b L H3) as [child [remaining [Pref [Bound F]]]].
      exists child,remaining. split; [eapply source_prefix_cons; [exact E|reflexivity|exact Pref]|].
      split; [lia|exact F].
Qed.

Local Opaque unfold_with.
Theorem source_unpair_loop_subtree root input out1 out2 :
  unfold_root root = Some (tree_unpair input out1 out2) ->
  exists child, SourcePrefix source_graph root [true;true;true;false] child /\
    unfold_root child = Some (tree_while1 out1 out2).
Proof.
  intro U. unfold unfold_root in U.
  assert (P : constructor_tree_prefix (tree_unpair input out1 out2)
    [true;true;true;false] (tree_while1 out1 out2)).
  { unfold tree_unpair. repeat constructor. }
  unfold tree_while1 in *.
  destruct (source_prefix_from_tree 64 root _ _ _ _ U P)
    as [child [remaining [Pref [Bound F]]]].
  exists child. split; [exact Pref|]. unfold unfold_root.
  replace 64 with (remaining + (64-remaining)) by lia.
  now apply unfold_with_more_fuel.
Qed.

Print Assumptions source_prefix_from_tree.
Print Assumptions source_unpair_loop_subtree.
