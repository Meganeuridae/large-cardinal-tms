(** Source-control paths through the concrete pair and unpair routines. *)
From Stdlib Require Import Lists.List.
From Berkeley Require Import CompilerSyntax CompilerData CompilerReverse CompilerContexts
  CompilerTrees ConstructorGraph.
Import ListNotations.
Local Opaque source_graph.

Lemma constructor_source_prefix_concat program root xs mid ys child :
  SourcePrefix program root xs mid -> SourcePrefix program mid ys child ->
  SourcePrefix program root (xs++ys) child.
Proof.
  intros P Q. induction P; [exact Q|].
  simpl. eapply source_prefix_cons; [exact H|exact H0|]. now apply IHP.
Qed.

Theorem constructor_pair_leaf_paths root a b out :
  unfold_root root = Some (tree_pair a b out) ->
  SourceSelect source_graph root [true;false] (SDec b) /\
  SourceSelect source_graph root [true;true;false;false] (SInc out) /\
  SourceSelect source_graph root [true;true;true] (SContinue 3).
Proof.
  intro T. repeat split.
  - eapply root_unfold_selection; [exact T|]. unfold tree_pair.
    apply tree_select_right, tree_select_left, tree_select_dec.
  - eapply root_unfold_selection; [exact T|]. unfold tree_pair.
    apply tree_select_right, tree_select_right, tree_select_left, tree_select_left, tree_select_inc.
  - eapply root_unfold_selection; [exact T|]. unfold tree_pair.
    apply tree_select_right, tree_select_right, tree_select_right, tree_select_continue.
Qed.

Theorem constructor_unpair_leaf_paths root input out1 out2 :
  unfold_root root = Some (tree_unpair input out1 out2) ->
  SourceSelect source_graph root [false] (SDec input) /\
  SourceSelect source_graph root [true;false] (SInc out1) /\
  SourceSelect source_graph root [true;true;false;false] (SDec out2) /\
  SourceSelect source_graph root [true;true;false;true] (SContinue 3) /\
  SourceSelect source_graph root [true;true;true;true] (SContinue 4).
Proof.
  intro T. repeat split.
  - eapply root_unfold_selection; [exact T|]. unfold tree_unpair.
    apply tree_select_left, tree_select_dec.
  - eapply root_unfold_selection; [exact T|]. unfold tree_unpair.
    apply tree_select_right, tree_select_left, tree_select_inc.
  - eapply root_unfold_selection; [exact T|]. unfold tree_unpair.
    apply tree_select_right, tree_select_right, tree_select_left, tree_select_left, tree_select_dec.
  - eapply root_unfold_selection; [exact T|]. unfold tree_unpair.
    apply tree_select_right, tree_select_right, tree_select_left, tree_select_right, tree_select_continue.
  - eapply root_unfold_selection; [exact T|]. unfold tree_unpair.
    apply tree_select_right, tree_select_right, tree_select_right, tree_select_right, tree_select_continue.
Qed.

(** The closed constructor DAG contains these exact loop contexts. *)
Theorem constructor_internal_prefixes :
  SourcePrefix source_graph 11 [false] 8 /\
  SourcePrefix source_graph 41 [false] 29 /\
  SourcePrefix source_graph 41 [true;true;false] 39 /\
  SourcePrefix source_graph 8 [false] 2 /\
  SourcePrefix source_graph 8 [true;true;false;true] 4 /\
  SourcePrefix source_graph 39 [false] 33 /\
  SourcePrefix source_graph 39 [true;true;false;true] 35 /\
  SourcePrefix source_graph 29 [true;true;true;false] 24.
Proof.
  repeat split; apply source_prefix_find_sound; vm_compute; reflexivity.
Qed.

Print Assumptions constructor_source_prefix_concat.
Print Assumptions constructor_pair_leaf_paths.
Print Assumptions constructor_unpair_leaf_paths.
Print Assumptions constructor_internal_prefixes.
