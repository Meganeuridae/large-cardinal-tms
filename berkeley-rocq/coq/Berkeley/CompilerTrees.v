(** Operational selection from finite structured subtrees. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerData CompilerReverse CompilerContexts ConstructorGraph.
Import ListNotations.
Local Opaque source_graph.

Inductive TreeSelect : constructor_tree -> list bool -> source_atom -> Prop :=
| tree_select_inc r : TreeSelect (CTInc r) [] (SInc r)
| tree_select_dec r : TreeSelect (CTDec r) [] (SDec r)
| tree_select_halt : TreeSelect CTHalt [] SHalt
| tree_select_break k : TreeSelect (CTBreak k) [] (SBreak k)
| tree_select_continue k : TreeSelect (CTContinue k) [] (SContinue k)
| tree_select_left a b bits leaf : TreeSelect a bits leaf ->
    TreeSelect (CTSeq a b) (false::bits) leaf
| tree_select_right a b bits leaf : TreeSelect b bits leaf ->
    TreeSelect (CTSeq a b) (true::bits) leaf.

Definition atom_selected a bits leaf :=
  match a with
  | SNode i => SourceSelect source_graph i bits leaf
  | _ => bits = [] /\ leaf = a
  end.

Theorem unfolded_tree_selection fuel atom tree bits leaf :
  unfold_with (nth_error source_graph) fuel atom = Some tree ->
  TreeSelect tree bits leaf -> atom_selected atom bits leaf.
Proof.
  revert atom tree bits leaf.
  induction fuel as [|fuel IH]; intros atom tree bits leaf U S; [discriminate|].
  destruct atom as [i|r|r| |k|k]; cbn [unfold_with] in U;
    try (inversion U; subst tree; inversion S; subst; cbn [atom_selected]; auto).
  destruct (nth_error source_graph i) as [[left right]|] eqn:P; [|discriminate].
  destruct (unfold_with (nth_error source_graph) fuel left) as [lt|] eqn:L; [|discriminate].
  destruct (unfold_with (nth_error source_graph) fuel right) as [rt|] eqn:R; [|discriminate].
  inversion U; subst tree.
  inversion S as [| | | | |a0 b0 bs0 lf0 Sel|a0 b0 bs0 lf0 Sel]; subst.
  - pose proof (IH _ _ _ _ L Sel) as M.
    destruct left as [j|r|r| |k|k]; cbn [atom_selected] in M |- *;
      try (destruct M as [-> ->]; eapply select_leaf; [exact P|reflexivity|reflexivity]).
    eapply select_node with (pair:=(SNode j,right)) (j:=j); [exact P|reflexivity|exact M].
  - pose proof (IH _ _ _ _ R Sel) as M.
    destruct right as [j|r|r| |k|k]; cbn [atom_selected] in M |- *;
      try (destruct M as [-> ->]; eapply select_leaf; [exact P|reflexivity|reflexivity]).
    eapply select_node with (pair:=(left,SNode j)) (j:=j); [exact P|reflexivity|exact M].
Qed.

Local Opaque unfold_with.
Theorem root_unfold_selection root tree bits leaf : unfold_root root = Some tree ->
  TreeSelect tree bits leaf -> SourceSelect source_graph root bits leaf.
Proof.
  intros U S. unfold unfold_root in U.
  exact (unfolded_tree_selection 64 (SNode root) tree bits leaf U S).
Qed.

Lemma while1_source_selections root input output : unfold_root root = Some (tree_while1 input output) ->
  SourceSelect source_graph root [false] (SDec input) /\
  SourceSelect source_graph root [true;false] (SInc output) /\
  SourceSelect source_graph root [true;true] (SContinue 2).
Proof.
  intro U. repeat split.
  - eapply root_unfold_selection; [exact U|]. unfold tree_while1.
    apply tree_select_left, tree_select_dec.
  - eapply root_unfold_selection; [exact U|]. unfold tree_while1.
    apply tree_select_right, tree_select_left, tree_select_inc.
  - eapply root_unfold_selection; [exact U|]. unfold tree_while1.
    apply tree_select_right, tree_select_right, tree_select_continue.
Qed.

Lemma while2_source_selections root input output1 output2 :
  unfold_root root = Some (tree_while2 input output1 output2) ->
  SourceSelect source_graph root [false] (SDec input) /\
  SourceSelect source_graph root [true;false;false] (SInc output1) /\
  SourceSelect source_graph root [true;false;true] (SInc output2) /\
  SourceSelect source_graph root [true;true] (SContinue 2).
Proof.
  intro U. repeat split.
  - eapply root_unfold_selection; [exact U|]. unfold tree_while2.
    apply tree_select_left, tree_select_dec.
  - eapply root_unfold_selection; [exact U|]. unfold tree_while2.
    apply tree_select_right, tree_select_left, tree_select_left, tree_select_inc.
  - eapply root_unfold_selection; [exact U|]. unfold tree_while2.
    apply tree_select_right, tree_select_left, tree_select_right, tree_select_inc.
  - eapply root_unfold_selection; [exact U|]. unfold tree_while2.
    apply tree_select_right, tree_select_right, tree_select_continue.
Qed.

Print Assumptions unfolded_tree_selection.
Print Assumptions while1_source_selections.
Print Assumptions while2_source_selections.
