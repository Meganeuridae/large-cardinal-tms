(** Outer source control for the two concrete TMBuilder.pair instances. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import RuntimeControl RuntimeCalls CompilerSyntax CompilerData
  CompilerReverse CompilerContexts CompilerExecution CompilerRegisters ConstructorGraph
  ConstructorPaths ConstructorPC ConstructorControl.
Import ListNotations.

Record pair_layout root input1 input2 output first_loop second_loop : Prop := {
  pair_layout_tree : unfold_root root = Some (tree_pair input1 input2 output);
  pair_first_prefix : SourcePrefix source_graph root [false] first_loop;
  pair_first_tree : unfold_root first_loop = Some (tree_while2 input1 input2 output);
  pair_second_prefix : SourcePrefix source_graph root [true;true;false;true] second_loop;
  pair_second_tree : unfold_root second_loop = Some (tree_while1 input2 input1)
}.

Lemma pair_layout_push : pair_layout 8 2 3 8 2 4.
Proof.
  destruct source_internal_trees as [A [_ [_ [D [E _]]]]].
  destruct constructor_internal_prefixes as [_ [_ [_ [P [Q _]]]]].
  constructor; assumption.
Qed.
Lemma pair_layout_cons : pair_layout 39 8 2 9 33 35.
Proof.
  destruct source_internal_trees as [_ [B [_ [_ [_ [F [G _]]]]]]].
  destruct constructor_internal_prefixes as [_ [_ [_ [_ [_ [P [Q _]]]]]]].
  constructor; assumption.
Qed.

Lemma pair_test_leaf ctx root i j k :
  SourcePrefix source_graph source_root ctx root ->
  unfold_root root = Some (tree_pair i j k) ->
  SourceSelect source_graph source_root (ctx++[true;false]) (SDec j).
Proof.
  intros P T. destruct (constructor_pair_leaf_paths _ _ _ _ T) as [Sel _].
  eapply source_select_in_context; eassumption.
Qed.
Lemma pair_inc_leaf ctx root i j k :
  SourcePrefix source_graph source_root ctx root ->
  unfold_root root = Some (tree_pair i j k) ->
  SourceSelect source_graph source_root (ctx++[true;true;false;false]) (SInc k).
Proof.
  intros P T. destruct (constructor_pair_leaf_paths _ _ _ _ T) as [_ [Sel _]].
  eapply source_select_in_context; eassumption.
Qed.
Lemma pair_continue_leaf ctx root i j k :
  SourcePrefix source_graph source_root ctx root ->
  unfold_root root = Some (tree_pair i j k) ->
  SourceSelect source_graph source_root (ctx++[true;true;true]) (SContinue 3).
Proof.
  intros P T. destruct (constructor_pair_leaf_paths _ _ _ _ T) as [_ [_ Sel]].
  eapply source_select_in_context; eassumption.
Qed.

Lemma source_pair_test_zero ctx root i j k rs :
  SourcePrefix source_graph source_root ctx root -> unfold_root root = Some (tree_pair i j k) ->
  j < 11 -> nth_error rs j = Some 0 ->
  SourceProgramStep (ctx++[true],rs) (loop_return ctx,rs).
Proof.
  intros P T J N. destruct (loop_return_spec ctx) as [out [n [E R]]]. rewrite R.
  eapply constructor_step_dec_zero with (pad:=1) (i:=j) (count:=S(S n)).
  - change (SourceSelect source_graph source_root ((ctx++[true])++[false]) (SDec j)).
    rewrite <- app_assoc. eapply pair_test_leaf; eassumption.
  - exact J.
  - exact N.
  - change (break_pc 1 (rev ((ctx++[true])++[false])++[false]) = Some(out,S(S n))).
    rewrite <- app_assoc. now apply constructor_failed_test_return.
Qed.

Lemma source_pair_test_positive ctx root i j k rs n :
  SourcePrefix source_graph source_root ctx root -> unfold_root root = Some (tree_pair i j k) ->
  j < 11 -> nth_error rs j = Some (S n) ->
  SourceProgramStep (ctx++[true],rs) (ctx++[true;true],set_register j n rs ++ [0]).
Proof.
  intros P T J N.
  replace (ctx++[true;true]) with (return_word (true::rev (ctx++[true])++[false]))
    by (rewrite constructor_return_word, <- app_assoc; reflexivity).
  eapply constructor_step_dec_positive with (pad:=1) (i:=j) (count:=0).
  - change (SourceSelect source_graph source_root ((ctx++[true])++[false]) (SDec j)).
    rewrite <- app_assoc. eapply pair_test_leaf; eassumption.
  - exact J.
  - exact N.
  - change (break_pc 0 (rev ((ctx++[true])++[false])++[false]) =
      Some(true::rev (ctx++[true])++[false],0)).
    pose proof (proj1 (constructor_child_return (ctx++[true]) 0)) as C.
    now rewrite app_nil_r in C.
Qed.

Lemma source_pair_increment ctx root i j k rs n :
  SourcePrefix source_graph source_root ctx root -> unfold_root root = Some (tree_pair i j k) ->
  k < 11 -> nth_error rs k = Some n ->
  SourceProgramStep (ctx++[true;true],rs)
    (ctx++[true;true;false;true],set_register k (S n) rs).
Proof.
  intros P T K N.
  replace (ctx++[true;true;false;true]) with
    (return_word (true::rev (ctx++[true;true;false])++[false]))
    by (rewrite constructor_return_word, <- app_assoc; reflexivity).
  eapply constructor_step_inc with (pad:=2) (i:=k) (count:=0).
  - change (SourceSelect source_graph source_root ((ctx++[true;true])++[false;false]) (SInc k)).
    rewrite <- app_assoc. eapply pair_inc_leaf; eassumption.
  - exact K.
  - exact N.
  - change (break_pc 0 (rev ((ctx++[true;true])++[false;false])++[false]) =
      Some(true::rev (ctx++[true;true;false])++[false],0)).
    rewrite <- app_assoc.
    pose proof (proj1 (constructor_child_return (ctx++[true;true;false]) 0)) as C.
    rewrite app_nil_r in C. rewrite <- app_assoc in C. exact C.
Qed.

Lemma source_pair_continue ctx root i j k rs :
  SourcePrefix source_graph source_root ctx root -> unfold_root root = Some (tree_pair i j k) ->
  SourceProgramStep (ctx++[true;true;true],rs) (ctx,rs).
Proof.
  intros P T. replace ctx with (rev (rev ctx)) at 2 by apply rev_involutive.
  replace (ctx++[true;true;true]) with ((ctx++[true;true])++[true])
    by (rewrite <- app_assoc; reflexivity).
  eapply constructor_step_continue with (k:=2) (count:=2).
  - rewrite <- app_assoc. eapply pair_continue_leaf; eassumption.
  - apply constructor_outer_continue.
Qed.

Print Assumptions pair_layout_push.
Print Assumptions pair_layout_cons.
Print Assumptions source_pair_test_zero.
Print Assumptions source_pair_test_positive.
Print Assumptions source_pair_increment.
Print Assumptions source_pair_continue.
