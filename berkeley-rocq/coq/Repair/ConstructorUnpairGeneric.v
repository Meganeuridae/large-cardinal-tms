(** Literal unpair source execution for any checked register instantiation. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import RuntimeControl RuntimeCalls CompilerSyntax CompilerRegisters ConstructorPC CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerContexts CompilerExecution CompilerLoopBase CompilerLoops ConstructorGraph ConstructorPaths ConstructorControl ConstructorUnpair ConstructorUnpairGenericTree SourceExecution.
Import ListNotations.

Lemma generic_unpair_leaves ctx root i j k :
  SourcePrefix source_graph source_root ctx root -> unfold_root root = Some (tree_unpair i j k) ->
  SourceSelect source_graph source_root (ctx++[false]) (SDec i) /\
  SourceSelect source_graph source_root (ctx++[true;false]) (SInc j) /\
  SourceSelect source_graph source_root (ctx++[true;true;false;false]) (SDec k) /\
  SourceSelect source_graph source_root (ctx++[true;true;false;true]) (SContinue 3) /\
  SourceSelect source_graph source_root (ctx++[true;true;true;true]) (SContinue 4).
Proof.
  intros P T. destruct (constructor_unpair_leaf_paths _ _ _ _ T) as [A [B [C [D E]]]].
  repeat split; eapply source_select_in_context; eassumption.
Qed.

Lemma generic_unpair_input_zero ctx root i j k rs :
  SourcePrefix source_graph source_root ctx root -> unfold_root root = Some (tree_unpair i j k) ->
  i < 11 -> nth_error rs i = Some 0 -> SourceProgramStep (ctx,rs) (loop_return ctx,rs).
Proof.
  intros P T I N. destruct (loop_return_spec ctx) as [out [n [Ret E]]]. rewrite E.
  eapply constructor_step_dec_zero with (pad:=1) (i:=i) (count:=S n).
  - change (SourceSelect source_graph source_root (ctx++[false]) (SDec i)).
    exact (proj1 (generic_unpair_leaves _ _ _ _ _ P T)).
  - exact I.
  - exact N.
  - change (break_pc 1 (rev (ctx++[false])++[false]) = Some(out,S n)).
    now apply constructor_first_test_return.
Qed.

Lemma generic_unpair_input_positive ctx root i j k rs n :
  SourcePrefix source_graph source_root ctx root -> unfold_root root = Some (tree_unpair i j k) ->
  i < 11 -> nth_error rs i = Some (S n) ->
  SourceProgramStep (ctx,rs) (ctx++[true],set_register i n rs ++ [0]).
Proof.
  intros P T I N. rewrite <- constructor_return_word.
  eapply constructor_step_dec_positive with (pad:=1) (i:=i) (count:=0).
  - change (SourceSelect source_graph source_root (ctx++[false]) (SDec i)).
    exact (proj1 (generic_unpair_leaves _ _ _ _ _ P T)).
  - exact I.
  - exact N.
  - change (break_pc 0 (rev (ctx++[false])++[false]) = Some(true::rev ctx++[false],0)).
    pose proof (proj1 (constructor_child_return ctx 0)) as C. now rewrite app_nil_r in C.
Qed.

Lemma generic_unpair_increment ctx root i j k rs x :
  SourcePrefix source_graph source_root ctx root -> unfold_root root = Some (tree_unpair i j k) ->
  j < 11 -> nth_error rs j = Some x ->
  SourceProgramStep (ctx++[true],rs) (ctx++[true;true],set_register j (S x) rs).
Proof.
  intros P T J N.
  replace (ctx++[true;true]) with (return_word (true::rev (ctx++[true])++[false]))
    by (rewrite constructor_return_word, <- app_assoc; reflexivity).
  eapply constructor_step_inc with (pad:=1) (i:=j) (count:=0).
  - change (SourceSelect source_graph source_root ((ctx++[true])++[false]) (SInc j)).
    rewrite <- app_assoc. exact (proj1 (proj2 (generic_unpair_leaves _ _ _ _ _ P T))).
  - exact J.
  - exact N.
  - change (break_pc 0 (rev ((ctx++[true])++[false])++[false]) =
      Some (true::rev (ctx++[true])++[false],0)).
    pose proof (proj1 (constructor_child_return (ctx++[true]) 0)) as C. now rewrite app_nil_r in C.
Qed.

Lemma generic_unpair_test_zero ctx root i j k rs :
  SourcePrefix source_graph source_root ctx root -> unfold_root root = Some (tree_unpair i j k) ->
  k < 11 -> nth_error rs k = Some 0 ->
  SourceProgramStep (ctx++[true;true],rs) (ctx++[true;true;true],rs).
Proof.
  intros P T K N. destruct (constructor_inner_test_zero ctx) as [Ret Out]. rewrite <- Out.
  eapply constructor_step_dec_zero with (pad:=2) (i:=k) (count:=1).
  - change (SourceSelect source_graph source_root ((ctx++[true;true])++[false;false]) (SDec k)).
    rewrite <- app_assoc. exact (proj1 (proj2 (proj2 (generic_unpair_leaves _ _ _ _ _ P T)))).
  - exact K.
  - exact N.
  - change (break_pc 1 (rev ((ctx++[true;true])++[false;false])++[false]) =
      Some (true::true::true::rev ctx++[false],1)). rewrite <- app_assoc. exact Ret.
Qed.

Lemma generic_unpair_test_positive ctx root i j k rs y :
  SourcePrefix source_graph source_root ctx root -> unfold_root root = Some (tree_unpair i j k) ->
  k < 11 -> nth_error rs k = Some (S y) ->
  SourceProgramStep (ctx++[true;true],rs)
    (ctx++[true;true;false;true],set_register k y rs ++ [0]).
Proof.
  intros P T K N.
  replace (ctx++[true;true;false;true]) with
    (return_word (true::rev (ctx++[true;true;false])++[false]))
    by (rewrite constructor_return_word, <- app_assoc; reflexivity).
  eapply constructor_step_dec_positive with (pad:=2) (i:=k) (count:=0).
  - change (SourceSelect source_graph source_root ((ctx++[true;true])++[false;false]) (SDec k)).
    rewrite <- app_assoc. exact (proj1 (proj2 (proj2 (generic_unpair_leaves _ _ _ _ _ P T)))).
  - exact K.
  - exact N.
  - change (break_pc 0 (rev ((ctx++[true;true])++[false;false])++[false]) =
      Some (true::rev (ctx++[true;true;false])++[false],0)).
    rewrite <- app_assoc. pose proof (proj1 (constructor_child_return (ctx++[true;true;false]) 0)) as C.
    rewrite app_nil_r in C. rewrite <- app_assoc in C. exact C.
Qed.

Lemma generic_unpair_continue_early ctx root i j k rs :
  SourcePrefix source_graph source_root ctx root -> unfold_root root = Some (tree_unpair i j k) ->
  SourceProgramStep (ctx++[true;true;false;true],rs) (ctx,rs).
Proof.
  intros P T. replace ctx with (rev (rev ctx)) at 2 by apply rev_involutive.
  replace (ctx++[true;true;false;true]) with ((ctx++[true;true;false])++[true])
    by (rewrite <- app_assoc; reflexivity).
  eapply constructor_step_continue with (k:=2) (count:=3).
  - rewrite <- app_assoc. exact (proj1 (proj2 (proj2 (proj2 (generic_unpair_leaves _ _ _ _ _ P T))))).
  - apply constructor_unpair_continue_early.
Qed.

Lemma generic_unpair_continue_late ctx root i j k rs :
  SourcePrefix source_graph source_root ctx root -> unfold_root root = Some (tree_unpair i j k) ->
  SourceProgramStep (ctx++[true;true;true;true],rs) (ctx,rs).
Proof.
  intros P T. replace ctx with (rev (rev ctx)) at 2 by apply rev_involutive.
  replace (ctx++[true;true;true;true]) with ((ctx++[true;true;true])++[true])
    by (rewrite <- app_assoc; reflexivity).
  eapply constructor_step_continue with (k:=3) (count:=3).
  - rewrite <- app_assoc. exact (proj2 (proj2 (proj2 (proj2 (generic_unpair_leaves _ _ _ _ _ P T))))).
  - apply constructor_unpair_continue_late.
Qed.

Theorem generic_unpair_positive_cycle ctx root i j k rs n x y :
  SourcePrefix source_graph source_root ctx root -> unfold_root root = Some (tree_unpair i j k) ->
  i < 11 -> j < 11 -> k < 11 -> i<>j -> i<>k -> j<>k -> 11 <= length rs ->
  nth_error rs i = Some (S n) -> nth_error rs j = Some x -> nth_error rs k = Some (S y) ->
  SourceProgramRuns (ctx,rs)
    (ctx, set_register k y (set_register j (S x) (set_register i n rs ++ [0])) ++ [0]).
Proof.
  intros P T I J K IJ IK JK L N X Y.
  assert (X' : nth_error (set_register i n rs ++ [0]) j = Some x).
  { rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact X. }
  assert (Y' : nth_error (set_register j (S x) (set_register i n rs ++ [0])) k = Some (S y)).
  { rewrite nth_error_set_other by lia. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact Y. }
  eapply source_program_next; [eapply generic_unpair_input_positive; eassumption|].
  eapply source_program_next; [eapply generic_unpair_increment; eassumption|].
  eapply source_program_next; [eapply generic_unpair_test_positive; eassumption|].
  eapply source_program_next; [eapply generic_unpair_continue_early; eassumption|].
  constructor.
Qed.

Theorem generic_unpair_zero_output_cycle ctx root i j k rs n x :
  SourcePrefix source_graph source_root ctx root -> unfold_root root = Some (tree_unpair i j k) ->
  i < 11 -> j < 11 -> k < 11 -> i<>j -> i<>k -> j<>k -> 11 <= length rs ->
  nth_error rs i = Some (S n) -> nth_error rs j = Some x -> nth_error rs k = Some 0 ->
  let r1 := set_register i n rs ++ [0] in
  let r2 := set_register j (S x) r1 in
  SourceProgramRuns (ctx,rs)
    (ctx, set_register k (S x) (set_register j 0 r2) ++ repeat 0 (S x)).
Proof.
  intros P T I J K IJ IK JK L N X Y. cbn zeta.
  set (r1 := set_register i n rs ++ [0]). set (r2 := set_register j (S x) r1).
  assert (L1 : 11 <= length r1) by (unfold r1; rewrite app_length, set_register_length; simpl; lia).
  assert (L2 : 11 <= length r2) by (unfold r2; rewrite set_register_length; exact L1).
  assert (X1 : nth_error r1 j = Some x).
  { unfold r1. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact X. }
  assert (Y1 : nth_error r1 k = Some 0).
  { unfold r1. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact Y. }
  assert (X2 : nth_error r2 j = Some (S x)) by (unfold r2; apply nth_error_set_same; lia).
  assert (Y2 : nth_error r2 k = Some 0) by (unfold r2; rewrite nth_error_set_other by lia; exact Y1).
  destruct (source_unpair_loop_subtree root i j k T) as [inner [Sub LoopTree]].
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P Sub) as LoopPrefix.
  destruct (while1_transfer_nonempty (ctx++[true;true;true;false]) inner r2 j k (S x) 0
              LoopPrefix LoopTree J K JK L2 X2 Y2) as [mid [First Rest]].
  cbn [Nat.add_0_l] in Rest.
  assert (Ret : loop_return (ctx++[true;true;true;false]) = ctx++[true;true;true;true]).
  { replace (ctx++[true;true;true;false]) with ((ctx++[true;true;true])++[false])
      by (rewrite <- app_assoc; reflexivity).
    rewrite constructor_loop_return_false, <- app_assoc. reflexivity. }
  rewrite Ret in Rest.
  eapply source_program_next; [eapply generic_unpair_input_positive; eassumption|].
  eapply source_program_next; [eapply generic_unpair_increment; eassumption|].
  eapply source_program_next; [eapply generic_unpair_test_zero; eassumption|].
  eapply source_program_next with (t:=mid).
  - eapply constructor_unpad_first_step with (pad:=1).
    change (SourceProgramStep ((ctx++[true;true;true])++[false],r2) mid).
    rewrite <- app_assoc. exact First.
  - eapply source_program_runs_trans; [exact Rest|].
    eapply source_program_next; [eapply generic_unpair_continue_late; eassumption|constructor].
Qed.

Print Assumptions generic_unpair_leaves.
Print Assumptions generic_unpair_input_zero.
Print Assumptions generic_unpair_input_positive.
Print Assumptions generic_unpair_positive_cycle.
Print Assumptions generic_unpair_zero_output_cycle.
