(** Exact source tree and PCs for the MP scratch-register equality test. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import RuntimeControl RuntimeCalls RuntimeJumps CompilerSyntax CompilerReverse CompilerContexts CompilerRegisters ConstructorPaths ConstructorPC ConstructorUnpair.
From Repair Require Import ConstructorGraph CompilerData SourceExecution CompilerTrees CompilerLoopBase ConstructorControl SearchPrimitivesDrain.
Import ListNotations.

Definition tree_mp_compare :=
  CTSeq
    (CTSeq
      (CTSeq (CTDec 9)
        (CTSeq (CTSeq (CTDec 10) (CTContinue 2)) (CTSeq (tree_drain 9) (CTBreak 2))))
      (CTSeq (CTDec 10) (CTSeq (tree_drain 10) (CTBreak 1))))
    (tree_drain 2).

Local Transparent source_graph unfold_root.
Lemma source_mp_compare_tree : unfold_root 684 = Some tree_mp_compare.
Proof. vm_compute. reflexivity. Qed.
Lemma source_mp_compare_prefixes :
  SourcePrefix source_graph 684 [false;false;true;true;false] 661 /\
  SourcePrefix source_graph 684 [false;true;true;false] 662 /\
  SourcePrefix source_graph 684 [true] 675 /\
  unfold_root 675 = Some(tree_drain 2).
Proof. repeat split; try (apply source_prefix_find_sound); vm_compute; reflexivity. Qed.
Local Opaque source_graph unfold_root.

Lemma source_mp_compare_leaves ctx : SourcePrefix source_graph source_root ctx 684 ->
  SourceSelect source_graph source_root (ctx++[false;false;false]) (SDec 9) /\
  SourceSelect source_graph source_root (ctx++[false;false;true;false;false]) (SDec 10) /\
  SourceSelect source_graph source_root (ctx++[false;false;true;false;true]) (SContinue 2) /\
  SourceSelect source_graph source_root (ctx++[false;false;true;true;true]) (SBreak 2) /\
  SourceSelect source_graph source_root (ctx++[false;true;false]) (SDec 10) /\
  SourceSelect source_graph source_root (ctx++[false;true;true;true]) (SBreak 1).
Proof.
  intro P. repeat split.
  - eapply source_select_in_context; [exact P|]. eapply root_unfold_selection; [exact source_mp_compare_tree|].
    unfold tree_mp_compare. apply tree_select_left,tree_select_left,tree_select_left,tree_select_dec.
  - eapply source_select_in_context; [exact P|]. eapply root_unfold_selection; [exact source_mp_compare_tree|].
    unfold tree_mp_compare. apply tree_select_left,tree_select_left,tree_select_right,tree_select_left,tree_select_left,tree_select_dec.
  - eapply source_select_in_context; [exact P|]. eapply root_unfold_selection; [exact source_mp_compare_tree|].
    unfold tree_mp_compare. apply tree_select_left,tree_select_left,tree_select_right,tree_select_left,tree_select_right,tree_select_continue.
  - eapply source_select_in_context; [exact P|]. eapply root_unfold_selection; [exact source_mp_compare_tree|].
    unfold tree_mp_compare. apply tree_select_left,tree_select_left,tree_select_right,tree_select_right,tree_select_right,tree_select_break.
  - eapply source_select_in_context; [exact P|]. eapply root_unfold_selection; [exact source_mp_compare_tree|].
    unfold tree_mp_compare. apply tree_select_left,tree_select_right,tree_select_left,tree_select_dec.
  - eapply source_select_in_context; [exact P|]. eapply root_unfold_selection; [exact source_mp_compare_tree|].
    unfold tree_mp_compare. apply tree_select_left,tree_select_right,tree_select_right,tree_select_right,tree_select_break.
Qed.

Lemma source_mp_eq_left_zero ctx rs : SourcePrefix source_graph source_root ctx 684 -> nth_error rs 9=Some 0 ->
  SourceProgramStep (ctx,rs) (ctx++[false;true],rs).
Proof.
  intros P N. replace (ctx++[false;true]) with (return_word (true::rev (ctx++[false])++[false]))
    by (rewrite constructor_return_word, <- app_assoc; reflexivity).
  eapply constructor_step_dec_zero with (pad:=3) (i:=9) (count:=1).
  - change (SourceSelect source_graph source_root (ctx++[false;false;false]) (SDec 9)).
    exact (proj1 (source_mp_compare_leaves ctx P)).
  - lia.
  - exact N.
  - change (break_pc 1 (rev (ctx++[false;false;false])++[false]) =
      Some(true::rev (ctx++[false])++[false],1)).
    rewrite !rev_app_distr. reflexivity.
Qed.

Lemma source_mp_eq_left_positive ctx rs n : SourcePrefix source_graph source_root ctx 684 -> nth_error rs 9=Some(S n) ->
  SourceProgramStep (ctx,rs) (ctx++[false;false;true],set_register 9 n rs++[0]).
Proof.
  intros P N. replace (ctx++[false;false;true]) with
    (return_word (true::rev (ctx++[false;false])++[false]))
    by (rewrite constructor_return_word, <- app_assoc; reflexivity).
  eapply constructor_step_dec_positive with (pad:=3) (i:=9) (count:=0).
  - change (SourceSelect source_graph source_root (ctx++[false;false;false]) (SDec 9)).
    exact (proj1 (source_mp_compare_leaves ctx P)).
  - lia.
  - exact N.
  - change (break_pc 0 (rev (ctx++[false;false;false])++[false]) =
      Some(true::rev (ctx++[false;false])++[false],0)).
    rewrite !rev_app_distr. reflexivity.
Qed.

Lemma source_mp_eq_loop_right_positive ctx rs n : SourcePrefix source_graph source_root ctx 684 -> nth_error rs 10=Some(S n) ->
  SourceProgramStep (ctx++[false;false;true],rs)
    (ctx++[false;false;true;false;true],set_register 10 n rs++[0]).
Proof.
  intros P N. replace (ctx++[false;false;true;false;true]) with
    (return_word (true::rev (ctx++[false;false;true;false])++[false]))
    by (rewrite constructor_return_word, <- app_assoc; reflexivity).
  eapply constructor_step_dec_positive with (pad:=2) (i:=10) (count:=0).
  - change (SourceSelect source_graph source_root ((ctx++[false;false;true])++[false;false]) (SDec 10)).
    rewrite <- app_assoc. exact (proj1 (proj2 (source_mp_compare_leaves ctx P))).
  - lia.
  - exact N.
  - change (break_pc 0 (rev ((ctx++[false;false;true])++[false;false])++[false]) =
      Some(true::rev (ctx++[false;false;true;false])++[false],0)).
    rewrite !rev_app_distr. reflexivity.
Qed.

Lemma source_mp_eq_loop_right_zero ctx rs : SourcePrefix source_graph source_root ctx 684 -> nth_error rs 10=Some 0 ->
  SourceProgramStep (ctx++[false;false;true],rs) (ctx++[false;false;true;true],rs).
Proof.
  intros P N. replace (ctx++[false;false;true;true]) with
    (return_word (true::rev (ctx++[false;false;true])++[false]))
    by (rewrite constructor_return_word, <- app_assoc; reflexivity).
  eapply constructor_step_dec_zero with (pad:=2) (i:=10) (count:=1).
  - change (SourceSelect source_graph source_root ((ctx++[false;false;true])++[false;false]) (SDec 10)).
    rewrite <- app_assoc. exact (proj1 (proj2 (source_mp_compare_leaves ctx P))).
  - lia.
  - exact N.
  - change (break_pc 1 (rev ((ctx++[false;false;true])++[false;false])++[false]) =
      Some(true::rev (ctx++[false;false;true])++[false],1)).
    rewrite !rev_app_distr. reflexivity.
Qed.

Lemma source_mp_eq_loop_continue ctx rs : SourcePrefix source_graph source_root ctx 684 ->
  SourceProgramStep (ctx++[false;false;true;false;true],rs) (ctx++[false;false],rs).
Proof.
  intro P. replace (ctx++[false;false]) with (rev (rev (ctx++[false;false]))) by apply rev_involutive.
  replace (ctx++[false;false;true;false;true]) with ((ctx++[false;false;true;false])++[true])
    by (rewrite <- app_assoc; reflexivity).
  eapply constructor_step_continue with (k:=1) (count:=2).
  - rewrite <- app_assoc. exact (proj1 (proj2 (proj2 (source_mp_compare_leaves ctx P)))).
  - rewrite !rev_app_distr. cbn [rev app continue_pc]. reflexivity.
Qed.

Lemma source_mp_eq_test_right_zero ctx rs : SourcePrefix source_graph source_root ctx 684 -> nth_error rs 10=Some 0 ->
  SourceProgramStep (ctx++[false;true],rs) (ctx++[true],rs).
Proof.
  intros P N. rewrite <- constructor_return_word.
  eapply constructor_step_dec_zero with (pad:=1) (i:=10) (count:=2).
  - change (SourceSelect source_graph source_root ((ctx++[false;true])++[false]) (SDec 10)).
    rewrite <- app_assoc. exact (proj1 (proj2 (proj2 (proj2 (proj2 (source_mp_compare_leaves ctx P)))))).
  - lia.
  - exact N.
  - change (break_pc 1 (rev ((ctx++[false;true])++[false])++[false]) = Some(true::rev ctx++[false],2)).
    rewrite !rev_app_distr. reflexivity.
Qed.

Lemma source_mp_eq_test_right_positive ctx rs n : SourcePrefix source_graph source_root ctx 684 -> nth_error rs 10=Some(S n) ->
  SourceProgramStep (ctx++[false;true],rs)
    (ctx++[false;true;true],set_register 10 n rs++[0]).
Proof.
  intros P N. replace (ctx++[false;true;true]) with
    (return_word (true::rev (ctx++[false;true])++[false]))
    by (rewrite constructor_return_word, <- app_assoc; reflexivity).
  eapply constructor_step_dec_positive with (pad:=1) (i:=10) (count:=0).
  - change (SourceSelect source_graph source_root ((ctx++[false;true])++[false]) (SDec 10)).
    rewrite <- app_assoc. exact (proj1 (proj2 (proj2 (proj2 (proj2 (source_mp_compare_leaves ctx P)))))).
  - lia.
  - exact N.
  - change (break_pc 0 (rev ((ctx++[false;true])++[false])++[false]) =
      Some(true::rev (ctx++[false;true])++[false],0)).
    rewrite !rev_app_distr. reflexivity.
Qed.

Lemma source_mp_eq_loop_left_zero ctx rs : SourcePrefix source_graph source_root ctx 684 -> nth_error rs 9=Some 0 ->
  SourceProgramStep (ctx++[false;false],rs) (ctx++[false;true],rs).
Proof.
  intros P N. replace (ctx++[false;true]) with (return_word (true::rev (ctx++[false])++[false]))
    by (rewrite constructor_return_word, <- app_assoc; reflexivity).
  eapply constructor_step_dec_zero with (pad:=1) (i:=9) (count:=1).
  - change (SourceSelect source_graph source_root ((ctx++[false;false])++[false]) (SDec 9)).
    rewrite <- app_assoc. exact (proj1 (source_mp_compare_leaves ctx P)).
  - lia.
  - exact N.
  - change (break_pc 1 (rev ((ctx++[false;false])++[false])++[false]) =
      Some(true::rev (ctx++[false])++[false],1)). rewrite !rev_app_distr. reflexivity.
Qed.

Lemma source_mp_eq_loop_left_positive ctx rs n : SourcePrefix source_graph source_root ctx 684 -> nth_error rs 9=Some(S n) ->
  SourceProgramStep (ctx++[false;false],rs) (ctx++[false;false;true],set_register 9 n rs++[0]).
Proof.
  intros P N. replace (ctx++[false;false;true]) with
    (return_word (true::rev (ctx++[false;false])++[false]))
    by (rewrite constructor_return_word, <- app_assoc; reflexivity).
  eapply constructor_step_dec_positive with (pad:=1) (i:=9) (count:=0).
  - change (SourceSelect source_graph source_root ((ctx++[false;false])++[false]) (SDec 9)).
    rewrite <- app_assoc. exact (proj1 (source_mp_compare_leaves ctx P)).
  - lia.
  - exact N.
  - change (break_pc 0 (rev ((ctx++[false;false])++[false])++[false]) =
      Some(true::rev (ctx++[false;false])++[false],0)). rewrite !rev_app_distr. reflexivity.
Qed.

Lemma source_mp_eq_break_left ctx rs : SourcePrefix source_graph source_root ctx 684 ->
  SourceProgramStep (ctx++[false;false;true;true;true],rs) (loop_return ctx,rs).
Proof.
  intro P. destruct (loop_return_spec ctx) as [out [n [Ret E]]]. rewrite E.
  replace (ctx++[false;false;true;true;true]) with ((ctx++[false;false;true;true])++[true])
    by (rewrite <- app_assoc; reflexivity).
  eapply source_program_step with (n:=0). rewrite app_nil_r.
  eapply source_break with (k:=2) (n:=S(S(S(S n)))).
  - rewrite <- app_assoc. exact (proj1 (proj2 (proj2 (proj2 (source_mp_compare_leaves ctx P))))).
  - rewrite !rev_app_distr. cbn [rev app break_pc]. now rewrite Ret.
Qed.

Lemma source_mp_eq_break_right ctx rs : SourcePrefix source_graph source_root ctx 684 ->
  SourceProgramStep (ctx++[false;true;true;true],rs) (loop_return ctx,rs).
Proof.
  intro P. destruct (loop_return_spec ctx) as [out [n [Ret E]]]. rewrite E.
  replace (ctx++[false;true;true;true]) with ((ctx++[false;true;true])++[true])
    by (rewrite <- app_assoc; reflexivity).
  eapply source_program_step with (n:=0). rewrite app_nil_r.
  eapply source_break with (k:=1) (n:=S(S(S n))).
  - rewrite <- app_assoc. exact (proj2 (proj2 (proj2 (proj2 (proj2 (source_mp_compare_leaves ctx P)))))).
  - rewrite !rev_app_distr. cbn [rev app break_pc]. now rewrite Ret.
Qed.

Print Assumptions source_mp_eq_loop_left_zero.
Print Assumptions source_mp_eq_break_left.
Print Assumptions source_mp_eq_break_right.

Print Assumptions source_mp_compare_tree.
Print Assumptions source_mp_compare_prefixes.
Print Assumptions source_mp_compare_leaves.
