(** Literal source execution at the entry of TMBuilder.unpair.

    The arithmetic invariant for the whole routine is proved separately in
    ConstructorStructured; these lemmas expose the actual compiled source
    control and the physical register-list extension at its outer test. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import RuntimeControl RuntimeCalls CompilerSyntax CompilerData CompilerReverse CompilerContexts
  CompilerExecution CompilerRegisters ConstructorGraph ConstructorPaths ConstructorPC ConstructorControl.
From Berkeley Require Import CompilerLoopBase CompilerLoops.
Import ListNotations.

Lemma unpair_input_leaf ctx : SourcePrefix source_graph source_root ctx 29 ->
  SourceSelect source_graph source_root (ctx++[false]) (SDec 3).
Proof.
  intro P. destruct source_internal_trees as [_ [_ [U _]]].
  destruct (constructor_unpair_leaf_paths _ _ _ _ U) as [Sel _].
  eapply source_select_in_context; eassumption.
Qed.

Theorem source_unpair_input_zero ctx rs :
  SourcePrefix source_graph source_root ctx 29 -> nth_error rs 3 = Some 0 ->
  SourceProgramStep (ctx,rs) (loop_return ctx,rs).
Proof.
  intros P H. destruct (loop_return_spec ctx) as [out [n [Ret E]]]. rewrite E.
  eapply constructor_step_dec_zero with (pad:=1) (i:=3) (count:=S n).
  - change (SourceSelect source_graph source_root (ctx++[false]) (SDec 3)).
    now apply unpair_input_leaf.
  - lia.
  - exact H.
  - change (break_pc 1 (rev (ctx++[false])++[false]) = Some(out,S n)).
    now apply constructor_first_test_return.
Qed.

Theorem source_unpair_input_positive ctx rs n :
  SourcePrefix source_graph source_root ctx 29 -> nth_error rs 3 = Some (S n) ->
  SourceProgramStep (ctx,rs) (ctx++[true],set_register 3 n rs ++ [0]).
Proof.
  intros P H. rewrite <- constructor_return_word.
  eapply constructor_step_dec_positive with (pad:=1) (i:=3) (count:=0).
  - change (SourceSelect source_graph source_root (ctx++[false]) (SDec 3)).
    now apply unpair_input_leaf.
  - lia.
  - exact H.
  - change (break_pc 0 (rev (ctx++[false])++[false]) =
              Some(true::rev ctx++[false],0)).
    pose proof (proj1 (constructor_child_return ctx 0)) as C.
    now rewrite app_nil_r in C.
Qed.

Lemma unpair_increment_leaf ctx : SourcePrefix source_graph source_root ctx 29 ->
  SourceSelect source_graph source_root (ctx++[true;false]) (SInc 8).
Proof.
  intro P. destruct source_internal_trees as [_ [_ [U _]]].
  destruct (constructor_unpair_leaf_paths _ _ _ _ U) as [_ [Sel _]].
  eapply source_select_in_context; eassumption.
Qed.
Lemma unpair_output_test_leaf ctx : SourcePrefix source_graph source_root ctx 29 ->
  SourceSelect source_graph source_root (ctx++[true;true;false;false]) (SDec 9).
Proof.
  intro P. destruct source_internal_trees as [_ [_ [U _]]].
  destruct (constructor_unpair_leaf_paths _ _ _ _ U) as [_ [_ [Sel _]]].
  eapply source_select_in_context; eassumption.
Qed.
Lemma unpair_continue_early_leaf ctx : SourcePrefix source_graph source_root ctx 29 ->
  SourceSelect source_graph source_root (ctx++[true;true;false;true]) (SContinue 3).
Proof.
  intro P. destruct source_internal_trees as [_ [_ [U _]]].
  destruct (constructor_unpair_leaf_paths _ _ _ _ U) as [_ [_ [_ [Sel _]]]].
  eapply source_select_in_context; eassumption.
Qed.
Lemma unpair_continue_late_leaf ctx : SourcePrefix source_graph source_root ctx 29 ->
  SourceSelect source_graph source_root (ctx++[true;true;true;true]) (SContinue 4).
Proof.
  intro P. destruct source_internal_trees as [_ [_ [U _]]].
  destruct (constructor_unpair_leaf_paths _ _ _ _ U) as [_ [_ [_ [_ Sel]]]].
  eapply source_select_in_context; eassumption.
Qed.

Lemma source_unpair_increment ctx rs x :
  SourcePrefix source_graph source_root ctx 29 -> nth_error rs 8 = Some x ->
  SourceProgramStep (ctx++[true],rs) (ctx++[true;true],set_register 8 (S x) rs).
Proof.
  intros P H.
  replace (ctx++[true;true]) with (return_word (true::rev (ctx++[true])++[false]))
    by (rewrite constructor_return_word, <- app_assoc; reflexivity).
  eapply constructor_step_inc with (pad:=1) (i:=8) (count:=0).
  - change (SourceSelect source_graph source_root ((ctx++[true])++[false]) (SInc 8)).
    rewrite <- app_assoc. now apply unpair_increment_leaf.
  - lia.
  - exact H.
  - change (break_pc 0 (rev ((ctx++[true])++[false])++[false]) =
      Some (true::rev (ctx++[true])++[false],0)).
    pose proof (proj1 (constructor_child_return (ctx++[true]) 0)) as C.
    now rewrite app_nil_r in C.
Qed.

Lemma source_unpair_test_zero ctx rs :
  SourcePrefix source_graph source_root ctx 29 -> nth_error rs 9 = Some 0 ->
  SourceProgramStep (ctx++[true;true],rs) (ctx++[true;true;true],rs).
Proof.
  intros P H. destruct (constructor_inner_test_zero ctx) as [Ret Out]. rewrite <- Out.
  eapply constructor_step_dec_zero with (pad:=2) (i:=9) (count:=1).
  - change (SourceSelect source_graph source_root ((ctx++[true;true])++[false;false]) (SDec 9)).
    rewrite <- app_assoc. now apply unpair_output_test_leaf.
  - lia.
  - exact H.
  - change (break_pc 1 (rev ((ctx++[true;true])++[false;false])++[false]) =
      Some (true::true::true::rev ctx++[false],1)).
    rewrite <- app_assoc. exact Ret.
Qed.

Lemma source_unpair_test_positive ctx rs y :
  SourcePrefix source_graph source_root ctx 29 -> nth_error rs 9 = Some (S y) ->
  SourceProgramStep (ctx++[true;true],rs)
    (ctx++[true;true;false;true],set_register 9 y rs ++ [0]).
Proof.
  intros P H.
  replace (ctx++[true;true;false;true]) with
    (return_word (true::rev (ctx++[true;true;false])++[false]))
    by (rewrite constructor_return_word, <- app_assoc; reflexivity).
  eapply constructor_step_dec_positive with (pad:=2) (i:=9) (count:=0).
  - change (SourceSelect source_graph source_root ((ctx++[true;true])++[false;false]) (SDec 9)).
    rewrite <- app_assoc. now apply unpair_output_test_leaf.
  - lia.
  - exact H.
  - change (break_pc 0 (rev ((ctx++[true;true])++[false;false])++[false]) =
      Some (true::rev (ctx++[true;true;false])++[false],0)).
    rewrite <- app_assoc.
    pose proof (proj1 (constructor_child_return (ctx++[true;true;false]) 0)) as C.
    rewrite app_nil_r in C. rewrite <- app_assoc in C. exact C.
Qed.

Lemma source_unpair_continue_early ctx rs :
  SourcePrefix source_graph source_root ctx 29 ->
  SourceProgramStep (ctx++[true;true;false;true],rs) (ctx,rs).
Proof.
  intro P. replace ctx with (rev (rev ctx)) at 2 by apply rev_involutive.
  replace (ctx++[true;true;false;true]) with ((ctx++[true;true;false])++[true])
    by (rewrite <- app_assoc; reflexivity).
  eapply constructor_step_continue with (k:=2) (count:=3).
  - rewrite <- app_assoc. now apply unpair_continue_early_leaf.
  - apply constructor_unpair_continue_early.
Qed.

Lemma source_unpair_continue_late ctx rs :
  SourcePrefix source_graph source_root ctx 29 ->
  SourceProgramStep (ctx++[true;true;true;true],rs) (ctx,rs).
Proof.
  intro P. replace ctx with (rev (rev ctx)) at 2 by apply rev_involutive.
  replace (ctx++[true;true;true;true]) with ((ctx++[true;true;true])++[true])
    by (rewrite <- app_assoc; reflexivity).
  eapply constructor_step_continue with (k:=3) (count:=3).
  - rewrite <- app_assoc. now apply unpair_continue_late_leaf.
  - apply constructor_unpair_continue_late.
Qed.

Theorem source_unpair_positive_cycle ctx rs n x y :
  SourcePrefix source_graph source_root ctx 29 -> 11 <= length rs ->
  nth_error rs 3 = Some (S n) -> nth_error rs 8 = Some x -> nth_error rs 9 = Some (S y) ->
  SourceProgramRuns (ctx,rs)
    (ctx, set_register 9 y (set_register 8 (S x) (set_register 3 n rs ++ [0])) ++ [0]).
Proof.
  intros P L N X Y.
  assert (X' : nth_error (set_register 3 n rs ++ [0]) 8 = Some x).
  { rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact X. }
  assert (Y' : nth_error (set_register 8 (S x) (set_register 3 n rs ++ [0])) 9 = Some (S y)).
  { rewrite nth_error_set_other by lia. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact Y. }
  eapply source_program_next; [apply source_unpair_input_positive; eassumption|].
  eapply source_program_next; [apply source_unpair_increment; eassumption|].
  eapply source_program_next; [apply source_unpair_test_positive; eassumption|].
  eapply source_program_next; [apply source_unpair_continue_early; eassumption|].
  constructor.
Qed.

Lemma constructor_loop_return_false ctx : loop_return (ctx++[false]) = ctx++[true].
Proof.
  unfold loop_return. pose proof (proj1 (constructor_child_return ctx 0)) as E.
  rewrite app_nil_r in E. rewrite E. apply constructor_return_word.
Qed.

(** The other actual unpair cycle: out2=0, so out1 is drained into it
    before the source's four-level continue returns to the outer test. *)
Theorem source_unpair_zero_output_cycle ctx rs n x :
  SourcePrefix source_graph source_root ctx 29 -> 11 <= length rs ->
  nth_error rs 3 = Some (S n) -> nth_error rs 8 = Some x -> nth_error rs 9 = Some 0 ->
  let r1 := set_register 3 n rs ++ [0] in
  let r2 := set_register 8 (S x) r1 in
  SourceProgramRuns (ctx,rs)
    (ctx, set_register 9 (S x) (set_register 8 0 r2) ++ repeat 0 (S x)).
Proof.
  intros P L N X Y. cbn zeta.
  set (r1 := set_register 3 n rs ++ [0]).
  set (r2 := set_register 8 (S x) r1).
  assert (L1 : 11 <= length r1).
  { unfold r1. rewrite app_length, set_register_length. simpl. lia. }
  assert (L2 : 11 <= length r2) by (unfold r2; rewrite set_register_length; exact L1).
  assert (X1 : nth_error r1 8 = Some x).
  { unfold r1. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact X. }
  assert (Y1 : nth_error r1 9 = Some 0).
  { unfold r1. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact Y. }
  assert (X2 : nth_error r2 8 = Some (S x)).
  { unfold r2. apply nth_error_set_same. lia. }
  assert (Y2 : nth_error r2 9 = Some 0).
  { unfold r2. rewrite nth_error_set_other by lia. exact Y1. }
  destruct constructor_internal_prefixes as [_ [_ [_ [_ [_ [_ [_ Sub]]]]]]].
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P Sub) as LoopPrefix.
  destruct source_internal_trees as [_ [_ [_ [_ [_ [_ [_ LoopTree]]]]]]].
  destruct (while1_transfer_nonempty (ctx++[true;true;true;false]) 24 r2 8 9 (S x) 0
              LoopPrefix LoopTree ltac:(lia) ltac:(lia) ltac:(lia) L2 X2 Y2)
    as [mid [First Rest]].
  cbn [Nat.add_0_l] in Rest.
  assert (Ret : loop_return (ctx++[true;true;true;false]) = ctx++[true;true;true;true]).
  { replace (ctx++[true;true;true;false]) with ((ctx++[true;true;true])++[false])
      by (rewrite <- app_assoc; reflexivity).
    rewrite constructor_loop_return_false, <- app_assoc. reflexivity. }
  rewrite Ret in Rest.
  eapply source_program_next; [apply source_unpair_input_positive; eassumption|].
  eapply source_program_next; [apply source_unpair_increment; eassumption|].
  eapply source_program_next; [apply source_unpair_test_zero; eassumption|].
  eapply source_program_next with (t:=mid).
  - eapply constructor_unpad_first_step with (pad:=1).
    change (SourceProgramStep ((ctx++[true;true;true])++[false],r2) mid).
    rewrite <- app_assoc. exact First.
  - eapply source_program_runs_trans; [exact Rest|].
    eapply source_program_next; [apply source_unpair_continue_late; eassumption|constructor].
Qed.

Print Assumptions source_unpair_input_zero.
Print Assumptions source_unpair_input_positive.
Print Assumptions source_unpair_positive_cycle.
Print Assumptions source_unpair_zero_output_cycle.
