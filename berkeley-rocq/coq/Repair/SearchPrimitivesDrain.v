(** Source execution of while_decnz(register, ()), the proof-search clear. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import RuntimeControl RuntimeCalls RuntimeJumps CompilerSyntax CompilerReverse CompilerContexts CompilerRegisters ConstructorPC.
From Repair Require Import ConstructorGraph CompilerData SourceExecution CompilerTrees CompilerLoopBase CompilerLoops ConstructorControl.
Import ListNotations.

Definition tree_drain i := CTSeq (CTDec i) (CTContinue 1).

Lemma source_drain_leaves ctx root i :
  SourcePrefix source_graph source_root ctx root -> unfold_root root = Some (tree_drain i) ->
  SourceSelect source_graph source_root (ctx++[false]) (SDec i) /\
  SourceSelect source_graph source_root (ctx++[true]) (SContinue 1).
Proof.
  intros P T. split; eapply source_select_in_context; [exact P| |exact P|];
    eapply root_unfold_selection; [exact T| |exact T|]; unfold tree_drain.
  - apply tree_select_left, tree_select_dec.
  - apply tree_select_right, tree_select_continue.
Qed.

Lemma source_drain_zero_step ctx root i rs :
  SourcePrefix source_graph source_root ctx root -> unfold_root root = Some (tree_drain i) ->
  i < 11 -> nth_error rs i = Some 0 -> SourceProgramStep (ctx,rs) (loop_return ctx,rs).
Proof.
  intros P T I N. destruct (loop_return_spec ctx) as [out [n [Ret E]]]. rewrite E.
  eapply constructor_step_dec_zero with (pad:=1) (i:=i) (count:=S n).
  - change (SourceSelect source_graph source_root (ctx++[false]) (SDec i)).
    exact (proj1 (source_drain_leaves _ _ _ P T)).
  - exact I.
  - exact N.
  - change (break_pc 1 (rev (ctx++[false])++[false]) = Some(out,S n)).
    now apply constructor_first_test_return.
Qed.

Lemma source_drain_positive_cycle ctx root i rs n :
  SourcePrefix source_graph source_root ctx root -> unfold_root root = Some (tree_drain i) ->
  i < 11 -> nth_error rs i = Some (S n) ->
  SourceProgramRuns (ctx,rs) (ctx,set_register i n rs ++ [0]).
Proof.
  intros P T I N. eapply source_program_next with (t:=(ctx++[true],set_register i n rs ++ [0])).
  - replace (ctx++[true]) with (return_word (true::rev ctx++[false]))
      by apply constructor_return_word.
    eapply constructor_step_dec_positive with (pad:=1) (i:=i) (count:=0).
    + change (SourceSelect source_graph source_root (ctx++[false]) (SDec i)).
      exact (proj1 (source_drain_leaves _ _ _ P T)).
    + exact I.
    + exact N.
    + change (break_pc 0 (rev (ctx++[false])++[false]) = Some(true::rev ctx++[false],0)).
      pose proof (proj1 (constructor_child_return ctx 0)) as C. now rewrite app_nil_r in C.
  - eapply source_program_next; [|constructor].
    replace ctx with (rev (rev ctx)) at 2 by apply rev_involutive.
    eapply constructor_step_continue with (k:=0) (count:=0).
    + exact (proj2 (source_drain_leaves _ _ _ P T)).
    + destruct (rev ctx); reflexivity.
Qed.

Theorem source_drain ctx root i rs n :
  SourcePrefix source_graph source_root ctx root -> unfold_root root = Some (tree_drain i) ->
  i < 11 -> 11 <= length rs -> nth_error rs i = Some n ->
  SourceProgramRuns (ctx,rs) (loop_return ctx,set_register i 0 rs ++ repeat 0 n).
Proof.
  intros P T I. revert rs. induction n as [|n IH]; intros rs L N.
  - cbn [repeat]. rewrite app_nil_r, (set_register_noop _ _ _ N).
    eapply source_program_next; [eapply source_drain_zero_step; eassumption|constructor].
  - set (rs' := set_register i n rs ++ [0]).
    assert (L' : 11 <= length rs') by (unfold rs'; rewrite app_length,set_register_length; simpl; lia).
    assert (N' : nth_error rs' i = Some n).
    { unfold rs'. rewrite nth_error_app1 by (rewrite set_register_length; lia).
      apply nth_error_set_same. lia. }
    pose proof (IH rs' L' N') as Tail.
    unfold rs' in Tail. rewrite set_register_append in Tail by (rewrite set_register_length; lia).
    rewrite set_register_twice in Tail. cbn [repeat].
    eapply source_program_runs_trans; [eapply source_drain_positive_cycle; eassumption|].
    change (SourceProgramRuns (ctx,set_register i n rs ++ [0])
      (loop_return ctx, set_register i 0 rs ++ ([0] ++ repeat 0 n))).
    rewrite app_assoc. exact Tail.
Qed.

Theorem source_drain_nonempty ctx root i rs n :
  SourcePrefix source_graph source_root ctx root -> unfold_root root = Some (tree_drain i) ->
  i < 11 -> 11 <= length rs -> nth_error rs i = Some n ->
  exists mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (loop_return ctx,set_register i 0 rs ++ repeat 0 n).
Proof.
  intros P T I L N. destruct n as [|n].
  - cbn [repeat]. rewrite app_nil_r, (set_register_noop _ _ _ N).
    exists (loop_return ctx,rs). split; [eapply source_drain_zero_step; eassumption|constructor].
  - eapply source_runs_nonempty_when_distinct.
    + eapply source_drain; eassumption.
    + intro E. apply (f_equal (fun z => length (snd z))) in E. cbn [snd] in E.
      rewrite app_length, repeat_length, set_register_length in E. lia.
Qed.

Local Transparent source_graph unfold_root.
Theorem source_drain_roots :
  unfold_root 632 = Some (tree_drain 4) /\ unfold_root 633 = Some (tree_drain 5) /\
  unfold_root 634 = Some (tree_drain 6) /\ unfold_root 635 = Some (tree_drain 7) /\
  unfold_root 661 = Some (tree_drain 9) /\ unfold_root 662 = Some (tree_drain 10) /\
  unfold_root 675 = Some (tree_drain 2) /\ unfold_root 679 = Some (tree_drain 8).
Proof. vm_compute. repeat split; reflexivity. Qed.

Print Assumptions source_drain.
Print Assumptions source_drain_nonempty.
Print Assumptions source_drain_roots.
