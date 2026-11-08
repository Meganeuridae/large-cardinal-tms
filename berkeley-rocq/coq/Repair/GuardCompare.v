(** Actual repaired-source execution of the guarded comparison subtree.
    Equality takes the body that clears topwff; inequality skips that body. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerReverse CompilerContexts CompilerRegisters ConstructorPaths ConstructorPush.
From Repair Require Import ConstructorGraph CompilerData SourceExecution CompilerTrees SearchPrimitivesDrain
  GuardEqControl GuardEq Frame.
Import ListNotations.

Definition guard_compare_frame (before after : list nat) :=
  forall i, i<11 -> i<>2 -> i<>9 -> i<>10 -> nth_error after i=nth_error before i.

Theorem repaired_guard_compare_nonempty ctx a b top rs :
  SourcePrefix source_graph source_root ctx 684 -> 11<=length rs ->
  nth_error rs 2=Some top -> nth_error rs 9=Some a -> nth_error rs 10=Some b ->
  exists result mid,
    SourceProgramStep (ctx,rs) mid /\ SourceProgramRuns mid (loop_return ctx,result) /\
    11<=length result /\ nth_error result 2=Some (if Nat.eqb a b then 0 else top) /\
    nth_error result 9=Some 0 /\ nth_error result 10=Some 0 /\ guard_compare_frame rs result /\
    exists k, skipn 11 result=skipn 11 rs++repeat 0 k.
Proof.
  intros Prefix Len Top A B.
  destruct (source_mp_eq_test_nonempty ctx a b rs Prefix Len A B)
    as [r1 [mid [First [Test [L1 [A1 [B1 F1]]]]]]].
  assert (Top1 : nth_error r1 2=Some top) by (rewrite F1 by lia; exact Top).
  unfold eq_test_exit in Test. destruct (Nat.eqb a b) eqn:Equal.
  - assert (Pbody : SourcePrefix source_graph source_root (ctx++[true]) 675).
    { eapply constructor_source_prefix_concat; [exact Prefix|].
      exact (proj1 (proj2 (proj2 source_mp_compare_prefixes))). }
    assert (Tree : unfold_root 675=Some(tree_drain 2)).
    { exact (proj2 (proj2 (proj2 source_mp_compare_prefixes))). }
    destruct (source_drain_nonempty (ctx++[true]) 675 2 r1 top Pbody Tree ltac:(lia) L1 Top1)
      as [m2 [DrainFirst DrainRest]].
    rewrite constructor_loop_return_true in DrainRest.
    set (result := set_register 2 0 r1++repeat 0 top) in *.
    assert (Run : SourceProgramRuns mid (loop_return ctx,result)).
    { eapply source_program_runs_trans; [exact Test|]. eapply source_program_next; eassumption. }
    assert (Full : SourceProgramRuns (ctx,rs) (loop_return ctx,result))
      by (eapply source_program_next; eassumption).
    destruct (repair_source_runs_zero_suffix _ _ Full Len) as [k [Suffix Length]].
    exists result,mid. split; [exact First|]. split; [exact Run|].
    cbn [snd] in Suffix,Length. repeat split; try lia.
    + unfold result. rewrite nth_error_app1 by (rewrite set_register_length; lia).
      apply nth_error_set_same. lia.
    + unfold result. rewrite nth_error_app1 by (rewrite set_register_length; lia).
      rewrite nth_error_set_other by lia. exact A1.
    + unfold result. rewrite nth_error_app1 by (rewrite set_register_length; lia).
      rewrite nth_error_set_other by lia. exact B1.
    + unfold guard_compare_frame. intros i I I2 I9 I10. unfold result.
      rewrite nth_error_app1 by (rewrite set_register_length; lia).
      rewrite nth_error_set_other by lia. now apply F1.
    + now exists k.
  - assert (Full : SourceProgramRuns (ctx,rs) (loop_return ctx,r1))
      by (eapply source_program_next; eassumption).
    destruct (repair_source_runs_zero_suffix _ _ Full Len) as [k [Suffix Length]].
    exists r1,mid. split; [exact First|]. split; [exact Test|]. cbn [snd] in Suffix,Length.
    repeat split; try assumption; try lia.
    + unfold guard_compare_frame. intros i I I2 I9 I10. now apply F1.
    + now exists k.
Qed.

Print Assumptions repaired_guard_compare_nonempty.
