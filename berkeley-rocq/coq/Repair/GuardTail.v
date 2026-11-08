(** Full repaired source contract for the post-emission guarded-distinction
    suffix: compare restored variable names and clear the formula on equality. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerReverse CompilerContexts CompilerRegisters ConstructorPaths ConstructorPush.
From Repair Require Import ConstructorGraph CompilerData SourceExecution CompilerTrees GuardCopy GuardCompare Frame.
Import ListNotations.

Definition guard_tail_frame (before after : list nat) :=
  forall i, i<11 -> i<>2 -> nth_error after i=nth_error before i.

Local Transparent source_graph unfold_root.
Lemma guard_tail_source_shape :
  nth_error source_graph source_guarded_root=Some(SNode source_plain_distinction_root,SNode 852) /\
  SourcePrefix source_graph 852 [false] 683 /\
  SourcePrefix source_graph 852 [true;false] 16 /\
  SourcePrefix source_graph 852 [true;true;false] 656 /\
  SourcePrefix source_graph 852 [true;true;true;false] 20 /\
  SourcePrefix source_graph 852 [true;true;true;true] 684 /\
  unfold_root 683=Some(tree_while2 5 8 9) /\
  unfold_root 16=Some(tree_while1 8 5) /\
  unfold_root 656=Some(tree_while2 6 8 10) /\
  unfold_root 20=Some(tree_while1 8 6).
Proof.
  repeat split; try (apply source_prefix_find_sound); vm_compute; reflexivity.
Qed.
Local Opaque source_graph unfold_root.

Lemma guard_loop_return_two_true ctx : loop_return (ctx++[true;true])=loop_return ctx.
Proof.
  replace (ctx++[true;true]) with ((ctx++[true])++[true]) by now rewrite <- app_assoc.
  now rewrite !constructor_loop_return_true.
Qed.

Theorem repaired_guard_tail_nonempty ctx a b top rs :
  SourcePrefix source_graph source_root ctx 852 -> 11<=length rs ->
  nth_error rs 2=Some top -> nth_error rs 5=Some a -> nth_error rs 6=Some b ->
  nth_error rs 8=Some 0 -> nth_error rs 9=Some 0 -> nth_error rs 10=Some 0 ->
  exists result mid,
    SourceProgramStep (ctx,rs) mid /\ SourceProgramRuns mid (loop_return ctx,result) /\
    11<=length result /\ nth_error result 2=Some(if Nat.eqb a b then 0 else top) /\
    guard_tail_frame rs result /\ exists k, skipn 11 result=skipn 11 rs++repeat 0 k.
Proof.
  intros Prefix Len Top A B S8 S9 S10.
  destruct guard_tail_source_shape as [_ [C1 [C2 [C3 [C4 [CE [T1 [T2 [T3 T4]]]]]]]]].
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ Prefix C1) as P1.
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ Prefix C2) as P2.
  destruct (guarded_copy_nonempty ctx 683 16 5 9 rs a P1 P2 T1 T2
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Len A S8 S9)
    as [r1 [mid [First [Run1 [L1 [A9 [F1 _]]]]]]].
  assert (A1 : nth_error r1 5=Some a) by (rewrite F1 by lia; exact A).
  assert (B1 : nth_error r1 6=Some b) by (rewrite F1 by lia; exact B).
  assert (S81 : nth_error r1 8=Some 0) by (rewrite F1 by lia; exact S8).
  assert (S101 : nth_error r1 10=Some 0) by (rewrite F1 by lia; exact S10).
  assert (Top1 : nth_error r1 2=Some top) by (rewrite F1 by lia; exact Top).
  set (ctx2:=ctx++[true;true]).
  assert (P3 : SourcePrefix source_graph source_root (ctx2++[false]) 656).
  { unfold ctx2. rewrite <- app_assoc. cbn [app].
    eapply constructor_source_prefix_concat; eassumption. }
  assert (P4 : SourcePrefix source_graph source_root (ctx2++[true;false]) 20).
  { unfold ctx2. rewrite <- app_assoc. cbn [app].
    eapply constructor_source_prefix_concat; eassumption. }
  destruct (guarded_copy_nonempty ctx2 656 20 6 10 r1 b P3 P4 T3 T4
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) L1 B1 S81 S101)
    as [r2 [mid2 [First2 [Run2 [L2 [B10 [F2 _]]]]]]].
  assert (A2 : nth_error r2 5=Some a) by (rewrite F2 by lia; exact A1).
  assert (B2 : nth_error r2 6=Some b) by (rewrite F2 by lia; exact B1).
  assert (S82 : nth_error r2 8=Some 0) by (rewrite F2 by lia; exact S81).
  assert (A92 : nth_error r2 9=Some a) by (rewrite F2 by lia; exact A9).
  assert (Top2 : nth_error r2 2=Some top) by (rewrite F2 by lia; exact Top1).
  set (ctx3:=ctx2++[true;true]).
  assert (Peq : SourcePrefix source_graph source_root ctx3 684).
  { unfold ctx3,ctx2. rewrite <- app_assoc. cbn [app].
    eapply constructor_source_prefix_concat; eassumption. }
  destruct (repaired_guard_compare_nonempty ctx3 a b top r2 Peq L2 Top2 A92 B10)
    as [result [mid3 [First3 [Run3 [L3 [T3' [S93 [S103 [F3 _]]]]]]]]].
  unfold ctx3,ctx2 in Run3. rewrite !guard_loop_return_two_true in Run3.
  assert (Rest : SourceProgramRuns mid (loop_return ctx,result)).
  { eapply source_program_runs_trans; [exact Run1|]. eapply source_program_next; [exact First2|].
    eapply source_program_runs_trans; [exact Run2|]. eapply source_program_next; eassumption. }
  assert (Full : SourceProgramRuns (ctx,rs) (loop_return ctx,result))
    by (eapply source_program_next; eassumption).
  destruct (repair_source_runs_zero_suffix _ _ Full Len) as [pad [Suffix Length]].
  exists result,mid. split; [exact First|]. split; [exact Rest|].
  cbn [snd] in Suffix,Length. repeat split; try assumption; try lia.
  - unfold guard_tail_frame. intros i I I2.
    destruct (Nat.eq_dec i 9) as [->|I9]; [now rewrite S93,S9|].
    destruct (Nat.eq_dec i 10) as [->|I10]; [now rewrite S103,S10|].
    rewrite F3 by lia. rewrite F2 by lia. now apply F1.
  - now exists pad.
Qed.

Print Assumptions guard_tail_source_shape.
Print Assumptions repaired_guard_tail_nonempty.
