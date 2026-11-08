(** Source execution of the two component blocks of the Cantor pair loop. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import RuntimeControl CompilerSyntax CompilerRegisters ConstructorPC CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerExecution CompilerLoopBase CompilerLoops ConstructorGraph ConstructorPaths ConstructorControl ConstructorUnpair ConstructorPairControl SourceExecution.
Import ListNotations.

Definition pair_head_store i j k a b c rs :=
  set_register k (c+a) (set_register j (b+a) (set_register i 0 rs)) ++ repeat 0 a.

Theorem source_pair_head_nonempty ctx root i j k first second rs a b c :
  pair_layout root i j k first second -> SourcePrefix source_graph source_root ctx root ->
  i < 11 -> j < 11 -> k < 11 -> i<>j -> i<>k -> j<>k -> 11 <= length rs ->
  nth_error rs i = Some a -> nth_error rs j = Some b -> nth_error rs k = Some c ->
  exists mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (ctx++[true],pair_head_store i j k a b c rs).
Proof.
  intros Layout P I J K IJ IK JK L A B C.
  destruct Layout as [Tree FPrefix FTree SPrefix STree].
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P FPrefix) as Prefix.
  destruct (while2_transfer_nonempty (ctx++[false]) first rs i j k a b c
    Prefix FTree I J K IJ IK JK L A B C) as [mid [First Rest]].
  rewrite constructor_loop_return_false in Rest.
  exists mid. split.
  - eapply constructor_unpad_first_step with (pad:=1). exact First.
  - exact Rest.
Qed.

Theorem source_pair_head ctx root i j k first second rs a b c :
  pair_layout root i j k first second -> SourcePrefix source_graph source_root ctx root ->
  i < 11 -> j < 11 -> k < 11 -> i<>j -> i<>k -> j<>k -> 11 <= length rs ->
  nth_error rs i = Some a -> nth_error rs j = Some b -> nth_error rs k = Some c ->
  SourceProgramRuns (ctx,rs) (ctx++[true],pair_head_store i j k a b c rs).
Proof.
  intros Layout P I J K IJ IK JK L A B C.
  destruct (source_pair_head_nonempty _ _ _ _ _ _ _ _ _ _ _ Layout P I J K IJ IK JK L A B C)
    as [mid [Step Run]]. eapply source_program_next; eassumption.
Qed.

Lemma source_pair_inner_return ctx :
  loop_return (ctx++[true;true;false;true]) = ctx++[true;true;true].
Proof.
  unfold loop_return.
  pose proof (proj1 (constructor_child_return (ctx++[true;true]) 1)) as E.
  change (break_pc 0 (rev ((ctx++[true;true])++[false]++[true])++[false]) =
    Some(true::rev (ctx++[true;true])++[false],1)) in E.
  replace ((ctx++[true;true])++[false]++[true]) with (ctx++[true;true;false;true]) in E
    by (repeat rewrite <- app_assoc; reflexivity).
  rewrite E, constructor_return_word, <- app_assoc. reflexivity.
Qed.

Definition pair_tail_store i j k h c rs :=
  let after_dec := set_register j h rs ++ [0] in
  let after_inc := set_register k (S c) after_dec in
  set_register i h (set_register j 0 after_inc) ++ repeat 0 h.

Theorem source_pair_positive_tail ctx root i j k first second rs h c :
  pair_layout root i j k first second -> SourcePrefix source_graph source_root ctx root ->
  i < 11 -> j < 11 -> k < 11 -> i<>j -> i<>k -> j<>k -> 11 <= length rs ->
  nth_error rs i = Some 0 -> nth_error rs j = Some (S h) -> nth_error rs k = Some c ->
  SourceProgramRuns (ctx++[true],rs) (ctx,pair_tail_store i j k h c rs).
Proof.
  intros Layout P I J K IJ IK JK L A B C.
  destruct Layout as [Tree FPrefix FTree SPrefix STree].
  set (after_dec := set_register j h rs ++ [0]).
  set (after_inc := set_register k (S c) after_dec).
  assert (L1 : 11 <= length after_dec).
  { unfold after_dec. rewrite app_length,set_register_length. simpl. lia. }
  assert (L2 : 11 <= length after_inc) by (unfold after_inc; rewrite set_register_length; exact L1).
  assert (C1 : nth_error after_dec k = Some c).
  { unfold after_dec. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact C. }
  assert (A1 : nth_error after_dec i = Some 0).
  { unfold after_dec. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact A. }
  assert (B1 : nth_error after_dec j = Some h).
  { unfold after_dec. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    apply nth_error_set_same. lia. }
  assert (A2 : nth_error after_inc i = Some 0).
  { unfold after_inc. rewrite nth_error_set_other by lia. exact A1. }
  assert (B2 : nth_error after_inc j = Some h).
  { unfold after_inc. rewrite nth_error_set_other by lia. exact B1. }
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P SPrefix) as Prefix.
  destruct (while1_transfer_nonempty (ctx++[true;true;false;true]) second after_inc j i h 0
     Prefix STree J I ltac:(lia) L2 B2 A2) as [mid [First Rest]].
  cbn [Nat.add_0_l] in Rest. rewrite source_pair_inner_return in Rest.
  unfold pair_tail_store. fold after_dec after_inc.
  eapply source_program_next; [apply source_pair_test_positive with (root:=root) (i:=i) (k:=k); eassumption|].
  eapply source_program_next; [apply source_pair_increment with (root:=root) (i:=i) (j:=j); eassumption|].
  eapply source_program_next; [exact First|].
  eapply source_program_runs_trans; [exact Rest|].
  eapply source_program_next; [apply source_pair_continue with (root:=root) (i:=i) (j:=j) (k:=k); eassumption|constructor].
Qed.

Print Assumptions source_pair_head.
Print Assumptions source_pair_head_nonempty.
Print Assumptions source_pair_positive_tail.
