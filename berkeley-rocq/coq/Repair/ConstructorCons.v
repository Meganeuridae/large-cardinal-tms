(** Concrete source execution of ZF2.cons: unpair the stack, restore its
    remainder, pair the old stack top with the formula top, and restore it. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerRegisters ConstructorArithmetic CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerContexts CompilerExecution CompilerLoopBase CompilerLoops ConstructorData ConstructorGraph ConstructorPaths ConstructorControl ConstructorUnpair ConstructorUnpairFull ConstructorPairControl ConstructorPairFull ConstructorPush ConstructorFrame SourceExecution.
Import ListNotations.

Local Transparent unfold_small constructor_nodes.
Lemma cons_transfer_prefix : SourcePrefix source_graph 41 [true;false] 30.
Proof. apply source_prefix_find_sound. vm_compute. reflexivity. Qed.
Lemma cons_final_prefix : SourcePrefix source_graph 41 [true;true;true] 40.
Proof. apply source_prefix_find_sound. vm_compute. reflexivity. Qed.
Lemma cons_transfer_tree : unfold_root 30 = Some (tree_while1 9 3).
Proof. apply unfold_small_root_sound. vm_compute. reflexivity. Qed.
Lemma cons_final_tree : unfold_root 40 = Some (tree_while1 9 2).
Proof. apply unfold_small_root_sound. vm_compute. reflexivity. Qed.
Lemma cons_loop_return_three ctx : loop_return (ctx++[true;true;true]) = loop_return ctx.
Proof.
  replace (ctx++[true;true;true]) with (((ctx++[true])++[true])++[true])
    by (repeat rewrite <- app_assoc; reflexivity).
  now rewrite !constructor_loop_return_true.
Qed.

Definition outside_cons (before after : list nat) := forall i, i<11 ->
  i<>2 -> i<>3 -> i<>8 -> i<>9 -> nth_error after i = nth_error before i.

Theorem source_cons_nonempty ctx rs t a rest :
  SourcePrefix source_graph source_root ctx source_cons_root -> 11<=length rs ->
  nth_error rs 2=Some t -> nth_error rs 3=Some (cantor a rest) ->
  nth_error rs 8=Some 0 -> nth_error rs 9=Some 0 ->
  exists result mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (loop_return ctx,result) /\
    11<=length result /\ nth_error result 2=Some (cantor a t) /\
    nth_error result 3=Some rest /\ nth_error result 8=Some 0 /\
    nth_error result 9=Some 0 /\ outside_cons rs result /\
    exists pad, skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  intros P L Top Stack X Y.
  change (SourcePrefix source_graph source_root ctx 41) in P.
  destruct constructor_internal_prefixes as [_ [UnpairPrefix [PairPrefix _]]].
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P UnpairPrefix) as Punpair.
  destruct (source_unpair_cantor (ctx++[false]) rs a rest Punpair L Stack X Y)
    as [r1 [UnpairRun [L1 [S1 [X1 [Y1 F1]]]]]].
  rewrite constructor_loop_return_false in UnpairRun.
  assert (Diff : (ctx++[false],rs) <> (ctx++[true],r1)).
  { intro E. apply (f_equal (@fst _ _)) in E. cbn [fst] in E.
    apply app_inv_head in E. discriminate. }
  destruct (source_runs_nonempty_when_distinct _ _ UnpairRun Diff) as [mid [First UnpairTail]].
  assert (T1 : nth_error r1 2=Some t).
  { rewrite (F1 2) by lia. exact Top. }
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P cons_transfer_prefix) as Ptransfer.
  destruct (while1_transfer_nonempty (ctx++[true;false]) 30 r1 9 3 rest 0
    Ptransfer cons_transfer_tree ltac:(lia) ltac:(lia) ltac:(lia) L1 Y1 S1)
    as [mid2 [TransferFirst TransferRun]].
  replace (ctx++[true;false]) with ((ctx++[true])++[false]) in TransferRun by now rewrite <- app_assoc.
  rewrite constructor_loop_return_false in TransferRun.
  rewrite <- app_assoc in TransferRun. cbn [app] in TransferRun.
  set (r2 := set_register 3 rest (set_register 9 0 r1) ++ repeat 0 rest).
  change (SourceProgramRuns mid2 (ctx++[true;true],r2)) in TransferRun.
  assert (L2 : 11<=length r2).
  { unfold r2. rewrite length_app,repeat_length,!set_register_length. lia. }
  assert (T2 : nth_error r2 2=Some t).
  { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact T1. }
  assert (S2 : nth_error r2 3=Some rest).
  { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    apply nth_error_set_same. rewrite set_register_length. lia. }
  assert (X2 : nth_error r2 8=Some a).
  { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact X1. }
  assert (Y2 : nth_error r2 9=Some 0).
  { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite nth_error_set_other by lia. apply nth_error_set_same. lia. }
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P PairPrefix) as Ppair.
  destruct (source_pair_cantor_nonempty (ctx++[true;true;false]) 39 8 2 9 33 35 a t 0 r2
    pair_layout_cons Ppair ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) ltac:(lia) L2 X2 T2 Y2)
    as [r3 [mid3 [PairFirst [PairRun [L3 [X3 [T3 [Y3 F3]]]]]]]].
  replace (ctx++[true;true;false]) with ((ctx++[true;true])++[false]) in PairRun by now rewrite <- app_assoc.
  rewrite constructor_loop_return_false in PairRun.
  rewrite <- app_assoc in PairRun. cbn [app] in PairRun.
  assert (S3 : nth_error r3 3=Some rest).
  { rewrite (F3 3) by lia. exact S2. }
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P cons_final_prefix) as Pfinal.
  pose proof (while1_transfer (ctx++[true;true;true]) 40 r3 9 2 (cantor a t) 0
    Pfinal cons_final_tree ltac:(lia) ltac:(lia) ltac:(lia) L3 Y3 T3) as FinalRun.
  cbn [Nat.add_0_l] in FinalRun. rewrite cons_loop_return_three in FinalRun.
  set (result := set_register 2 (cantor a t) (set_register 9 0 r3) ++ repeat 0 (cantor a t)).
  change (SourceProgramRuns (ctx++[true;true;true],r3) (loop_return ctx,result)) in FinalRun.
  assert (AllTail : SourceProgramRuns mid (loop_return ctx,result)).
  { eapply source_program_runs_trans; [exact UnpairTail|].
    eapply source_program_next with (t:=mid2).
    - eapply constructor_unpad_first_step with (pad:=1).
      change (SourceProgramStep ((ctx++[true])++[false],r1) mid2).
      rewrite <- app_assoc. exact TransferFirst.
    - eapply source_program_runs_trans; [exact TransferRun|].
      eapply source_program_next with (t:=mid3).
      + eapply constructor_unpad_first_step with (pad:=1).
        change (SourceProgramStep ((ctx++[true;true])++[false],r2) mid3).
        rewrite <- app_assoc. exact PairFirst.
      + eapply source_program_runs_trans; eassumption. }
  assert (AllRun : SourceProgramRuns (ctx,rs) (loop_return ctx,result)).
  { eapply source_program_next; [eapply constructor_unpad_first_step with (pad:=1); exact First|exact AllTail]. }
  destruct (source_runs_zero_suffix _ _ AllRun L) as [pad [Pad _]].
  exists result,mid. repeat split.
  - eapply constructor_unpad_first_step with (pad:=1). exact First.
  - exact AllTail.
  - unfold result. rewrite length_app,repeat_length,!set_register_length. lia.
  - unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    apply nth_error_set_same. rewrite set_register_length. lia.
  - unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact S3.
  - unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact X3.
  - unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite nth_error_set_other by lia. apply nth_error_set_same. lia.
  - unfold outside_cons. intros i I I2 I3 I8 I9.
    unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia.
    rewrite (F3 i) by lia.
    unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. apply F1; lia.
  - exists pad. exact Pad.
Qed.

Theorem source_cons_total_nonempty ctx rs t s :
  SourcePrefix source_graph source_root ctx source_cons_root -> 11<=length rs ->
  nth_error rs 2=Some t -> nth_error rs 3=Some s ->
  nth_error rs 8=Some 0 -> nth_error rs 9=Some 0 ->
  exists result mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (loop_return ctx,result) /\
    11<=length result /\
    (let '(a,rest) := uncantor s in
      nth_error result 2=Some (cantor a t) /\ nth_error result 3=Some rest) /\
    nth_error result 8=Some 0 /\ nth_error result 9=Some 0 /\ outside_cons rs result /\
    exists pad, skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  intros P L T S X Y. pose proof (cantor_uncantor s) as C.
  destruct (uncantor s) as [a rest] eqn:E. cbn in C. subst s.
  destruct (source_cons_nonempty ctx rs t a rest P L T S X Y) as [result [mid H]].
  exists result,mid. tauto.
Qed.
Print Assumptions source_cons_nonempty.
Print Assumptions source_cons_total_nonempty.
