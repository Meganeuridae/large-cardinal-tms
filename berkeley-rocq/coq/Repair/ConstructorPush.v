(** Source-level execution of ZF2.pushwff, using the proved pair loop. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import RuntimeControl CompilerSyntax CompilerRegisters ConstructorArithmetic CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerContexts CompilerExecution CompilerLoopBase CompilerLoops ConstructorData ConstructorGraph ConstructorPaths ConstructorControl ConstructorUnpair ConstructorPairControl ConstructorPairFull SourceExecution.
Import ListNotations.

Local Transparent unfold_small constructor_nodes.
Lemma source_push_transfer_tree : unfold_root 10 = Some (tree_while1 8 3).
Proof. apply unfold_small_root_sound. vm_compute. reflexivity. Qed.

Lemma source_push_transfer_prefix : SourcePrefix source_graph 11 [true] 10.
Proof. apply source_prefix_find_sound. vm_compute. reflexivity. Qed.

Lemma constructor_loop_return_true ctx : loop_return (ctx++[true]) = loop_return ctx.
Proof.
  destruct (loop_return_spec ctx) as [out [n [E F]]]. rewrite F.
  unfold loop_return. rewrite rev_app_distr. cbn [rev app break_pc].
  rewrite E. reflexivity.
Qed.

Definition outside_push (before after : list nat) :=
  forall r, r < 11 -> r<>2 -> r<>3 -> r<>8 -> nth_error after r = nth_error before r.

Theorem source_push_nonempty ctx rs t s :
  SourcePrefix source_graph source_root ctx source_pushwff_root -> 11 <= length rs ->
  nth_error rs 2 = Some t -> nth_error rs 3 = Some s -> nth_error rs 8 = Some 0 ->
  exists result mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (loop_return ctx,result) /\
    11 <= length result /\ nth_error result 2 = Some 0 /\
    nth_error result 3 = Some (cantor t s) /\ nth_error result 8 = Some 0 /\
    outside_push rs result.
Proof.
  intros Prefix L Top Stack Scratch.
  destruct constructor_internal_prefixes as [PairPrefix _].
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ Prefix PairPrefix) as P.
  destruct (source_pair_cantor_nonempty (ctx++[false]) 8 2 3 8 2 4 t s 0 rs
    pair_layout_push P ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) ltac:(lia) L Top Stack Scratch)
    as [paired [mid [First [PairRun [PL [PT [PS [PX Frame]]]]]]]].
  cbn [Nat.add_0_l] in PX. rewrite constructor_loop_return_false in PairRun.
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ Prefix source_push_transfer_prefix) as Q.
  destruct (while1_transfer_nonempty (ctx++[true]) 10 paired 8 3 (cantor t s) 0
    Q source_push_transfer_tree ltac:(lia) ltac:(lia) ltac:(lia) PL PX PS)
    as [mid2 [MoveFirst MoveRun]].
  cbn [Nat.add_0_l] in MoveRun. rewrite constructor_loop_return_true in MoveRun.
  set (result := set_register 3 (cantor t s) (set_register 8 0 paired) ++ repeat 0 (cantor t s)).
  fold result in MoveRun.
  exists result,mid. repeat split.
  - eapply constructor_unpad_first_step with (pad:=1). exact First.
  - eapply source_program_runs_trans; [exact PairRun|].
    eapply source_program_next; eassumption.
  - unfold result. rewrite app_length, repeat_length, !set_register_length. lia.
  - unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact PT.
  - unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    apply nth_error_set_same. rewrite set_register_length. lia.
  - unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite nth_error_set_other by lia. apply nth_error_set_same. lia.
  - unfold outside_push, result. intros r R A B C.
    rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. apply Frame; assumption.
Qed.

Theorem source_push ctx rs t s :
  SourcePrefix source_graph source_root ctx source_pushwff_root -> 11 <= length rs ->
  nth_error rs 2 = Some t -> nth_error rs 3 = Some s -> nth_error rs 8 = Some 0 ->
  exists result, SourceProgramRuns (ctx,rs) (loop_return ctx,result) /\
    11 <= length result /\ nth_error result 2 = Some 0 /\
    nth_error result 3 = Some (cantor t s) /\ nth_error result 8 = Some 0 /\
    outside_push rs result.
Proof.
  intros P L T S X.
  destruct (source_push_nonempty ctx rs t s P L T S X) as [result [mid [Step [Run Facts]]]].
  exists result. split; [eapply source_program_next; eassumption|exact Facts].
Qed.

Print Assumptions source_push_nonempty.
Print Assumptions source_push.
