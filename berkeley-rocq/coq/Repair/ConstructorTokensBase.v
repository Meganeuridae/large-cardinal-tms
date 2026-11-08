(** Source execution of the generated variable constructors. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import RuntimeControl CompilerSyntax CompilerRegisters ConstructorArithmetic CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerContexts CompilerExecution CompilerLoopBase ConstructorGraph ConstructorPaths ConstructorControl ConstructorUnpair ConstructorPush ConstructorFrame SourceExecution.
Import ListNotations.

Definition variable_root n := nth n [11;93;94;114;170;171;172;404;467;470;471] 11.
Local Transparent source_graph source_token_roots.
Lemma variable_root_children n : n<10 ->
  SourcePrefix source_graph (variable_root (S n)) [false] (variable_root n) /\
  SourceSelect source_graph (variable_root (S n)) [true] (SInc 2).
Proof.
  intro H. do 10 (destruct n as [|n]; [split;
    [apply source_prefix_find_sound; vm_compute; reflexivity|
     eapply select_leaf; [vm_compute; reflexivity|reflexivity|reflexivity]]|]). lia.
Qed.
Lemma variable_root_in n : n<=10 -> In (16+n,variable_root n) source_token_roots.
Proof. intro H. do 11 (destruct n as [|n]; [vm_compute; intuition congruence|]). lia. Qed.

Lemma variable_increment_step ctx rs n :
  SourceSelect source_graph source_root (ctx++[true]) (SInc 2) ->
  nth_error rs 2=Some n ->
  SourceProgramStep (ctx++[true],rs) (loop_return ctx,set_register 2 (S n) rs).
Proof.
  intros Sel V. destruct (loop_return_spec (ctx++[true])) as [out [k [E F]]].
  rewrite constructor_loop_return_true in F. rewrite F.
  eapply constructor_step_inc with (pad:=0) (i:=2) (value:=n) (count:=k).
  - now rewrite app_nil_r.
  - lia.
  - exact V.
  - now rewrite app_nil_r.
Qed.

Theorem source_variable_nonempty n ctx rs t s : n<=10 ->
  SourcePrefix source_graph source_root ctx (variable_root n) -> 11<=length rs ->
  nth_error rs 2=Some t -> nth_error rs 3=Some s -> nth_error rs 8=Some 0 ->
  exists result mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (loop_return ctx,result) /\
    11<=length result /\ nth_error result 2=Some n /\
    nth_error result 3=Some (cantor t s) /\ nth_error result 8=Some 0 /\
    outside_push rs result /\
    exists pad, skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  revert ctx rs t s. induction n as [|n IH]; intros ctx rs t s Hn P L T Stack X.
  - change (SourcePrefix source_graph source_root ctx source_pushwff_root) in P.
    destruct (source_push_nonempty ctx rs t s P L T Stack X)
      as [result [mid [F [R [Len [Top [Stack1 [Scratch Frame]]]]]]]].
    assert (AllRun : SourceProgramRuns (ctx,rs) (loop_return ctx,result)).
    { eapply source_program_next; eassumption. }
    destruct (source_runs_zero_suffix _ _ AllRun L) as [pad [Pad _]].
    exists result,mid. repeat split; try assumption. exists pad. exact Pad.
  - destruct (variable_root_children n ltac:(lia)) as [Child Inc].
    pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P Child) as Pchild.
    destruct (IH (ctx++[false]) rs t s ltac:(lia) Pchild L T Stack X)
      as [r1 [mid [First [Run [L1 [T1 [S1 [X1 [Frame [pad Pad]]]]]]]]]].
    rewrite constructor_loop_return_false in Run.
    assert (Sel : SourceSelect source_graph source_root (ctx++[true]) (SInc 2)).
    { eapply source_select_in_context; eassumption. }
    pose proof (variable_increment_step ctx r1 n Sel T1) as Next.
    set (result := set_register 2 (S n) r1).
    change (SourceProgramStep (ctx++[true],r1) (loop_return ctx,result)) in Next.
    assert (AllTail : SourceProgramRuns mid (loop_return ctx,result)).
    { eapply source_program_runs_trans; [exact Run|].
      eapply source_program_next; [exact Next|constructor]. }
    assert (AllRun : SourceProgramRuns (ctx,rs) (loop_return ctx,result)).
    { eapply source_program_next; [eapply constructor_unpad_first_step with (pad:=1); exact First|exact AllTail]. }
    destruct (source_runs_zero_suffix _ _ AllRun L) as [pad' [Pad' _]].
    exists result,mid. repeat split.
    + eapply constructor_unpad_first_step with (pad:=1). exact First.
    + exact AllTail.
    + unfold result. rewrite set_register_length. exact L1.
    + unfold result. apply nth_error_set_same. lia.
    + unfold result. rewrite nth_error_set_other by lia. exact S1.
    + unfold result. rewrite nth_error_set_other by lia. exact X1.
    + unfold outside_push. intros i I I2 I3 I8. unfold result.
      rewrite nth_error_set_other by lia. apply Frame; assumption.
    + exists pad'. exact Pad'.
Qed.
Print Assumptions variable_root_children.
Print Assumptions source_variable_nonempty.
