(** Execution of the composite equality, membership, implication, quantifier,
    and negation constructor subtrees in the extracted source DAG. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerRegisters ConstructorArithmetic CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerContexts CompilerExecution CompilerLoopBase ConstructorGraph ConstructorPaths ConstructorControl ConstructorUnpair ConstructorPush ConstructorFrame ConstructorParam ConstructorCons ConstructorTokensV SourceExecution.
Import ListNotations.

Record binary_layout root tag : Prop := {
  binary_first_cons : SourcePrefix source_graph root [false] source_cons_root;
  binary_middle_v : SourcePrefix source_graph root [true;false] (v_root tag);
  binary_final_cons : SourcePrefix source_graph root [true;true] source_cons_root
}.
Local Transparent source_graph.
Lemma binary_layout_eq : binary_layout 71 0.
Proof. constructor; apply source_prefix_find_sound; vm_compute; reflexivity. Qed.
Lemma binary_layout_mem : binary_layout 88 1.
Proof. constructor; apply source_prefix_find_sound; vm_compute; reflexivity. Qed.
Lemma binary_layout_imp : binary_layout 44 2.
Proof. constructor; apply source_prefix_find_sound; vm_compute; reflexivity. Qed.
Lemma binary_layout_all : binary_layout 61 4.
Proof. constructor; apply source_prefix_find_sound; vm_compute; reflexivity. Qed.
Lemma neg_first_v : SourcePrefix source_graph 57 [false] (v_root 3).
Proof. apply source_prefix_find_sound. vm_compute. reflexivity. Qed.
Lemma neg_final_cons : SourcePrefix source_graph 57 [true] source_cons_root.
Proof. apply source_prefix_find_sound. vm_compute. reflexivity. Qed.

Lemma outside_cons_trans a b c : outside_cons a b -> outside_cons b c -> outside_cons a c.
Proof. unfold outside_cons. intros A B i H I J K M. now rewrite B,A by assumption. Qed.
Lemma outside_push_is_cons a b : outside_push a b -> outside_cons a b.
Proof. unfold outside_push,outside_cons. intros H i I A B C D. now apply H. Qed.

Theorem source_binary_nonempty ctx root tag rs t a rest :
  binary_layout root tag -> tag<=4 -> SourcePrefix source_graph source_root ctx root ->
  11<=length rs -> nth_error rs 2=Some t -> nth_error rs 3=Some (cantor a rest) ->
  nth_error rs 8=Some 0 -> nth_error rs 9=Some 0 ->
  exists result mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (loop_return ctx,result) /\
    11<=length result /\ nth_error result 2=Some (cantor (cantor a t) tag) /\
    nth_error result 3=Some rest /\ nth_error result 8=Some 0 /\
    nth_error result 9=Some 0 /\ outside_cons rs result /\
    exists pad, skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  intros [C1 VP C2] Tag Prefix Len Top Stack X Y.
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ Prefix C1) as P1.
  destruct (source_cons_nonempty (ctx++[false]) rs t a rest P1 Len Top Stack X Y)
    as [r1 [mid [First [Run1 [L1 [T1 [S1 [X1 [Y1 [F1 [p1 Tail1]]]]]]]]]]].
  rewrite constructor_loop_return_false in Run1.
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ Prefix VP) as P2.
  destruct (source_v_nonempty tag (ctx++[true;false]) r1 (cantor a t) rest
    Tag P2 L1 T1 S1 X1) as [r2 [mid2 [First2 [Run2 [L2 [T2 [S2 [X2 [F2 [p2 Tail2]]]]]]]]]].
  replace (ctx++[true;false]) with ((ctx++[true])++[false]) in Run2 by now rewrite <- app_assoc.
  rewrite constructor_loop_return_false in Run2. rewrite <- app_assoc in Run2. cbn [app] in Run2.
  assert (Y2 : nth_error r2 9=Some 0) by (rewrite (F2 9) by lia; exact Y1).
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ Prefix C2) as P3.
  destruct (source_cons_nonempty (ctx++[true;true]) r2 tag (cantor a t) rest
    P3 L2 T2 S2 X2 Y2) as [result [mid3 [First3 [Run3 [L3 [T3 [S3 [X3 [Y3 [F3 [p3 Tail3]]]]]]]]]]].
  rewrite loop_return_two_true in Run3.
  assert (AllTail : SourceProgramRuns mid (loop_return ctx,result)).
  { eapply source_program_runs_trans; [exact Run1|].
    eapply source_program_next with (t:=mid2).
    - eapply constructor_unpad_first_step with (pad:=1).
      change (SourceProgramStep ((ctx++[true])++[false],r1) mid2).
      rewrite <- app_assoc. exact First2.
    - eapply source_program_runs_trans; [exact Run2|].
      eapply source_program_next with (t:=mid3); eassumption. }
  assert (AllRun : SourceProgramRuns (ctx,rs) (loop_return ctx,result)).
  { eapply source_program_next; [eapply constructor_unpad_first_step with (pad:=1); exact First|exact AllTail]. }
  destruct (source_runs_zero_suffix _ _ AllRun Len) as [pad [Pad _]].
  exists result,mid. repeat split; try assumption.
  - eapply constructor_unpad_first_step with (pad:=1). exact First.
  - eapply outside_cons_trans; [exact F1|].
    eapply outside_cons_trans; [apply outside_push_is_cons; exact F2|exact F3].
  - exists pad. exact Pad.
Qed.

Theorem source_negation_nonempty ctx rs t s :
  SourcePrefix source_graph source_root ctx 57 -> 11<=length rs ->
  nth_error rs 2=Some t -> nth_error rs 3=Some s ->
  nth_error rs 8=Some 0 -> nth_error rs 9=Some 0 ->
  exists result mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (loop_return ctx,result) /\
    11<=length result /\ nth_error result 2=Some (cantor t 3) /\
    nth_error result 3=Some s /\ nth_error result 8=Some 0 /\
    nth_error result 9=Some 0 /\ outside_cons rs result /\
    exists pad, skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  intros Prefix Len Top Stack X Y.
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ Prefix neg_first_v) as P1.
  destruct (source_v_nonempty 3 (ctx++[false]) rs t s ltac:(lia) P1 Len Top Stack X)
    as [r1 [mid [First [Run1 [L1 [T1 [S1 [X1 [F1 [p1 Tail1]]]]]]]]]].
  rewrite constructor_loop_return_false in Run1.
  assert (Y1 : nth_error r1 9=Some 0) by (rewrite (F1 9) by lia; exact Y).
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ Prefix neg_final_cons) as P2.
  destruct (source_cons_nonempty (ctx++[true]) r1 3 t s P2 L1 T1 S1 X1 Y1)
    as [result [mid2 [First2 [Run2 [L2 [T2 [S2 [X2 [Y2 [F2 [p2 Tail2]]]]]]]]]]].
  rewrite constructor_loop_return_true in Run2.
  assert (AllTail : SourceProgramRuns mid (loop_return ctx,result)).
  { eapply source_program_runs_trans; [exact Run1|].
    eapply source_program_next with (t:=mid2); eassumption. }
  assert (AllRun : SourceProgramRuns (ctx,rs) (loop_return ctx,result)).
  { eapply source_program_next; [eapply constructor_unpad_first_step with (pad:=1); exact First|exact AllTail]. }
  destruct (source_runs_zero_suffix _ _ AllRun Len) as [pad [Pad _]].
  exists result,mid. repeat split; try assumption.
  - eapply constructor_unpad_first_step with (pad:=1). exact First.
  - eapply outside_cons_trans; [apply outside_push_is_cons; exact F1|exact F2].
  - exists pad. exact Pad.
Qed.
Print Assumptions source_binary_nonempty.
Print Assumptions source_negation_nonempty.
