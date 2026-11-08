(** Actual source prefix of one proof-search iteration through quadruple decode. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import CompilerRegisters ConstructorArithmetic.
From Repair Require Import CompilerExecution CompilerLoopBase ConstructorControl ConstructorUnpair SearchPrimitivesSetup SearchPrimitivesClear SearchPrimitivesDecode SearchPrimitivesDecodeFull SourceExecution.
Import ListNotations.

Definition iteration_word pending next := match pending with 0 => next | S p => p end.
Definition iteration_next pending next := match pending with 0 => S next | S _ => next end.

Theorem source_setup_main_nonempty pending next rs :
  11<=length rs -> nth_error rs 0=Some pending -> nth_error rs 1=Some next -> nth_error rs 8=Some 0 ->
  exists result mid, SourceProgramStep ([],rs) mid /\ SourceProgramRuns mid ([true],result) /\
    11<=length result /\ nth_error result 0=Some(iteration_word pending next) /\
    nth_error result 1=Some(iteration_next pending next) /\ nth_error result 8=Some 0 /\ setup_frame rs result.
Proof.
  intros L N Q X. destruct source_setup_loop_prefixes as [_ [_ P]].
  assert (Return : loop_return [false]=[true]).
  { change (loop_return ([]++[false])=[]++[true]). apply constructor_loop_return_false. }
  destruct pending as [|n].
  - destruct (source_setup_fresh_nonempty [false] rs next P L N Q X)
      as [result [mid [Step [Run [Len [A [B [C F]]]]]]]].
    rewrite Return in Run. cbn [iteration_word iteration_next].
    exists result,mid. repeat split; try assumption.
    eapply constructor_unpad_first_step with (pad:=1). exact Step.
  - destruct (source_setup_pending_nonempty [false] rs n next P L N Q X)
      as [result [mid [Step [Run [Len [A [B [C F]]]]]]]].
    rewrite Return in Run. cbn [iteration_word iteration_next].
    exists result,mid. repeat split; try assumption.
    eapply constructor_unpad_first_step with (pad:=1). exact Step.
Qed.

Theorem source_iteration_prefix_nonempty pending next t s op a b c tail rs :
  11<=length rs -> nth_error rs 0=Some pending -> nth_error rs 1=Some next ->
  nth_error rs 2=Some t -> nth_error rs 3=Some s -> nth_error rs 8=Some 0 -> nth_error rs 9=Some 0 ->
  iteration_word pending next = cantor op (cantor a (cantor b (cantor c tail))) ->
  exists result mid, SourceProgramStep ([],rs) mid /\ SourceProgramRuns mid (decode_cursor 4,result) /\
    11<=length result /\ nth_error result 0=Some tail /\
    nth_error result 1=Some(iteration_next pending next) /\ nth_error result 2=Some t /\ nth_error result 3=Some s /\
    nth_error result 4=Some op /\ nth_error result 5=Some a /\ nth_error result 6=Some b /\
    nth_error result 7=Some c /\ nth_error result 8=Some 0 /\ nth_error result 9=Some 0 /\
    nth_error result 10=nth_error rs 10.
Proof.
  intros L N Q T S X Y Code.
  destruct (source_setup_main_nonempty pending next rs L N Q X)
    as [r1 [m1 [Step1 [Run1 [L1 [N1 [Q1 [X1 F1]]]]]]]].
  assert (T1 : nth_error r1 2=Some t) by (rewrite F1 by lia; exact T).
  assert (S1 : nth_error r1 3=Some s) by (rewrite F1 by lia; exact S).
  assert (Y1 : nth_error r1 9=Some 0) by (rewrite F1 by lia; exact Y).
  assert (Z1 : nth_error r1 10=nth_error rs 10) by (apply F1; lia).
  destruct (source_clear_all_nonempty r1 L1)
    as [r2 [m2 [Step2 [Run2 [L2 [A2 [B2 [C2 [D2 F2]]]]]]]]].
  change (SourceProgramStep ([true],r1) m2) in Step2.
  change (SourceProgramRuns m2 (decode_cursor 0,r2)) in Run2.
  assert (N2 : nth_error r2 0=Some(cantor op (cantor a (cantor b (cantor c tail)))))
    by (rewrite F2 by lia; rewrite <- Code; exact N1).
  assert (Q2 : nth_error r2 1=Some(iteration_next pending next)) by (rewrite F2 by lia; exact Q1).
  assert (T2 : nth_error r2 2=Some t) by (rewrite F2 by lia; exact T1).
  assert (S2 : nth_error r2 3=Some s) by (rewrite F2 by lia; exact S1).
  assert (X2 : nth_error r2 8=Some 0) by (rewrite F2 by lia; exact X1).
  assert (Y2 : nth_error r2 9=Some 0) by (rewrite F2 by lia; exact Y1).
  assert (Z2 : nth_error r2 10=nth_error rs 10) by (rewrite F2 by lia; exact Z1).
  destruct (source_decode_quadruple_nonempty op a b c tail r2 L2 N2 A2 B2 C2 D2 X2 Y2)
    as [result [m3 [Step3 [Run3 [L3 [N3 [A3 [B3 [C3 [D3 [X3 [Y3 F3]]]]]]]]]]]].
  assert (Q3 : nth_error result 1=Some(iteration_next pending next)) by (rewrite F3 by lia; exact Q2).
  assert (T3 : nth_error result 2=Some t) by (rewrite F3 by lia; exact T2).
  assert (S3 : nth_error result 3=Some s) by (rewrite F3 by lia; exact S2).
  assert (Z3 : nth_error result 10=nth_error rs 10) by (rewrite F3 by lia; exact Z2).
  exists result,m1. repeat split; try assumption.
  eapply source_program_runs_trans; [exact Run1|]. eapply source_program_next; [exact Step2|].
  eapply source_program_runs_trans; [exact Run2|]. eapply source_program_next; eassumption.
Qed.

Print Assumptions source_setup_main_nonempty.
Print Assumptions source_iteration_prefix_nonempty.
