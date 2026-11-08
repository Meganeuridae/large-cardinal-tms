(** Four actual main-program field decodings from one numeric proof word. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import ConstructorArithmetic.
From Repair Require Import CompilerExecution CompilerLoopBase SearchPrimitivesDecode SourceExecution.
Import ListNotations.

Definition decode_full_frame (before after : list nat) :=
  forall r, r<11 -> r<>0 -> r<>4 -> r<>5 -> r<>6 -> r<>7 -> r<>8 -> r<>9 ->
    nth_error after r = nth_error before r.

Theorem source_decode_quadruple_nonempty op a b c tail rs :
  11<=length rs ->
  nth_error rs 0 = Some (cantor op (cantor a (cantor b (cantor c tail)))) ->
  nth_error rs 4 = Some 0 -> nth_error rs 5 = Some 0 ->
  nth_error rs 6 = Some 0 -> nth_error rs 7 = Some 0 ->
  nth_error rs 8 = Some 0 -> nth_error rs 9 = Some 0 ->
  exists result mid, SourceProgramStep (decode_cursor 0,rs) mid /\
    SourceProgramRuns mid (decode_cursor 4,result) /\ 11<=length result /\
    nth_error result 0=Some tail /\ nth_error result 4=Some op /\
    nth_error result 5=Some a /\ nth_error result 6=Some b /\
    nth_error result 7=Some c /\ nth_error result 8=Some 0 /\
    nth_error result 9=Some 0 /\ decode_full_frame rs result.
Proof.
  intros L N A B C D X Y.
  destruct (source_decode_field_nonempty 0 op (cantor a (cantor b (cantor c tail))) 0 rs
    ltac:(lia) L N X Y A) as [r1 [m1 [S1 [R1 [L1 [N1 [X1 [Y1 [A1 F1]]]]]]]]].
  change (nth_error r1 4 = Some op) in A1. unfold decode_frame, decode_target in F1. cbn in F1.
  assert (B1 : nth_error r1 5=Some 0) by (rewrite F1 by lia; exact B).
  assert (C1 : nth_error r1 6=Some 0) by (rewrite F1 by lia; exact C).
  assert (D1 : nth_error r1 7=Some 0) by (rewrite F1 by lia; exact D).
  destruct (source_decode_field_nonempty 1 a (cantor b (cantor c tail)) 0 r1
    ltac:(lia) L1 N1 X1 Y1 B1) as [r2 [m2 [S2 [R2 [L2 [N2 [X2 [Y2 [B2 F2]]]]]]]]].
  change (nth_error r2 5 = Some a) in B2. unfold decode_frame, decode_target in F2. cbn in F2.
  assert (A2 : nth_error r2 4=Some op) by (rewrite F2 by lia; exact A1).
  assert (C2 : nth_error r2 6=Some 0) by (rewrite F2 by lia; exact C1).
  assert (D2 : nth_error r2 7=Some 0) by (rewrite F2 by lia; exact D1).
  destruct (source_decode_field_nonempty 2 b (cantor c tail) 0 r2
    ltac:(lia) L2 N2 X2 Y2 C2) as [r3 [m3 [S3 [R3 [L3 [N3 [X3 [Y3 [C3 F3]]]]]]]]].
  change (nth_error r3 6 = Some b) in C3. unfold decode_frame, decode_target in F3. cbn in F3.
  assert (A3 : nth_error r3 4=Some op) by (rewrite F3 by lia; exact A2).
  assert (B3 : nth_error r3 5=Some a) by (rewrite F3 by lia; exact B2).
  assert (D3 : nth_error r3 7=Some 0) by (rewrite F3 by lia; exact D2).
  destruct (source_decode_field_nonempty 3 c tail 0 r3
    ltac:(lia) L3 N3 X3 Y3 D3) as [result [m4 [S4 [R4 [L4 [N4 [X4 [Y4 [D4 F4]]]]]]]]].
  change (nth_error result 7 = Some c) in D4. unfold decode_frame, decode_target in F4. cbn in F4.
  assert (A4 : nth_error result 4=Some op) by (rewrite F4 by lia; exact A3).
  assert (B4 : nth_error result 5=Some a) by (rewrite F4 by lia; exact B3).
  assert (C4 : nth_error result 6=Some b) by (rewrite F4 by lia; exact C3).
  exists result,m1. repeat split; try assumption.
  - eapply source_program_runs_trans; [exact R1|]. eapply source_program_next; [exact S2|].
    eapply source_program_runs_trans; [exact R2|]. eapply source_program_next; [exact S3|].
    eapply source_program_runs_trans; [exact R3|]. eapply source_program_next; eassumption.
  - unfold decode_full_frame. intros r H H0 H4 H5 H6 H7 H8 H9.
    rewrite F4, F3, F2, F1 by lia. reflexivity.
Qed.

Print Assumptions source_decode_quadruple_nonempty.
