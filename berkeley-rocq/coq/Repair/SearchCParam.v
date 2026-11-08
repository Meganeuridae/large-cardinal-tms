(** Total source-level contract for both concrete cparam routines. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerRegisters ConstructorArithmetic CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerExecution SearchCParamControl SearchCParamNoPop SearchCParamOne SourceExecution.
Import ListNotations.

Definition cparam_stack_after code s := if Nat.eqb code 1 then snd (uncantor s) else s.
Definition cparam_value_after code s old := if Nat.eqb code 1 then fst (uncantor s) else old.

Theorem source_cparam_nonempty ctx root p clear copy rs code s old :
  cparam_layout root p clear copy -> SourcePrefix source_graph source_root ctx root ->
  p<11 -> p<>3 -> p<>4 -> p<>8 -> p<>9 -> 11<=length rs ->
  nth_error rs 4=Some code -> nth_error rs 3=Some s -> nth_error rs p=Some old ->
  nth_error rs 8=Some 0 -> nth_error rs 9=Some 0 ->
  exists result mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (loop_return ctx,result) /\ 11<=length result /\
    nth_error result 4=Some code /\ nth_error result 3=Some(cparam_stack_after code s) /\
    nth_error result p=Some(cparam_value_after code s old) /\
    nth_error result 8=Some 0 /\ nth_error result 9=Some 0 /\
    outside_cparam p rs result /\
    exists pad, skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  intros Layout Prefix Hp H3 H4 H8 H9 L Code Stack Param X Y.
  destruct code as [|[|n]].
  - destruct (source_cparam_zero_nonempty ctx root p clear copy rs Layout Prefix Code) as [mid [First Run]].
    exists rs,mid. cbn [cparam_stack_after cparam_value_after Nat.eqb]. repeat split; try assumption.
    exists 0. cbn [repeat]. now rewrite app_nil_r.
  - destruct (uncantor s) as [a rest] eqn:U.
    pose proof (cantor_uncantor s) as E. rewrite U in E. cbn in E. subst s.
    destruct (source_cparam_one_nonempty ctx root p clear copy rs a rest old
      Layout Prefix Hp H3 H4 H8 H9 L Code Stack Param X Y) as [result [mid H]].
    exists result,mid. unfold cparam_stack_after,cparam_value_after. cbn [Nat.eqb].
    rewrite U. exact H.
  - destruct (source_cparam_ge2_nonempty ctx root p clear copy rs n Layout Prefix L Code)
      as [result [mid [First [Run [Len [C [Frame [pad Pad]]]]]]]].
    assert (S' : nth_error result 3=Some s) by (rewrite (Frame 3) by lia; exact Stack).
    assert (P' : nth_error result p=Some old) by (rewrite (Frame p) by lia; exact Param).
    assert (X' : nth_error result 8=Some 0) by (rewrite (Frame 8) by lia; exact X).
    assert (Y' : nth_error result 9=Some 0) by (rewrite (Frame 9) by lia; exact Y).
    assert (F' : outside_cparam p rs result).
    { unfold outside_cparam. intros i I Ip I3 I8 I9.
      destruct (Nat.eq_dec i 4) as [->|D].
      - rewrite C. symmetry. exact Code.
      - now apply Frame. }
    exists result,mid. unfold cparam_stack_after,cparam_value_after. cbn [Nat.eqb].
    repeat split; try assumption. now exists pad.
Qed.
Print Assumptions source_cparam_nonempty.
