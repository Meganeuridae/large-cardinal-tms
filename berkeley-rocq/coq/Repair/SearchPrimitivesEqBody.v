(** Complete source semantics of MP's if_eq, including the equal-case body. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerRegisters CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerExecution CompilerLoopBase CompilerLoops ConstructorPaths ConstructorControl ConstructorUnpair ConstructorPush SearchPrimitivesEqControl SearchPrimitivesEq SourceExecution.
Import ListNotations.

Definition eq_body_frame (before after : list nat) :=
  forall r, r<11 -> r<>2 -> r<>9 -> r<>10 -> nth_error after r=nth_error before r.

Theorem source_mp_if_eq_nonempty ctx a b t p rs :
  SourcePrefix source_graph source_root ctx 670 -> 11<=length rs ->
  nth_error rs 2=Some t -> nth_error rs 5=Some p -> nth_error rs 8=Some 0 ->
  nth_error rs 9=Some a -> nth_error rs 10=Some b ->
  exists result mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (loop_return ctx,result) /\ 11<=length result /\
    nth_error result 2=Some(if Nat.eqb a b then t+p else t) /\
    nth_error result 5=Some p /\ nth_error result 8=Some 0 /\
    nth_error result 9=Some 0 /\ nth_error result 10=Some 0 /\ eq_body_frame rs result.
Proof.
  intros P L Top Param Scratch A B.
  destruct (source_mp_eq_test_nonempty ctx a b rs P L A B)
    as [r1 [mid [First [Test [L1 [A1 [B1 F1]]]]]]].
  assert (T1 : nth_error r1 2=Some t) by (rewrite F1 by lia; exact Top).
  assert (P1 : nth_error r1 5=Some p) by (rewrite F1 by lia; exact Param).
  assert (X1 : nth_error r1 8=Some 0) by (rewrite F1 by lia; exact Scratch).
  unfold eq_test_exit in Test. destruct (Nat.eqb a b) eqn:E.
  - destruct source_mp_compare_prefixes as [_ [_ [Sub1 [Sub2 [Tree1 Tree2]]]]].
    pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P Sub1) as Prefix1.
    pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P Sub2) as Prefix2.
    destruct (while2_transfer_nonempty (ctx++[true;false]) 659 r1 5 8 2 p 0 t
      Prefix1 Tree1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
      L1 P1 X1 T1) as [mid1 [Step1 Run1]].
    cbn [Nat.add_0_l] in Run1.
    set (r2:=set_register 2 (t+p) (set_register 8 p (set_register 5 0 r1)) ++ repeat 0 p).
    fold r2 in Run1.
    assert (Ret1 : loop_return (ctx++[true;false])=ctx++[true;true]).
    { replace (ctx++[true;false]) with ((ctx++[true])++[false]) by (rewrite <- app_assoc; reflexivity).
      rewrite constructor_loop_return_false, <- app_assoc. reflexivity. }
    rewrite Ret1 in Run1.
    assert (L2 : 11<=length r2) by (unfold r2; rewrite app_length,repeat_length,!set_register_length; lia).
    assert (T2 : nth_error r2 2=Some(t+p)).
    { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      apply nth_error_set_same. rewrite !set_register_length. lia. }
    assert (P2 : nth_error r2 5=Some 0).
    { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      rewrite !nth_error_set_other by lia. apply nth_error_set_same. lia. }
    assert (X2 : nth_error r2 8=Some p).
    { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      rewrite nth_error_set_other by lia. apply nth_error_set_same. rewrite set_register_length. lia. }
    assert (A2 : nth_error r2 9=Some 0).
    { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      rewrite !nth_error_set_other by lia. exact A1. }
    assert (B2 : nth_error r2 10=Some 0).
    { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      rewrite !nth_error_set_other by lia. exact B1. }
    destruct (while1_transfer_nonempty (ctx++[true;true]) 16 r2 8 5 p 0
      Prefix2 Tree2 ltac:(lia) ltac:(lia) ltac:(lia) L2 X2 P2) as [mid2 [Step2 Run2]].
    cbn [Nat.add_0_l] in Run2.
    set (result:=set_register 5 p (set_register 8 0 r2) ++ repeat 0 p). fold result in Run2.
    assert (Ret2 : loop_return (ctx++[true;true])=loop_return ctx).
    { replace (ctx++[true;true]) with ((ctx++[true])++[true]) by (rewrite <- app_assoc; reflexivity).
      now rewrite !constructor_loop_return_true. }
    rewrite Ret2 in Run2. exists result,mid. repeat split; try assumption.
    + eapply source_program_runs_trans; [exact Test|]. eapply source_program_next with (t:=mid1).
      * eapply constructor_unpad_first_step with (pad:=1).
        change (SourceProgramStep ((ctx++[true])++[false],r1) mid1). rewrite <- app_assoc. exact Step1.
      * eapply source_program_runs_trans; [exact Run1|]. eapply source_program_next; eassumption.
    + unfold result. rewrite app_length,repeat_length,!set_register_length. lia.
    + unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      rewrite !nth_error_set_other by lia. exact T2.
    + unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      apply nth_error_set_same. rewrite set_register_length. lia.
    + unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      rewrite nth_error_set_other by lia. apply nth_error_set_same. lia.
    + unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      rewrite !nth_error_set_other by lia. exact A2.
    + unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      rewrite !nth_error_set_other by lia. exact B2.
    + unfold eq_body_frame. intros r R R2 R9 R10.
      destruct (Nat.eq_dec r 5) as [->|R5].
      * unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
        rewrite nth_error_set_same by (rewrite set_register_length; lia). symmetry. exact Param.
      * destruct (Nat.eq_dec r 8) as [->|R8].
        -- unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
           rewrite nth_error_set_other by lia. rewrite nth_error_set_same by lia. symmetry. exact Scratch.
        -- unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
           rewrite !nth_error_set_other by lia. unfold r2.
           rewrite nth_error_app1 by (rewrite !set_register_length; lia).
           rewrite !nth_error_set_other by lia. apply F1; assumption.
  - exists r1,mid. repeat split; try assumption.
    unfold eq_body_frame,eq_test_frame in *. intros. eapply F1; eassumption.
Qed.

Print Assumptions source_mp_if_eq_nonempty.
