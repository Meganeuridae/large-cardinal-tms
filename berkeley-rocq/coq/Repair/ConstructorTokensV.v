(** Source execution helpers for the inlined v_0..v_4 routines. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import RuntimeControl CompilerSyntax CompilerRegisters ConstructorArithmetic ConstructorPC CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerContexts CompilerExecution CompilerLoopBase CompilerLoops ConstructorData ConstructorGraph ConstructorPaths ConstructorControl ConstructorUnpair ConstructorPairControl ConstructorPairFull ConstructorPush ConstructorFrame SourceExecution.
Import ListNotations.

Definition v_root tag := nth tag [11;42;43;56;60] 11.
Definition v_transfer_bits tag := if Nat.eqb tag 0 then [true] else [true;false].
Local Transparent source_graph source_token_roots.
Lemma v_layout tag : tag<=4 ->
  SourcePrefix source_graph (v_root tag) [false] 8 /\
  SourcePrefix source_graph (v_root tag) (v_transfer_bits tag) 10.
Proof.
  intro H. do 5 (destruct tag as [|tag]; [split;
    apply source_prefix_find_sound; vm_compute; reflexivity|]). lia.
Qed.

Fixpoint source_find_leaf (program : list source_pair) root bits : option source_atom :=
  match bits with
  | [] => None
  | b::tail =>
      match nth_error program root with
      | None => None
      | Some p => match tail with
          | [] => let leaf := select_branch p b in if is_leaf leaf then Some leaf else None
          | _::_ => match select_branch p b with
              | SNode next => source_find_leaf program next tail
              | _ => None end
          end
      end
  end.
Lemma source_find_leaf_sound program root bits leaf :
  source_find_leaf program root bits = Some leaf -> SourceSelect program root bits leaf.
Proof.
  revert root. induction bits as [|bit bits IH]; intros root E; [discriminate|].
  cbn [source_find_leaf] in E. destruct (nth_error program root) as [p|] eqn:P; [|discriminate].
  destruct bits as [|b bits].
  - destruct (is_leaf (select_branch p bit)) eqn:K; [|discriminate].
    inversion E; subst leaf. eapply select_leaf; [exact P|reflexivity|exact K].
  - destruct (select_branch p bit) as [next| | | | |] eqn:B; try discriminate.
    eapply select_node; [exact P|exact B|]. now apply IH.
Qed.

Definition v_inc_bits tag k :=
  [true;true] ++ repeat true k ++ if Nat.eqb (S k) tag then [] else [false].
Lemma v_inc_selection tag k : 1<=tag -> tag<=4 -> k<tag ->
  SourceSelect source_graph (v_root tag) (v_inc_bits tag k) (SInc 2).
Proof.
  intros A B C. destruct tag as [|[|[|[|[|tag]]]]]; try lia;
    destruct k as [|[|[|[|k]]]]; try lia;
    apply source_find_leaf_sound; vm_compute; reflexivity.
Qed.

Lemma repeat_true_snoc n : repeat true (S n) = repeat true n ++ [true].
Proof. replace (S n) with (n+1) by lia. rewrite repeat_app. reflexivity. Qed.
Lemma loop_return_true_repeat ctx n : loop_return (ctx++repeat true n)=loop_return ctx.
Proof.
  induction n as [|n IH].
  - cbn [repeat]. now rewrite app_nil_r.
  - rewrite repeat_true_snoc, app_assoc, constructor_loop_return_true. exact IH.
Qed.
Definition v_pc ctx k := ctx ++ ([true;true] ++ repeat true k).
Lemma v_pc_next ctx k : v_pc ctx k ++ [true] = v_pc ctx (S k).
Proof. unfold v_pc. rewrite repeat_true_snoc. repeat rewrite app_assoc. reflexivity. Qed.
Lemma v_pc_return ctx k : loop_return (v_pc ctx k)=loop_return ctx.
Proof. unfold v_pc. change (loop_return (ctx++repeat true (S(S k)))=loop_return ctx).
  apply loop_return_true_repeat. Qed.

Lemma v_inc_nonfinal pc rs x :
  SourceSelect source_graph source_root (pc++[false]) (SInc 2) ->
  nth_error rs 2=Some x ->
  SourceProgramStep (pc,rs) (pc++[true],set_register 2 (S x) rs).
Proof.
  intros Sel V. pose proof (constructor_child_return pc 0) as [E W].
  cbn [repeat app] in E. rewrite <- W.
  eapply constructor_step_inc with (pad:=1) (i:=2) (value:=x) (count:=0).
  - exact Sel.
  - lia.
  - exact V.
  - exact E.
Qed.
Lemma v_inc_final pc rs x :
  SourceSelect source_graph source_root pc (SInc 2) -> nth_error rs 2=Some x ->
  SourceProgramStep (pc,rs) (loop_return pc,set_register 2 (S x) rs).
Proof.
  intros Sel V. destruct (loop_return_spec pc) as [out [n [E F]]]. rewrite F.
  eapply constructor_step_inc with (pad:=0) (i:=2) (value:=x) (count:=n).
  - now rewrite app_nil_r.
  - lia.
  - exact V.
  - now rewrite app_nil_r.
Qed.

Theorem v_increments_run m : 1<=m -> forall tag k ctx rs x,
  tag<=4 -> tag=k+m -> SourcePrefix source_graph source_root ctx (v_root tag) ->
  11<=length rs -> nth_error rs 2=Some x ->
  SourceProgramRuns (v_pc ctx k,rs) (loop_return ctx,set_register 2 (x+m) rs).
Proof.
  induction m as [|m IH]; intro M; [lia|].
  intros tag k ctx rs x Tag Equation Prefix Len V. destruct m as [|m].
  - pose proof (v_inc_selection tag k ltac:(lia) Tag ltac:(lia)) as Selection.
    pose proof (source_select_in_context _ _ _ _ _ _ Prefix Selection) as Sel.
    unfold v_inc_bits in Sel. assert (E : Nat.eqb (S k) tag = true) by (apply Nat.eqb_eq; lia).
    rewrite E, app_nil_r in Sel. change (SourceSelect source_graph source_root (v_pc ctx k) (SInc 2)) in Sel.
    pose proof (v_inc_final (v_pc ctx k) rs x Sel V) as Step.
    rewrite v_pc_return in Step. replace (x+1) with (S x) by lia.
    eapply source_program_next; [exact Step|constructor].
  - pose proof (v_inc_selection tag k ltac:(lia) Tag ltac:(lia)) as Selection.
    pose proof (source_select_in_context _ _ _ _ _ _ Prefix Selection) as Sel.
    unfold v_inc_bits in Sel. assert (E : Nat.eqb (S k) tag = false) by (apply Nat.eqb_neq; lia).
    rewrite E in Sel.
    assert (A : ctx ++ ([true;true] ++ repeat true k ++ [false]) = v_pc ctx k ++ [false]).
    { unfold v_pc. repeat rewrite app_assoc. reflexivity. }
    rewrite A in Sel.
    pose proof (v_inc_nonfinal (v_pc ctx k) rs x Sel V) as Step.
    rewrite v_pc_next in Step.
    assert (Len' : 11<=length(set_register 2 (S x) rs)) by (rewrite set_register_length; exact Len).
    assert (V' : nth_error (set_register 2 (S x) rs) 2=Some(S x)) by (apply nth_error_set_same; lia).
    pose proof (IH ltac:(lia) tag (S k) ctx (set_register 2 (S x) rs) (S x)
      Tag ltac:(lia) Prefix Len' V') as Tail.
    rewrite set_register_twice in Tail.
    replace (S x + S m) with (x + S (S m)) in Tail by lia.
    eapply source_program_next; eassumption.
Qed.
Print Assumptions v_inc_selection.
Print Assumptions v_increments_run.

Theorem source_v_nonempty tag ctx rs t s : tag<=4 ->
  SourcePrefix source_graph source_root ctx (v_root tag) -> 11<=length rs ->
  nth_error rs 2=Some t -> nth_error rs 3=Some s -> nth_error rs 8=Some 0 ->
  exists result mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (loop_return ctx,result) /\
    11<=length result /\ nth_error result 2=Some tag /\
    nth_error result 3=Some (cantor t s) /\ nth_error result 8=Some 0 /\
    outside_push rs result /\
    exists pad, skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  intros Tag Prefix L Top Stack Scratch. destruct tag as [|tag].
  - change (SourcePrefix source_graph source_root ctx source_pushwff_root) in Prefix.
    destruct (source_push_nonempty ctx rs t s Prefix L Top Stack Scratch)
      as [result [mid [First [Run [Len [T [S [X Frame]]]]]]]].
    assert (AllRun : SourceProgramRuns (ctx,rs) (loop_return ctx,result)).
    { eapply source_program_next; eassumption. }
    destruct (source_runs_zero_suffix _ _ AllRun L) as [pad [Pad _]].
    exists result,mid. repeat split; try assumption. exists pad. exact Pad.
  - destruct (v_layout (S tag) Tag) as [PairPrefix TransferPrefix].
    unfold v_transfer_bits in TransferPrefix. cbn [Nat.eqb] in TransferPrefix.
    pose proof (constructor_source_prefix_concat _ _ _ _ _ _ Prefix PairPrefix) as Ppair.
    destruct (source_pair_cantor_nonempty (ctx++[false]) 8 2 3 8 2 4 t s 0 rs
      pair_layout_push Ppair ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(lia) ltac:(lia) L Top Stack Scratch)
      as [r1 [mid [First [PairRun [L1 [T1 [S1 [X1 F1]]]]]]]].
    cbn [Nat.add_0_l] in X1. rewrite constructor_loop_return_false in PairRun.
    pose proof (constructor_source_prefix_concat _ _ _ _ _ _ Prefix TransferPrefix) as Ptransfer.
    destruct (while1_transfer_nonempty (ctx++[true;false]) 10 r1 8 3 (cantor t s) 0
      Ptransfer source_push_transfer_tree ltac:(lia) ltac:(lia) ltac:(lia) L1 X1 S1)
      as [mid2 [TransferFirst TransferRun]].
    replace (ctx++[true;false]) with ((ctx++[true])++[false]) in TransferRun by now rewrite <- app_assoc.
    rewrite constructor_loop_return_false in TransferRun.
    rewrite <- app_assoc in TransferRun. cbn [app] in TransferRun.
    set (r2 := set_register 3 (cantor t s) (set_register 8 0 r1) ++ repeat 0 (cantor t s)).
    change (SourceProgramRuns mid2 (ctx++[true;true],r2)) in TransferRun.
    assert (L2 : 11<=length r2).
    { unfold r2. rewrite length_app,repeat_length,!set_register_length. lia. }
    assert (T2 : nth_error r2 2=Some 0).
    { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      rewrite !nth_error_set_other by lia. exact T1. }
    assert (S2 : nth_error r2 3=Some (cantor t s)).
    { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      apply nth_error_set_same. rewrite set_register_length. lia. }
    assert (X2 : nth_error r2 8=Some 0).
    { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      rewrite nth_error_set_other by lia. apply nth_error_set_same. lia. }
    pose proof (v_increments_run (S tag) ltac:(lia) (S tag) 0 ctx r2 0
      Tag ltac:(lia) Prefix L2 T2) as Increments.
    cbn [v_pc repeat app Nat.add] in Increments.
    set (result := set_register 2 (S tag) r2).
    change (SourceProgramRuns (ctx++[true;true],r2) (loop_return ctx,result)) in Increments.
    assert (AllTail : SourceProgramRuns mid (loop_return ctx,result)).
    { eapply source_program_runs_trans; [exact PairRun|].
      eapply source_program_next with (t:=mid2).
      - eapply constructor_unpad_first_step with (pad:=1).
        change (SourceProgramStep ((ctx++[true])++[false],r1) mid2).
        rewrite <- app_assoc. exact TransferFirst.
      - eapply source_program_runs_trans; eassumption. }
    assert (AllRun : SourceProgramRuns (ctx,rs) (loop_return ctx,result)).
    { eapply source_program_next; [eapply constructor_unpad_first_step with (pad:=1); exact First|exact AllTail]. }
    destruct (source_runs_zero_suffix _ _ AllRun L) as [pad [Pad _]].
    exists result,mid. repeat split.
    + eapply constructor_unpad_first_step with (pad:=1). exact First.
    + exact AllTail.
    + unfold result. rewrite set_register_length. exact L2.
    + unfold result. apply nth_error_set_same. lia.
    + unfold result. rewrite nth_error_set_other by lia. exact S2.
    + unfold result. rewrite nth_error_set_other by lia. exact X2.
    + unfold outside_push. intros i I I2 I3 I8.
      unfold result. rewrite nth_error_set_other by lia.
      unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      rewrite !nth_error_set_other by lia. apply F1; lia.
    + exists pad. exact Pad.
Qed.
Print Assumptions source_v_nonempty.
