(** Arbitrary-register unpair source execution, including a nonempty trace. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerRegisters ConstructorArithmetic CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerExecution CompilerLoopBase CompilerLoops ConstructorGraph ConstructorUnpairFull ConstructorPairFull ConstructorUnpairGeneric SourceExecution.
Import ListNotations.

Lemma generic_outside_write i j k before rs reg v pad : outside_pair i j k before rs ->
  11 <= length rs -> (reg=i \/ reg=j \/ reg=k) ->
  outside_pair i j k before (write_pad reg v rs pad).
Proof.
  unfold outside_pair. intros F L D r R A B C.
  rewrite write_pad_other by (destruct D as [D|[D|D]]; subst; lia). now apply F.
Qed.

Definition generic_unpair_positive_store i j k rs n x y :=
  write_pad k y (write_pad j (S x) (write_pad i n rs [0]) []) [0].
Definition generic_unpair_zero_store i j k rs n x :=
  write_pad k (S x) (write_pad j 0 (write_pad j (S x) (write_pad i n rs [0]) []) [])
    (repeat 0 (S x)).

Lemma generic_positive_store_invariant i j k rs n x y :
  i < 11 -> j < 11 -> k < 11 -> i<>j -> i<>k -> j<>k -> 11 <= length rs ->
  11 <= length (generic_unpair_positive_store i j k rs n x y) /\
  nth_error (generic_unpair_positive_store i j k rs n x y) i = Some n /\
  nth_error (generic_unpair_positive_store i j k rs n x y) j = Some (S x) /\
  nth_error (generic_unpair_positive_store i j k rs n x y) k = Some y /\
  outside_pair i j k rs (generic_unpair_positive_store i j k rs n x y).
Proof.
  intros I J K IJ IK JK L. unfold generic_unpair_positive_store. repeat split.
  - repeat rewrite write_pad_length. simpl. lia.
  - rewrite write_pad_other by (repeat rewrite write_pad_length; simpl; lia).
    rewrite write_pad_other by (repeat rewrite write_pad_length; simpl; lia).
    apply write_pad_same. lia.
  - rewrite write_pad_other by (repeat rewrite write_pad_length; simpl; lia).
    apply write_pad_same. rewrite write_pad_length. simpl. lia.
  - apply write_pad_same. repeat rewrite write_pad_length. simpl. lia.
  - eapply generic_outside_write; [|repeat rewrite write_pad_length; simpl; lia|right; right; reflexivity].
    eapply generic_outside_write; [|rewrite write_pad_length; simpl; lia|right; left; reflexivity].
    eapply generic_outside_write; [apply outside_pair_refl|exact L|now left].
Qed.

Lemma generic_zero_store_invariant i j k rs n x :
  i < 11 -> j < 11 -> k < 11 -> i<>j -> i<>k -> j<>k -> 11 <= length rs ->
  11 <= length (generic_unpair_zero_store i j k rs n x) /\
  nth_error (generic_unpair_zero_store i j k rs n x) i = Some n /\
  nth_error (generic_unpair_zero_store i j k rs n x) j = Some 0 /\
  nth_error (generic_unpair_zero_store i j k rs n x) k = Some (S x) /\
  outside_pair i j k rs (generic_unpair_zero_store i j k rs n x).
Proof.
  intros I J K IJ IK JK L. unfold generic_unpair_zero_store. repeat split.
  - repeat rewrite write_pad_length. rewrite repeat_length. simpl. lia.
  - rewrite write_pad_other by (repeat rewrite write_pad_length; simpl; lia).
    rewrite write_pad_other by (repeat rewrite write_pad_length; simpl; lia).
    rewrite write_pad_other by (repeat rewrite write_pad_length; simpl; lia).
    apply write_pad_same. lia.
  - rewrite write_pad_other by (repeat rewrite write_pad_length; simpl; lia).
    apply write_pad_same. repeat rewrite write_pad_length. simpl. lia.
  - apply write_pad_same. repeat rewrite write_pad_length. simpl. lia.
  - eapply generic_outside_write; [|repeat rewrite write_pad_length; simpl; lia|right; right; reflexivity].
    eapply generic_outside_write; [|repeat rewrite write_pad_length; simpl; lia|right; left; reflexivity].
    eapply generic_outside_write; [|rewrite write_pad_length; simpl; lia|right; left; reflexivity].
    eapply generic_outside_write; [apply outside_pair_refl|exact L|now left].
Qed.

Theorem source_unpair_generic_nonempty ctx root i j k n x y rs :
  SourcePrefix source_graph source_root ctx root -> unfold_root root = Some (tree_unpair i j k) ->
  i < 11 -> j < 11 -> k < 11 -> i<>j -> i<>k -> j<>k -> 11 <= length rs ->
  nth_error rs i = Some n -> nth_error rs j = Some x -> nth_error rs k = Some y ->
  exists result mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (loop_return ctx,result) /\
    11 <= length result /\ nth_error result i = Some 0 /\
    (let '(a,b) := unpair_iterations n (x,y) in
      nth_error result j = Some a /\ nth_error result k = Some b) /\
    outside_pair i j k rs result.
Proof.
  intros P T I J K IJ IK JK. revert x y rs.
  induction n as [|n IH]; intros x y rs L N X Y.
  - exists rs,(loop_return ctx,rs). repeat split; try assumption; try apply outside_pair_refl; try constructor.
    eapply generic_unpair_input_zero; eassumption.
  - cbn [unpair_iterations unpair_advance]. destruct y as [|y].
    + pose proof (generic_zero_store_invariant i j k rs n x I J K IJ IK JK L)
        as [L' [N' [X' [Y' F]]]].
      destruct (IH 0 (S x) (generic_unpair_zero_store i j k rs n x) L' N' X' Y')
        as [result [mid' [Next [Run [Len [Input [Output Frame]]]]]]].
      assert (Cycle : SourceProgramRuns (ctx,rs) (ctx,generic_unpair_zero_store i j k rs n x)).
      { unfold generic_unpair_zero_store, write_pad. rewrite !app_nil_r.
        eapply generic_unpair_zero_output_cycle; eassumption. }
      assert (Diff : (ctx,rs) <> (ctx,generic_unpair_zero_store i j k rs n x)).
      { intro E. apply (f_equal (fun z => length (snd z))) in E. cbn [snd] in E.
        unfold generic_unpair_zero_store in E. repeat rewrite write_pad_length in E.
        rewrite repeat_length in E. simpl in E. lia. }
      destruct (source_runs_nonempty_when_distinct _ _ Cycle Diff) as [mid [First Rest]].
      exists result,mid. repeat split; try assumption.
      * eapply source_program_runs_trans; [exact Rest|]. eapply source_program_next; eassumption.
      * eapply outside_pair_trans; eassumption.
    + pose proof (generic_positive_store_invariant i j k rs n x y I J K IJ IK JK L)
        as [L' [N' [X' [Y' F]]]].
      destruct (IH (S x) y (generic_unpair_positive_store i j k rs n x y) L' N' X' Y')
        as [result [mid' [Next [Run [Len [Input [Output Frame]]]]]]].
      assert (Cycle : SourceProgramRuns (ctx,rs) (ctx,generic_unpair_positive_store i j k rs n x y)).
      { unfold generic_unpair_positive_store, write_pad. rewrite app_nil_r.
        eapply generic_unpair_positive_cycle; eassumption. }
      assert (Diff : (ctx,rs) <> (ctx,generic_unpair_positive_store i j k rs n x y)).
      { intro E. apply (f_equal (fun z => length (snd z))) in E. cbn [snd] in E.
        unfold generic_unpair_positive_store in E. repeat rewrite write_pad_length in E. simpl in E. lia. }
      destruct (source_runs_nonempty_when_distinct _ _ Cycle Diff) as [mid [First Rest]].
      exists result,mid. repeat split; try assumption.
      * eapply source_program_runs_trans; [exact Rest|]. eapply source_program_next; eassumption.
      * eapply outside_pair_trans; eassumption.
Qed.

Theorem source_unpair_generic_cantor_nonempty ctx root i j k a b rs :
  SourcePrefix source_graph source_root ctx root -> unfold_root root = Some (tree_unpair i j k) ->
  i < 11 -> j < 11 -> k < 11 -> i<>j -> i<>k -> j<>k -> 11 <= length rs ->
  nth_error rs i = Some (cantor a b) -> nth_error rs j = Some 0 -> nth_error rs k = Some 0 ->
  exists result mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (loop_return ctx,result) /\ 11 <= length result /\
    nth_error result i = Some 0 /\ nth_error result j = Some a /\ nth_error result k = Some b /\
    outside_pair i j k rs result.
Proof.
  intros P T I J K IJ IK JK L N X Y.
  destruct (source_unpair_generic_nonempty ctx root i j k (cantor a b) 0 0 rs
    P T I J K IJ IK JK L N X Y) as [result [mid [Step [Run [Len [Input [Output Frame]]]]]]].
  change (unpair_iterations (cantor a b) (0,0)) with (uncantor (cantor a b)) in Output.
  rewrite uncantor_cantor in Output. exists result,mid. repeat split; tauto.
Qed.

Print Assumptions source_unpair_generic_nonempty.
Print Assumptions source_unpair_generic_cantor_nonempty.
