(** Complete source-control contract for the unpair loop, including the
    first 11-register frame and the machine's extra zero-register suffix. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerData CompilerReverse CompilerExecution
  CompilerRegisters CompilerLoopBase ConstructorArithmetic ConstructorUnpair.
Import ListNotations.

Definition write_pad i v rs pad := set_register i v rs ++ pad.
Lemma write_pad_length i v rs pad : length (write_pad i v rs pad) = length rs + length pad.
Proof. unfold write_pad. now rewrite app_length, set_register_length. Qed.
Lemma write_pad_same i v rs pad : i < length rs -> nth_error (write_pad i v rs pad) i = Some v.
Proof.
  intro H. unfold write_pad. rewrite nth_error_app1 by (rewrite set_register_length; exact H).
  now apply nth_error_set_same.
Qed.
Lemma write_pad_other i v rs pad j : i <> j -> j < length rs ->
  nth_error (write_pad i v rs pad) j = nth_error rs j.
Proof.
  intros D H. unfold write_pad. rewrite nth_error_app1 by (rewrite set_register_length; exact H).
  now apply nth_error_set_other.
Qed.

Definition outside_unpair (before after : list nat) := forall i, i < 11 -> i <> 3 -> i <> 8 -> i <> 9 ->
  nth_error after i = nth_error before i.
Lemma outside_unpair_refl rs : outside_unpair rs rs.
Proof. firstorder. Qed.
Lemma outside_unpair_trans a b c : outside_unpair a b -> outside_unpair b c -> outside_unpair a c.
Proof. unfold outside_unpair. intros A B i H I J K. now rewrite B, A by assumption. Qed.
Lemma outside_unpair_write before rs i v pad : outside_unpair before rs -> 11 <= length rs ->
  (i=3 \/ i=8 \/ i=9) -> outside_unpair before (write_pad i v rs pad).
Proof.
  unfold outside_unpair. intros F L D j H A B C.
  rewrite write_pad_other by (destruct D as [D|[D|D]]; subst; lia).
  now apply F.
Qed.

Definition unpair_positive_store rs n x y :=
  write_pad 9 y (write_pad 8 (S x) (write_pad 3 n rs [0]) []) [0].
Definition unpair_zero_store rs n x :=
  write_pad 9 (S x) (write_pad 8 0 (write_pad 8 (S x) (write_pad 3 n rs [0]) []) [])
    (repeat 0 (S x)).

Lemma unpair_positive_store_invariant rs n x y :
  11 <= length rs -> nth_error rs 8 = Some x -> nth_error rs 9 = Some (S y) ->
  11 <= length (unpair_positive_store rs n x y) /\
  nth_error (unpair_positive_store rs n x y) 3 = Some n /\
  nth_error (unpair_positive_store rs n x y) 8 = Some (S x) /\
  nth_error (unpair_positive_store rs n x y) 9 = Some y /\
  outside_unpair rs (unpair_positive_store rs n x y).
Proof.
  intros L X Y. unfold unpair_positive_store. repeat split.
  - repeat rewrite write_pad_length. simpl. lia.
  - rewrite write_pad_other by (repeat rewrite write_pad_length; simpl; lia).
    rewrite write_pad_other by (repeat rewrite write_pad_length; simpl; lia).
    apply write_pad_same. lia.
  - rewrite write_pad_other by (repeat rewrite write_pad_length; simpl; lia).
    apply write_pad_same. rewrite write_pad_length. simpl. lia.
  - apply write_pad_same. repeat rewrite write_pad_length. simpl. lia.
  - eapply outside_unpair_write; [|repeat rewrite write_pad_length; simpl; lia|right; right; reflexivity].
    eapply outside_unpair_write; [|rewrite write_pad_length; simpl; lia|right; left; reflexivity].
    eapply outside_unpair_write; [apply outside_unpair_refl|exact L|now left].
Qed.

Lemma unpair_zero_store_invariant rs n x :
  11 <= length rs -> nth_error rs 8 = Some x -> nth_error rs 9 = Some 0 ->
  11 <= length (unpair_zero_store rs n x) /\
  nth_error (unpair_zero_store rs n x) 3 = Some n /\
  nth_error (unpair_zero_store rs n x) 8 = Some 0 /\
  nth_error (unpair_zero_store rs n x) 9 = Some (S x) /\
  outside_unpair rs (unpair_zero_store rs n x).
Proof.
  intros L X Y. unfold unpair_zero_store. repeat split.
  - repeat rewrite write_pad_length. rewrite repeat_length. simpl. lia.
  - rewrite write_pad_other by (repeat rewrite write_pad_length; simpl; lia).
    rewrite write_pad_other by (repeat rewrite write_pad_length; simpl; lia).
    rewrite write_pad_other by (repeat rewrite write_pad_length; simpl; lia).
    apply write_pad_same. lia.
  - rewrite write_pad_other by (repeat rewrite write_pad_length; simpl; lia).
    apply write_pad_same. repeat rewrite write_pad_length. simpl. lia.
  - apply write_pad_same. repeat rewrite write_pad_length. simpl. lia.
  - eapply outside_unpair_write; [|repeat rewrite write_pad_length; simpl; lia|right; right; reflexivity].
    eapply outside_unpair_write; [|repeat rewrite write_pad_length; simpl; lia|right; left; reflexivity].
    eapply outside_unpair_write; [|rewrite write_pad_length; simpl; lia|right; left; reflexivity].
    eapply outside_unpair_write; [apply outside_unpair_refl|exact L|now left].
Qed.

Theorem source_unpair_iterations ctx n x y rs :
  SourcePrefix source_graph source_root ctx 29 -> 11 <= length rs ->
  nth_error rs 3 = Some n -> nth_error rs 8 = Some x -> nth_error rs 9 = Some y ->
  exists result, SourceProgramRuns (ctx,rs) (loop_return ctx,result) /\
    11 <= length result /\ nth_error result 3 = Some 0 /\
    (let '(a,b) := unpair_iterations n (x,y) in
      nth_error result 8 = Some a /\ nth_error result 9 = Some b) /\
    outside_unpair rs result.
Proof.
  revert x y rs. induction n as [|n IH]; intros x y rs P L N X Y.
  - exists rs. repeat split; try assumption; try apply outside_unpair_refl.
    eapply source_program_next; [apply source_unpair_input_zero; eassumption|constructor].
  - cbn [unpair_iterations unpair_advance]. destruct y as [|y].
    + pose proof (unpair_zero_store_invariant rs n x L X Y) as [L' [N' [X' [Y' F]]]].
      destruct (IH 0 (S x) (unpair_zero_store rs n x) P L' N' X' Y')
        as [result [Run [Len [Input [Output Frame]]]]].
      exists result. repeat split; try assumption.
      * eapply source_program_runs_trans; [|exact Run].
        unfold unpair_zero_store, write_pad. rewrite !app_nil_r.
        apply source_unpair_zero_output_cycle; assumption.
      * eapply outside_unpair_trans; eassumption.
    + pose proof (unpair_positive_store_invariant rs n x y L X Y) as [L' [N' [X' [Y' F]]]].
      destruct (IH (S x) y (unpair_positive_store rs n x y) P L' N' X' Y')
        as [result [Run [Len [Input [Output Frame]]]]].
      exists result. repeat split; try assumption.
      * eapply source_program_runs_trans; [|exact Run].
        unfold unpair_positive_store, write_pad. rewrite app_nil_r.
        apply source_unpair_positive_cycle; assumption.
      * eapply outside_unpair_trans; eassumption.
Qed.

Theorem source_unpair_cantor ctx rs a b :
  SourcePrefix source_graph source_root ctx 29 -> 11 <= length rs ->
  nth_error rs 3 = Some (cantor a b) -> nth_error rs 8 = Some 0 -> nth_error rs 9 = Some 0 ->
  exists result, SourceProgramRuns (ctx,rs) (loop_return ctx,result) /\
    11 <= length result /\ nth_error result 3 = Some 0 /\
    nth_error result 8 = Some a /\ nth_error result 9 = Some b /\ outside_unpair rs result.
Proof.
  intros P L N X Y.
  destruct (source_unpair_iterations ctx (cantor a b) 0 0 rs P L N X Y)
    as [result [Run [Len [Input [Output Frame]]]]].
  change (unpair_iterations (cantor a b) (0,0)) with (uncantor (cantor a b)) in Output.
  rewrite uncantor_cantor in Output. exists result. repeat split; tauto.
Qed.

Print Assumptions source_unpair_iterations.
Print Assumptions source_unpair_cantor.
