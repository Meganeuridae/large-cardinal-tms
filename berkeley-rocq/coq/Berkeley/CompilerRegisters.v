(** Register-list operations and finite PC returns for source block proofs. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import RuntimeTape RuntimeControl RuntimeCalls.
Import ListNotations.

Fixpoint set_register (i value : nat) (rs : list nat) : list nat :=
  match i,rs with
  | _,[] => []
  | 0,_::tail => value::tail
  | S j,x::tail => x::set_register j value tail
  end.

Lemma set_register_length i value rs : length (set_register i value rs) = length rs.
Proof. revert i. induction rs as [|x xs IH]; intros [|i]; cbn; auto. Qed.

Lemma set_register_split before old after value :
  set_register (length before) value (before++old::after) = before++value::after.
Proof. induction before; cbn; [reflexivity|now rewrite IHbefore]. Qed.

Lemma nth_error_set_same i value rs : i < length rs ->
  nth_error (set_register i value rs) i = Some value.
Proof.
  revert i. induction rs as [|x xs IH]; intros [|i] H; cbn in *; try lia; auto.
  apply IH. lia.
Qed.

Lemma nth_error_set_other i j value rs : i <> j ->
  nth_error (set_register i value rs) j = nth_error rs j.
Proof.
  revert i j. induction rs as [|x xs IH]; intros [|i] [|j] H; cbn in *; try congruence.
  apply IH. congruence.
Qed.

Lemma set_register_append i value rs suffix : i < length rs ->
  set_register i value (rs++suffix) = set_register i value rs ++ suffix.
Proof.
  revert i. induction rs as [|x xs IH]; intros [|i] H; cbn in *; try lia; auto.
  rewrite IH by lia. reflexivity.
Qed.

Lemma set_register_twice i v w rs :
  set_register i v (set_register i w rs) = set_register i v rs.
Proof. revert i. induction rs as [|x xs IH]; intros [|i]; cbn; auto. now rewrite IH. Qed.

Lemma set_register_commute i j v w rs : i <> j ->
  set_register i v (set_register j w rs) = set_register j w (set_register i v rs).
Proof.
  revert i j. induction rs as [|x xs IH]; intros [|i] [|j] H; cbn in *; try congruence; auto.
  rewrite IH by congruence. reflexivity.
Qed.

Lemma set_register_noop i v rs : nth_error rs i = Some v -> set_register i v rs = rs.
Proof.
  intro H. apply nth_error_split in H as [before [after [-> L]]].
  subst i. apply set_register_split.
Qed.

Definition loop_return ctx :=
  match break_pc 0 (rev ctx++[false]) with
  | Some (out,_) => return_word out
  | None => []
  end.
Lemma loop_return_spec ctx : exists out n,
  break_pc 0 (rev ctx++[false]) = Some(out,n) /\ loop_return ctx = return_word out.
Proof.
  assert (H : 0 < zeros (rev ctx++[false])).
  { rewrite zeros_app. cbn [zeros]. lia. }
  destruct (break_pc_total 0 _ H) as [out [n E]].
  exists out,n. split; [exact E|]. unfold loop_return. now rewrite E.
Qed.

Print Assumptions set_register_commute.
Print Assumptions loop_return_spec.
