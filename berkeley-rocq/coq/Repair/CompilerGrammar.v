(** Finite connection from the checked compressed syntax grammar to the
    extracted binary source DAG.  All node IDs here are source IDs. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import Syntax CompilerSyntax.
From Repair Require Import SyntaxData CompilerData.
Import ListNotations.

Fixpoint token_root (n : nat) (table : list (nat * nat)) : option nat :=
  match table with
  | [] => None
  | (code,root)::rest => if Nat.eqb n code then Some root else token_root n rest
  end.
Definition symbol_root limit (s : symbol) : option nat :=
  match s with
  | Terminal n => token_root n source_token_roots
  | Reference n => if n <? limit then nth_error source_rule_roots n else None
  end.
Fixpoint word_roots limit (xs : list symbol) : option (list nat) :=
  match xs with
  | [] => Some []
  | x::xs => match symbol_root limit x, word_roots limit xs with
             | Some a, Some rest => Some (a::rest)
             | _,_ => None
             end
  end.
Definition pair_refs_match root left right : bool :=
  match nth_error source_graph root with
  | Some (SNode a,SNode b) => andb (Nat.eqb a left) (Nat.eqb b right)
  | _ => false
  end.
Definition check_rule i : bool :=
  match nth_error rules i, nth_error source_rule_roots i with
  | Some (a,b), Some root =>
      match symbol_root i a, symbol_root i b with
      | Some lroot, Some rroot => pair_refs_match root lroot rroot
      | _,_ => false
      end
  | _,_ => false
  end.

Fixpoint sequence_match root (xs : list nat) : bool :=
  match xs with
  | [] => false
  | [x] => Nat.eqb root x
  | a::rest =>
      match nth_error source_graph root with
      | Some (SNode l,SNode r) => andb (Nat.eqb a l) (sequence_match r rest)
      | _ => false
      end
  end.
Definition check_residual i : bool :=
  match nth_error residuals i, nth_error source_residual_roots i with
  | Some word, Some root =>
      match word_roots (length rules) word with
      | Some nodes => sequence_match root nodes
      | None => false
      end
  | _,_ => false
  end.
Definition grammar_source_check : bool :=
  andb (Nat.eqb (length rules) (length source_rule_roots))
  (andb (Nat.eqb (length residuals) (length source_residual_roots))
  (andb (forallb check_rule (seq 0 (length rules)))
        (forallb check_residual (seq 0 (length residuals))))).

Lemma grammar_source_certificate : grammar_source_check = true.
Proof. vm_compute. reflexivity. Qed.

Inductive SourceSequence : nat -> list nat -> Prop :=
| source_sequence_singleton a : SourceSequence a [a]
| source_sequence_cons root a tail b rest :
    nth_error source_graph root = Some(SNode a,SNode tail) ->
    SourceSequence tail (b::rest) -> SourceSequence root (a::b::rest).

Lemma sequence_match_sound root xs : sequence_match root xs = true -> SourceSequence root xs.
Proof.
  revert root. induction xs as [|a rest IH]; intros root H; [discriminate|].
  destruct rest as [|b rest].
  - cbn [sequence_match] in H. apply Nat.eqb_eq in H. subst. constructor.
  - cbn [sequence_match] in H.
    destruct (nth_error source_graph root) as [[left right]|] eqn:E; [|discriminate].
    destruct left as [l| | | | |]; try discriminate.
    destruct right as [r| | | | |]; try discriminate.
    apply andb_true_iff in H as [A B]. apply Nat.eqb_eq in A. subst l.
    econstructor; [exact E|]. now apply IH.
Qed.

Lemma pair_refs_match_sound root left right : pair_refs_match root left right = true ->
  nth_error source_graph root = Some(SNode left,SNode right).
Proof.
  unfold pair_refs_match. destruct (nth_error source_graph root) as [[a b]|] eqn:E;
    [|discriminate]. destruct a as [l| | | | |]; try discriminate.
  destruct b as [r| | | | |]; try discriminate.
  intro H. apply andb_true_iff in H as [A B].
  apply Nat.eqb_eq in A. apply Nat.eqb_eq in B. subst. reflexivity.
Qed.

Theorem grammar_rule_is_source_pair i a b : nth_error rules i = Some (a,b) ->
  exists root left right,
    nth_error source_rule_roots i = Some root /\
    symbol_root i a = Some left /\ symbol_root i b = Some right /\
    nth_error source_graph root = Some(SNode left,SNode right).
Proof.
  intro Rule. pose proof grammar_source_certificate as C.
  unfold grammar_source_check in C.
  apply andb_true_iff in C as [_ C]. apply andb_true_iff in C as [_ C].
  apply andb_true_iff in C as [C _]. rewrite forallb_forall in C.
  assert (I : In i (seq 0 (length rules))).
  { apply in_seq. assert (H : i < length rules).
    { apply nth_error_Some. rewrite Rule. discriminate. } lia. }
  specialize (C i I). unfold check_rule in C. rewrite Rule in C.
  destruct (nth_error source_rule_roots i) as [root|] eqn:R; [|discriminate].
  destruct (symbol_root i a) as [left|] eqn:A; [|discriminate].
  destruct (symbol_root i b) as [right|] eqn:B; [|discriminate].
  exists root,left,right. repeat split; try reflexivity.
  now apply pair_refs_match_sound.
Qed.

Theorem grammar_residual_is_source_sequence i word : nth_error residuals i = Some word ->
  exists root nodes,
    nth_error source_residual_roots i = Some root /\
    word_roots (length rules) word = Some nodes /\ SourceSequence root nodes.
Proof.
  intro Word. pose proof grammar_source_certificate as C.
  unfold grammar_source_check in C.
  apply andb_true_iff in C as [_ C]. apply andb_true_iff in C as [_ C].
  apply andb_true_iff in C as [_ C]. rewrite forallb_forall in C.
  assert (I : In i (seq 0 (length residuals))).
  { apply in_seq. assert (H : i < length residuals).
    { apply nth_error_Some. rewrite Word. discriminate. } lia. }
  specialize (C i I). unfold check_residual in C. rewrite Word in C.
  destruct (nth_error source_residual_roots i) as [root|] eqn:R; [|discriminate].
  destruct (word_roots (length rules) word) as [nodes|] eqn:W; [|discriminate].
  exists root,nodes. repeat split; try reflexivity. now apply sequence_match_sound.
Qed.

Print Assumptions grammar_source_certificate.
Print Assumptions grammar_rule_is_source_pair.
Print Assumptions grammar_residual_is_source_sequence.
