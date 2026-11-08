(** Check the finite grammar's rule expansions against its complete environment. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import Syntax.
From Repair Require Import SyntaxData CompilerProof.
Import ListNotations.

Fixpoint same_nats xs ys :=
  match xs,ys with
  | [],[] => true
  | x::xs,y::ys => andb (Nat.eqb x y) (same_nats xs ys)
  | _,_ => false
  end.
Lemma same_nats_sound xs ys : same_nats xs ys = true -> xs = ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_true_iff in H as [A B]. apply Nat.eqb_eq in A. apply IH in B. now subst.
Qed.

Definition full_grammar_environment := definitions rules [].
Lemma full_grammar_environment_definition : full_grammar_environment = definitions rules [].
Proof. reflexivity. Qed.
Definition expansion_entry_check env entry :=
  let '(expanded,(a,b)) := entry in
  same_nats expanded (expand_symbol env a ++ expand_symbol env b).
Definition rule_expansion_check :=
  let env := full_grammar_environment in
  andb (Nat.eqb (length env) (length rules))
    (forallb (expansion_entry_check env) (combine env rules)).

Lemma rule_expansion_certificate : rule_expansion_check = true.
Proof. vm_compute. reflexivity. Qed.

Local Opaque full_grammar_environment rules.
Theorem full_environment_rule_expansion i a b : nth_error rules i = Some(a,b) ->
  nth i full_grammar_environment [] =
    expand_symbol full_grammar_environment a ++ expand_symbol full_grammar_environment b.
Proof.
  intro Rule. pose proof rule_expansion_certificate as C.
  unfold rule_expansion_check in C. apply andb_true_iff in C as [Len C].
  apply Nat.eqb_eq in Len. rewrite forallb_forall in C.
  assert (I : i < length full_grammar_environment).
  { rewrite Len. apply nth_error_Some. rewrite Rule. discriminate. }
  pose proof (@nth_error_nth' (list nat) full_grammar_environment i []) as Env.
  specialize (Env I).
  specialize (C (nth i full_grammar_environment [],(a,b))).
  assert (H : In (nth i full_grammar_environment [],(a,b)) (combine full_grammar_environment rules)).
  { apply nth_error_In with (n:=i). eapply nth_error_combine_some; eassumption. }
  specialize (C H). cbn [expansion_entry_check] in C. now apply same_nats_sound.
Qed.

Print Assumptions rule_expansion_certificate.
Print Assumptions full_environment_rule_expansion.
