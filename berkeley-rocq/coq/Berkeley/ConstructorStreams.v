(** Executable semantics of the primitive axiom-emitter constructor tokens.

    Formula parameters and variable parameters use the same numeric
    registers in ZF2.  Their interpretation is therefore a single arbitrary
    function [params]; only their positions in the syntax differ. *)
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia.
From Berkeley Require Import Syntax SyntaxData Certificate ConstructorArithmetic ConstructorRegisters.
Import ListNotations.

Definition bind {A B : Type} (o : option A) (f : A -> option B) :=
  match o with Some x => f x | None => None end.

Definition source_variable n r := bind (source_push r) (fun r' => Some (increment_top n r')).
Definition source_parameter p r :=
  match source_param p r with Some (r',_) => Some r' | None => None end.
Definition source_binary tag r :=
  bind (source_cons r) (fun r' =>
  bind (source_push r') (fun r'' => source_cons (increment_top tag r''))).
Definition source_negation r :=
  bind (source_push r) (fun r' => source_cons (increment_top 3 r')).

Lemma source_variable_correct n t s :
  source_variable n (CR t s 0 0) = Some (CR n (cantor t s) 0 0).
Proof.
  unfold source_variable. rewrite source_push_correct.
  reflexivity.
Qed.
Lemma source_parameter_correct p t s :
  source_parameter p (CR t s 0 0) = Some (CR p (cantor t s) 0 0).
Proof. unfold source_parameter. now rewrite source_param_correct. Qed.
Lemma source_binary_correct tag a b s :
  source_binary tag (CR b (cantor a s) 0 0) =
    Some (CR (cantor (cantor a b) tag) s 0 0).
Proof.
  unfold source_binary. rewrite source_cons_correct. cbn [bind].
  rewrite source_push_correct. cbn [bind increment_top top stack scratch1 scratch2].
  change (source_cons (CR tag (cantor (cantor a b) s) 0 0) =
          Some (CR (cantor (cantor a b) tag) s 0 0)).
  apply source_cons_correct.
Qed.
Lemma source_negation_correct p s :
  source_negation (CR p s 0 0) = Some (CR (cantor p 3) s 0 0).
Proof.
  unfold source_negation. rewrite source_push_correct.
  cbn [bind increment_top top stack scratch1 scratch2].
  change (source_cons (CR 3 (cantor p s) 0 0) = Some (CR (cantor p 3) s 0 0)).
  apply source_cons_correct.
Qed.

(** The token numbering is exactly Syntax.emit/export.py's convention:
    0..4 are weq, wel, wn, wim, wal, 8..15 are parameter pushes, and
    16+n is variable n. Unused 5..7 are rejected. *)
Definition token_step (params : nat -> nat) (tok : nat) (r : constructor_registers)
    : option constructor_registers :=
  match tok with
  | 0 => source_binary 0 r
  | 1 => source_binary 1 r
  | 2 => source_negation r
  | 3 => source_binary 2 r
  | 4 => source_binary 4 r
  | _ => if tok <? 8 then None
         else if tok <? 16 then source_parameter (params (tok-8)) r
         else source_variable (tok-16) r
  end.

Fixpoint run_tokens (params : nat -> nat) (ts : list nat) (r : constructor_registers)
    : option constructor_registers :=
  match ts with
  | [] => Some r
  | t::rest => bind (token_step params t r) (run_tokens params rest)
  end.

Lemma run_tokens_append params xs ys r :
  run_tokens params (xs++ys) r = bind (run_tokens params xs r) (run_tokens params ys).
Proof.
  revert r. induction xs as [|x xs IH]; intro r; [reflexivity|].
  cbn [app run_tokens]. unfold bind at 1.
  destruct (token_step params x r); [apply IH|reflexivity].
Qed.

Definition variable_value params x :=
  match x with V n => n | P n => params n end.
Fixpoint formula_code params f :=
  match f with
  | Atom b x y => cantor (cantor (variable_value params x) (variable_value params y))
                           (if b then 1 else 0)
  | Neg p => cantor (formula_code params p) 3
  | Imp p q => cantor (cantor (formula_code params p) (formula_code params q)) 2
  | All x p => cantor (cantor (variable_value params x) (formula_code params p)) 4
  | Hole n => params n
  end.

Definition valid_variable x := match x with V _ => true | P n => n <? 8 end.
Fixpoint valid_formula f :=
  match f with
  | Atom _ x y => valid_variable x && valid_variable y
  | Neg p => valid_formula p
  | Imp p q => valid_formula p && valid_formula q
  | All x p => valid_variable x && valid_formula p
  | Hole n => n <? 8
  end.

Lemma parameter_token_correct params n t s : n < 8 ->
  token_step params (8+n) (CR t s 0 0) = Some (CR (params n) (cantor t s) 0 0).
Proof.
  intro H. unfold token_step.
  cbn. assert (H7 : (n <=? 7) = true) by (apply Nat.leb_le; lia).
  rewrite H7, Nat.sub_0_r.
  apply source_parameter_correct.
Qed.

Lemma variable_token_correct params x t s : valid_variable x = true ->
  token_step params (var_token x) (CR t s 0 0) =
    Some (CR (variable_value params x) (cantor t s) 0 0).
Proof.
  destruct x as [n|n]; cbn [valid_variable var_token variable_value].
  - intro H. unfold token_step.
    cbn. rewrite Nat.sub_0_r.
    apply source_variable_correct.
  - intro H. apply Nat.ltb_lt in H. now apply parameter_token_correct.
Qed.

Theorem emitted_formula_constructs_code params f : valid_formula f = true ->
  forall t s, run_tokens params (emit f) (CR t s 0 0) =
    Some (CR (formula_code params f) (cantor t s) 0 0).
Proof.
  induction f as [b x y|p IHp|p IHp q IHq|x p IHp|n]; intros H t s.
  - cbn [valid_formula] in H. apply andb_true_iff in H as [Hx Hy].
    cbn [emit run_tokens app]. rewrite variable_token_correct by exact Hx. cbn [bind].
    rewrite variable_token_correct by exact Hy. cbn [bind].
    destruct b; cbn [token_step run_tokens bind formula_code]; now rewrite source_binary_correct.
  - cbn [valid_formula] in H. cbn [emit]. rewrite run_tokens_append, IHp by exact H.
    cbn [bind run_tokens token_step formula_code]. now rewrite source_negation_correct.
  - cbn [valid_formula] in H. apply andb_true_iff in H as [Hp Hq].
    cbn [emit]. rewrite !run_tokens_append, IHp by exact Hp.
    cbn [bind]. rewrite run_tokens_append, IHq by exact Hq. cbn [bind run_tokens token_step formula_code].
    now rewrite source_binary_correct.
  - cbn [valid_formula] in H. apply andb_true_iff in H as [Hx Hp].
    cbn [emit run_tokens app]. rewrite variable_token_correct by exact Hx. cbn [bind].
    rewrite run_tokens_append, IHp by exact Hp.
    cbn [bind run_tokens token_step formula_code]. now rewrite source_binary_correct.
  - cbn [valid_formula] in H. apply Nat.ltb_lt in H.
    cbn [emit run_tokens formula_code]. rewrite parameter_token_correct by exact H. reflexivity.
Qed.

Lemma candidate_formula_tokens_valid : forallb valid_formula candidate_axioms = true.
Proof. vm_compute. reflexivity. Qed.

(** This theorem uses the already kernel-checked grammar expansion, not a
    second computation of the large formula codes.  It is uniform in all
    numeric parameters, the prior top, and the prior encoded stack. *)
Theorem grammar_stream_constructs_formula params i f stream t s :
  nth_error candidate_axioms i = Some f ->
  nth_error (map (expand_word (definitions rules [])) residuals) i = Some stream ->
  run_tokens params stream (CR t s 0 0) =
    Some (CR (formula_code params f) (cantor t s) 0 0).
Proof.
  intros Hf Hstream. rewrite grammar_emits_exact_axioms, nth_error_map, Hf in Hstream.
  inversion Hstream; subst stream. apply emitted_formula_constructs_code.
  pose proof (proj1 (forallb_forall valid_formula candidate_axioms) candidate_formula_tokens_valid) as Hvalid.
  apply Hvalid. eapply nth_error_In; eassumption.
Qed.

Print Assumptions source_variable_correct.
Print Assumptions source_parameter_correct.
Print Assumptions source_binary_correct.
Print Assumptions source_negation_correct.
Print Assumptions emitted_formula_constructs_code.
Print Assumptions grammar_stream_constructs_formula.
