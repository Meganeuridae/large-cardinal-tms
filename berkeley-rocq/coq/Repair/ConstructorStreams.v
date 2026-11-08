(** Formula-stack semantics for the repaired grammar, reusing the original
    primitive constructor interpreter and its formula-encoding theorem. *)
From Stdlib Require Import Lists.List.
From Berkeley Require Import Syntax ConstructorArithmetic ConstructorRegisters.
From Berkeley Require Export ConstructorStreams.
From Repair Require Import SyntaxData Certificate.
Import ListNotations.

Lemma repair_formula_tokens_valid : forallb valid_formula repair_axioms=true.
Proof. vm_compute. reflexivity. Qed.

Theorem grammar_stream_constructs_repair_formula params i f stream t s :
  nth_error repair_axioms i=Some f ->
  nth_error (map (expand_word (definitions rules [])) residuals) i=Some stream ->
  run_tokens params stream (CR t s 0 0)=Some (CR (formula_code params f) (cantor t s) 0 0).
Proof.
  intros Hf Hstream. rewrite grammar_emits_exact_axioms,nth_error_map,Hf in Hstream.
  inversion Hstream; subst stream. apply emitted_formula_constructs_code.
  pose proof (proj1 (forallb_forall valid_formula repair_axioms) repair_formula_tokens_valid) as Valid.
  apply Valid. eapply nth_error_In; eassumption.
Qed.
Theorem grammar_stream_constructs_formula params i f stream t s :
  nth_error candidate_axioms i=Some f ->
  nth_error (map (expand_word (definitions rules [])) residuals) i=Some stream ->
  run_tokens params stream (CR t s 0 0)=Some (CR (formula_code params f) (cantor t s) 0 0).
Proof.
  intros F S. eapply grammar_stream_constructs_repair_formula; [|exact S].
  rewrite repair_axioms_extend_original,nth_error_app1; [exact F|].
  apply nth_error_Some. rewrite F. discriminate.
Qed.
Print Assumptions grammar_stream_constructs_formula.
