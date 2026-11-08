From Stdlib Require Import Lists.List.
From Berkeley Require Import Syntax SyntaxData.
Import ListNotations.

(** Bound names disappear, and the complete first-order syntax agrees. *)
Theorem all_axioms_alpha_equivalent :
  map (fun f => canonical f []) original_axioms =
  map (fun f => canonical f []) candidate_axioms.
Proof. vm_compute. reflexivity. Qed.

(** This verifies the finite grammar's expansion, not the register-to-TM compiler. *)
Theorem grammar_emits_exact_axioms :
  map (expand_word (definitions rules [])) residuals = map emit candidate_axioms.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions all_axioms_alpha_equivalent.
Print Assumptions grammar_emits_exact_axioms.
