(** Exact repaired formula extension and full compressed grammar expansion. *)
From Stdlib Require Import Lists.List.
From Berkeley Require Import Syntax SyntaxData.
From Repair Require Import SyntaxData.
Import ListNotations.

Definition guarded_distinction_formula := Neg (All (P 1) (Atom false (P 1) (P 2))).
Theorem repair_axioms_extend_original :
  repair_axioms = candidate_axioms ++ [guarded_distinction_formula].
Proof. vm_compute. reflexivity. Qed.
Theorem grammar_emits_exact_axioms :
  map (expand_word (definitions rules [])) residuals = map emit repair_axioms.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions repair_axioms_extend_original.
Print Assumptions grammar_emits_exact_axioms.
