(** Instantiated, kernel-checked versions of the quantifier lemmas needed for
    the fresh-variable bridge. The certificate data use explicit substitutions. *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
From Berkeley Require Import Syntax TheorySchemas ProofFormula ProofPresentation LogicBridge LogicCertificates LogicCertificateData.
Import ListNotations.
Definition dummy_formula := FEqual 0 0.
Definition quant_holes (p q : fol_formula) n :=
  match n with 1 => p | 2 => p | _ => q end.
Theorem logical_equality_exists x y : LogicalProvable (FNeg (FAll x (FNeg (FEqual x y)))).
Proof. exact (L18_certificate (logic_vars x y 0) (fun _ => dummy_formula)). Qed.
Theorem logical_distinctor_stable x y z :
  LogicalProvable (FImp (FNeg (FAll x (FEqual x y)))
    (FAll z (FNeg (FAll x (FEqual x y))))).
Proof. exact (L19_certificate (logic_vars x y z) (fun _ => dummy_formula)). Qed.
Theorem logical_fresh_implication x p q : LogicalProvable
  (FImp (FAll x (FImp p (FAll x p)))
   (FImp (FImp q (FAll x q)) (FImp (FImp p q) (FAll x (FImp p q))))).
Proof. exact (L20_certificate (logic_vars x 0 0) (quant_holes p q)). Qed.
Theorem logical_fresh_negation x p : LogicalProvable
  (FImp (FAll x (FImp p (FAll x p))) (FImp (FNeg p) (FAll x (FNeg p)))).
Proof. exact (L21_certificate (logic_vars x 0 0) (fun _ => p)). Qed.
Theorem logical_fresh_quantifier x y p : LogicalProvable
  (FImp (FAll y (FImp p (FAll x p))) (FImp (FAll y p) (FAll x (FAll y p)))).
Proof. exact (L22_certificate (logic_vars y x 0) (fun _ => p)). Qed.
Print Assumptions logical_equality_exists.
Print Assumptions logical_distinctor_stable.
Print Assumptions logical_fresh_implication.
Print Assumptions logical_fresh_negation.
Print Assumptions logical_fresh_quantifier.

Lemma logical_b9 x y z : LogicalProvable
  (FImp (FNeg (FAll x (FEqual x y)))
   (FImp (FNeg (FAll x (FEqual x z))) (FImp (FEqual y z) (FAll x (FEqual y z))))).
Proof.
  change (LogicalProvable (independent_instance (logic_vars x y z) (fun _ => dummy_formula)
    (nth 8 logical_schemas (Hole 0)))).
  eapply logical_axiom with (i:=8). reflexivity.
Qed.
Lemma logical_b14 x y z : LogicalProvable
  (FImp (FNeg (FAll x (FEqual x y)))
   (FImp (FNeg (FAll x (FEqual x z))) (FImp (FMember y z) (FAll x (FMember y z))))).
Proof.
  change (LogicalProvable (independent_instance (logic_vars x y z) (fun _ => dummy_formula)
    (nth 13 logical_schemas (Hole 0)))).
  eapply logical_axiom with (i:=13). reflexivity.
Qed.
Print Assumptions logical_b9.
Print Assumptions logical_b14.
Lemma logical_b8 x y z : LogicalProvable
  (FImp (FEqual x y) (FImp (FEqual x z) (FEqual y z))).
Proof.
  change (LogicalProvable (independent_instance (logic_vars x y z) (fun _ => dummy_formula)
    (nth 7 logical_schemas (Hole 0)))).
  eapply logical_axiom with (i:=7). reflexivity.
Qed.
Lemma logical_b12 x y z : LogicalProvable
  (FImp (FEqual x y) (FImp (FMember x z) (FMember y z))).
Proof.
  change (LogicalProvable (independent_instance (logic_vars x y z) (fun _ => dummy_formula)
    (nth 11 logical_schemas (Hole 0)))).
  eapply logical_axiom with (i:=11). reflexivity.
Qed.
Lemma logical_b13 x y z : LogicalProvable
  (FImp (FEqual x y) (FImp (FMember z x) (FMember z y))).
Proof.
  change (LogicalProvable (independent_instance (logic_vars x y z) (fun _ => dummy_formula)
    (nth 12 logical_schemas (Hole 0)))).
  eapply logical_axiom with (i:=12). reflexivity.
Qed.
Theorem logical_equality_right x y z : LogicalProvable
  (FImp (FEqual x y) (FImp (FEqual z x) (FEqual z y))).
Proof. exact (L17_certificate (logic_vars x y z) (fun _ => dummy_formula)). Qed.
Print Assumptions logical_b8.
Print Assumptions logical_b12.
Print Assumptions logical_b13.
Print Assumptions logical_equality_right.
