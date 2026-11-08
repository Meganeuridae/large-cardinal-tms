(** Truth rows for negation, implication and universal quantification, each
    produced by a concrete first-order Separation instance. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import ProofFormula FormulaSemantics BerkeleySyntaxBase BerkeleySyntaxInterpretation BerkeleySyntaxPairs
  BerkeleySyntaxFunction BerkeleySyntaxEnvironment BerkeleySyntaxSatisfactionAll BerkeleySyntaxZFBase BerkeleySyntaxZFSeparation.
Import ListNotations.

Definition negative_truth_formula := instantiate_formula (fun _=>0) (fst (b_not (b_rel 4 3 2) 5)).
Definition implication_truth_formula := instantiate_formula (fun _=>0) (fst (b_imp (b_rel 5 3 2) (b_rel 5 4 2) 6)).
Definition universal_truth_formula := instantiate_formula (fun _=>0) (fst (all_rhs_builder 2 7 3 4 5 6 8 9)).
Lemma negative_truth_output_fresh : fol_free 1 negative_truth_formula=false.
Proof. vm_compute. reflexivity. Qed.
Lemma implication_truth_output_fresh : fol_free 1 implication_truth_formula=false.
Proof. vm_compute. reflexivity. Qed.
Lemma universal_truth_output_fresh : fol_free 1 universal_truth_formula=false.
Proof. vm_compute. reflexivity. Qed.

Section TruthSlices.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Lemma negative_truth_formula_holds rho : FolHolds R rho negative_truth_formula <->
  ~RelGraph R (rho 4) (rho 3) (rho 2).
Proof.
  change (b_holds R rho (b_not (b_rel 4 3 2)) 5 <-> ~RelGraph R (rho 4) (rho 3) (rho 2)).
  rewrite b_holds_not,(relation_builder_holds EM) by lia. reflexivity.
Qed.
Lemma implication_truth_formula_holds rho : FolHolds R rho implication_truth_formula <->
  (RelGraph R (rho 5) (rho 3) (rho 2) -> RelGraph R (rho 5) (rho 4) (rho 2)).
Proof.
  change (b_holds R rho (b_imp (b_rel 5 3 2) (b_rel 5 4 2)) 6 <->
    (RelGraph R (rho 5) (rho 3) (rho 2) -> RelGraph R (rho 5) (rho 4) (rho 2))).
  rewrite b_holds_imp. assert (K : 6 <= b_next (b_rel 5 3 2) 6) by apply b_good_rel.
  rewrite !(relation_builder_holds EM) by lia. reflexivity.
Qed.
Lemma universal_truth_formula_holds rho : FolHolds R rho universal_truth_formula <->
  forall t, R t (rho 3) -> RelUpdate R (rho 2) t (rho 6) (rho 4) (rho 5) -> RelGraph R (rho 7) (rho 8) t.
Proof.
  change (b_holds R rho (all_rhs_builder 2 7 3 4 5 6 8) 9 <->
    forall t, R t (rho 3) -> RelUpdate R (rho 2) t (rho 6) (rho 4) (rho 5) -> RelGraph R (rho 7) (rho 8) t).
  rewrite (all_rhs_builder_holds EM) by lia. reflexivity.
Qed.

Theorem zf_negative_truth_slice e h q : exists slice, forall s,
  R s slice <-> R s e /\ ~RelGraph R h q s.
Proof.
  set (rho := update_variable (update_variable (fun _ : nat => e) 3 q) 4 h).
  destruct (zf_prefix_formula_separation R EM Model negative_truth_formula rho negative_truth_output_fresh) as [slice H].
  exists slice. intro s. specialize (H s). rewrite negative_truth_formula_holds in H. unfold rho in H.
  cbv [update_variable Nat.eqb] in H. exact H.
Qed.
Theorem zf_implication_truth_slice e h q r : exists slice, forall s,
  R s slice <-> R s e /\ (RelGraph R h q s -> RelGraph R h r s).
Proof.
  set (rho := update_variable (update_variable (update_variable (fun _ : nat => e) 3 q) 4 r) 5 h).
  destruct (zf_prefix_formula_separation R EM Model implication_truth_formula rho implication_truth_output_fresh) as [slice H].
  exists slice. intro s. specialize (H s). rewrite implication_truth_formula_holds in H. unfold rho in H.
  cbv [update_variable Nat.eqb] in H. exact H.
Qed.
Theorem zf_universal_truth_slice e h w m u q : exists slice, forall s,
  R s slice <-> R s e /\ forall t, R t e -> RelUpdate R s t u w m -> RelGraph R h q t.
Proof.
  set (rho := update_variable (update_variable (update_variable (update_variable (update_variable
    (update_variable (fun _ : nat => e) 3 e) 4 w) 5 m) 6 u) 7 h) 8 q).
  destruct (zf_prefix_formula_separation R EM Model universal_truth_formula rho universal_truth_output_fresh) as [slice H].
  exists slice. intro s. specialize (H s). rewrite universal_truth_formula_holds in H. unfold rho in H.
  cbv [update_variable Nat.eqb] in H. exact H.
Qed.
End TruthSlices.

Print Assumptions zf_negative_truth_slice.
Print Assumptions zf_implication_truth_slice.
Print Assumptions zf_universal_truth_slice.
