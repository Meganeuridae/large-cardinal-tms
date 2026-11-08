(** The literal protected-output replacement schema yields replacement for a
    first-order definable functional relation. No arbitrary-predicate
    replacement principle is assumed. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import Syntax SyntaxData ProofFormula ProofPresentation FormulaSemantics BerkeleySyntaxZFBase BerkeleySyntaxZFSeparation.
Import ListNotations.

Lemma protected_replacement_body {D} (R:D->D->Prop) rho p input out z v : fol_free 1 p=false ->
  (FolHolds R (update_variable (update_variable (update_variable (update_variable rho 3 input) 1 out) 2 z) 1 v) p <->
   FolHolds R (update_variable (update_variable rho 3 input) 2 z) p).
Proof.
  intro Fresh. apply FolHolds_agree_free. intros n N.
  assert (Ne : n<>1) by (intro Eq; subst; congruence). apply Nat.eqb_neq in Ne.
  unfold update_variable. now rewrite !Ne.
Qed.
Lemma protected_replacement_body_conclusion {D} (R:D->D->Prop) rho p input out z v : fol_free 1 p=false ->
  (FolHolds R (update_variable (update_variable (update_variable (update_variable rho 1 out) 2 z) 3 input) 1 v) p <->
   FolHolds R (update_variable (update_variable rho 3 input) 2 z) p).
Proof.
  intro Fresh. apply FolHolds_agree_free. intros n N.
  assert (Ne : n<>1) by (intro Eq; subst; congruence). apply Nat.eqb_neq in Ne.
  unfold update_variable. rewrite !Ne. destruct (Nat.eqb n 2) eqn:E2,(Nat.eqb n 3) eqn:E3; try reflexivity.
  apply Nat.eqb_eq in E2,E3. lia.
Qed.

Section Replacement.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Theorem zf_prefix_formula_replacement p rho : fol_free 1 p=false ->
  (forall input, exists out, forall z,
    FolHolds R (update_variable (update_variable rho 3 input) 2 z) p -> z=out) ->
  exists collection, forall z, R z collection <-> exists input,
    R input (rho 0) /\ FolHolds R (update_variable (update_variable rho 3 input) 2 z) p.
Proof.
  intros Fresh Functional.
  pose proof (Model 21 (nth 21 candidate_axioms (Hole 0)) (fun n=>n) (fun _=>p) rho
    ltac:(lia) ltac:(reflexivity)) as H.
  change (FolHolds R rho (FImp
    (FAll 3 (f_ex 1 (FAll 2 (FImp (FAll 1 p) (FEqual 2 1)))))
    (f_ex 1 (FAll 2 (f_iff (FMember 2 1) (f_ex 3 (f_and (FMember 3 0) (FAll 1 p)))))))) in H.
  cbn [FolHolds] in H.
  assert (Premise : forall input, FolHolds R (update_variable rho 3 input)
    (f_ex 1 (FAll 2 (FImp (FAll 1 p) (FEqual 2 1))))).
  { intro input. destruct (Functional input) as [out Unique]. rewrite (holds_f_ex R EM). exists out.
    cbn [FolHolds]. intros z Protected. apply Unique.
    apply (proj1 (protected_replacement_body R rho p input out z z Fresh)),Protected. }
  specialize (H Premise). rewrite (holds_f_ex R EM) in H. destruct H as [collection H]. exists collection. intro z.
  cbn [FolHolds] in H. specialize (H z). rewrite (holds_f_iff R EM) in H. cbn [FolHolds] in H.
  change (R z collection <-> FolHolds R (update_variable (update_variable rho 1 collection) 2 z)
    (f_ex 3 (f_and (FMember 3 0) (FAll 1 p)))) in H.
  rewrite (holds_f_ex R EM) in H. split.
  - intro Z. destruct (proj1 H Z) as [input In]. rewrite (holds_f_and R EM) in In. cbn [FolHolds] in In.
    change (R input (rho 0) /\ forall v,
      FolHolds R (update_variable (update_variable (update_variable (update_variable rho 1 collection) 2 z) 3 input) 1 v) p) in In.
    exists input. split; [exact (proj1 In)|].
    apply (proj1 (protected_replacement_body_conclusion R rho p input collection z z Fresh)),(proj2 In).
  - intros [input [In P]]. apply (proj2 H). exists input. rewrite (holds_f_and R EM). cbn [FolHolds].
    change (R input (rho 0) /\ forall v,
      FolHolds R (update_variable (update_variable (update_variable (update_variable rho 1 collection) 2 z) 3 input) 1 v) p).
    split; [exact In|]. intro v. apply (proj2 (protected_replacement_body_conclusion R rho p input collection z v Fresh)),P.
Qed.
End Replacement.

Print Assumptions protected_replacement_body.
Print Assumptions protected_replacement_body_conclusion.
Print Assumptions zf_prefix_formula_replacement.
