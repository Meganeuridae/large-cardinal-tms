(** The literal protected-output separation schema implies separation for
    first-order formulas whose output variable is not free. This is a schema
    over syntax, not a higher-order separation assumption. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import Syntax SyntaxData ProofFormula ProofPresentation FormulaSemantics BerkeleySyntaxZFBase.
Import ListNotations.

Fixpoint fol_free x p :=
  match p with
  | FEqual y z | FMember y z => Nat.eqb x y || Nat.eqb x z
  | FNeg q => fol_free x q
  | FImp q r => fol_free x q || fol_free x r
  | FAll y q => if Nat.eqb x y then false else fol_free x q
  end.
Definition f_and p q := FNeg (FImp p (FNeg q)).
Definition f_iff p q := f_and (FImp p q) (FImp q p).
Definition f_ex x p := FNeg (FAll x (FNeg p)).

Lemma FolHolds_agree_free {D} (R:D->D->Prop) p rho sigma :
  (forall n, fol_free n p=true -> rho n=sigma n) ->
  (FolHolds R rho p <-> FolHolds R sigma p).
Proof.
  revert rho sigma. induction p as [x y|x y|p IH|p IH q JH|x p IH]; intros rho sigma E; cbn [FolHolds].
  - assert (X : rho x=sigma x) by (apply E; cbn [fol_free]; now rewrite Nat.eqb_refl).
    assert (Y : rho y=sigma y) by (apply E; cbn [fol_free]; now rewrite Nat.eqb_refl,orb_true_r).
    now rewrite X,Y.
  - assert (X : rho x=sigma x) by (apply E; cbn [fol_free]; now rewrite Nat.eqb_refl).
    assert (Y : rho y=sigma y) by (apply E; cbn [fol_free]; now rewrite Nat.eqb_refl,orb_true_r).
    now rewrite X,Y.
  - rewrite IH by exact E. reflexivity.
  - rewrite IH,JH by (intros n N; apply E; cbn [fol_free]; apply orb_true_iff; auto). reflexivity.
  - assert (Agree : forall a n, fol_free n p=true ->
      update_variable rho x a n=update_variable sigma x a n).
    { intros a n N. unfold update_variable. destruct (Nat.eqb n x) eqn:Eq; [reflexivity|].
      apply E. cbn [fol_free]. now rewrite Eq. }
    split; intros H a.
    + apply (proj1 (IH _ _ (Agree a))),H.
    + apply (proj2 (IH _ _ (Agree a))),H.
Qed.

Lemma holds_f_and {D} (R:D->D->Prop) (EM:forall P:Prop,P\/ ~P) rho p q :
  FolHolds R rho (f_and p q) <-> FolHolds R rho p /\ FolHolds R rho q.
Proof.
  cbn [f_and FolHolds]. destruct (EM (FolHolds R rho p)),(EM (FolHolds R rho q)); tauto.
Qed.
Lemma holds_f_iff {D} (R:D->D->Prop) (EM:forall P:Prop,P\/ ~P) rho p q :
  FolHolds R rho (f_iff p q) <-> (FolHolds R rho p <-> FolHolds R rho q).
Proof. unfold f_iff. rewrite (holds_f_and R EM). cbn [FolHolds]. tauto. Qed.
Lemma holds_f_ex {D} (R:D->D->Prop) (EM:forall P:Prop,P\/ ~P) rho x p :
  FolHolds R rho (f_ex x p) <-> exists a, FolHolds R (update_variable rho x a) p.
Proof.
  cbn [f_ex FolHolds]. split.
  - intro H. destruct (EM (exists a, FolHolds R (update_variable rho x a) p)) as [E|E]; [exact E|].
    exfalso. apply H. intros a A. apply E. now exists a.
  - intros [a A] H. exact (H a A).
Qed.

Lemma protected_separation_body {D} (R:D->D->Prop) rho p out z : fol_free 1 p=false ->
  ((forall v, FolHolds R (update_variable (update_variable (update_variable rho 1 out) 2 z) 1 v) p) <->
   FolHolds R (update_variable rho 2 z) p).
Proof.
  intro Fresh. assert (Agree : forall v,
    FolHolds R (update_variable (update_variable (update_variable rho 1 out) 2 z) 1 v) p <->
    FolHolds R (update_variable rho 2 z) p).
  { intro v. apply FolHolds_agree_free. intros n N.
    assert (Ne : n<>1) by (intro Eq; subst; congruence).
    apply Nat.eqb_neq in Ne. unfold update_variable. now rewrite !Ne. }
  split; [intro H; apply (proj1 (Agree z)),H|intros H v; apply (proj2 (Agree v)),H].
Qed.

Section Separation.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Theorem zf_prefix_formula_separation p rho : fol_free 1 p=false -> exists out,
  forall z, R z out <-> R z (rho 0) /\ FolHolds R (update_variable rho 2 z) p.
Proof.
  intro Fresh.
  pose proof (Model 20 (nth 20 candidate_axioms (Hole 0)) (fun n=>n) (fun _=>p) rho
    ltac:(lia) ltac:(reflexivity)) as H.
  change (FolHolds R rho (f_ex 1 (FAll 2 (f_iff (FMember 2 1)
    (f_and (FMember 2 0) (FAll 1 p)))))) in H.
  rewrite (holds_f_ex R EM) in H. destruct H as [out H]. exists out. intro z.
  cbn [FolHolds] in H. specialize (H z).
  rewrite (holds_f_iff R EM),(holds_f_and R EM) in H. cbn [FolHolds] in H.
  change (R z out <-> R z (rho 0) /\
    forall v, FolHolds R (update_variable (update_variable (update_variable rho 1 out) 2 z) 1 v) p) in H.
  now rewrite (protected_separation_body R rho p out z Fresh) in H.
Qed.
End Separation.

Print Assumptions FolHolds_agree_free.
Print Assumptions protected_separation_body.
Print Assumptions zf_prefix_formula_separation.
