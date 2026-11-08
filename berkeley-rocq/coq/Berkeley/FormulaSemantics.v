(** Standard first-order equality/membership semantics. No classical or set
    theory principle is assumed in these definitions and structural lemmas. *)
From Stdlib Require Import Arith.Arith Bool.Bool.
From Berkeley Require Import ProofFormula.

Definition update_variable {D : Type} (rho : nat->D) (x : nat) (a : D) (y : nat) :=
  if Nat.eqb y x then a else rho y.
Fixpoint FolHolds {D : Type} (R : D->D->Prop) (rho : nat->D) (f : fol_formula) : Prop :=
  match f with
  | FEqual x y => rho x=rho y
  | FMember x y => R (rho x) (rho y)
  | FNeg p => ~FolHolds R rho p
  | FImp p q => FolHolds R rho p -> FolHolds R rho q
  | FAll x p => forall a, FolHolds R (update_variable rho x a) p
  end.
Lemma update_variable_eq {D} (rho:nat->D) x a : update_variable rho x a x=a.
Proof. unfold update_variable. now rewrite Nat.eqb_refl. Qed.
Lemma update_variable_neq {D} (rho:nat->D) x y a : y<>x -> update_variable rho x a y=rho y.
Proof. intro H. unfold update_variable. apply Nat.eqb_neq in H. now rewrite H. Qed.
Theorem FolHolds_ext {D} (R:D->D->Prop) f rho sigma :
  (forall n, rho n=sigma n) -> (FolHolds R rho f <-> FolHolds R sigma f).
Proof.
  revert rho sigma. induction f as [x y|x y|p IH|p IH q JH|x p IH]; intros rho sigma E; cbn [FolHolds].
  - now rewrite !E.
  - now rewrite !E.
  - now rewrite (IH rho sigma E).
  - now rewrite (IH rho sigma E),(JH rho sigma E).
  - split; intros H a; specialize (IH (update_variable rho x a) (update_variable sigma x a)).
    + apply (proj1 (IH ltac:(intro n; unfold update_variable; destruct (Nat.eqb n x); auto))). apply H.
    + apply (proj2 (IH ltac:(intro n; unfold update_variable; destruct (Nat.eqb n x); auto))). apply H.
Qed.
Lemma update_variable_same {D} (rho:nat->D) x a b y :
  update_variable (update_variable rho x a) x b y = update_variable rho x b y.
Proof. unfold update_variable. now destruct (Nat.eqb y x). Qed.
Lemma update_variable_restore {D} (rho:nat->D) x y : update_variable rho x (rho x) y=rho y.
Proof. unfold update_variable. destruct (Nat.eqb y x) eqn:E; [apply Nat.eqb_eq in E; now subst|reflexivity]. Qed.
Lemma update_variable_commute {D} (rho:nat->D) x y a b z : x<>y ->
  update_variable (update_variable rho x a) y b z =
  update_variable (update_variable rho y b) x a z.
Proof.
  intro H. unfold update_variable. destruct (Nat.eqb z y) eqn:Y,(Nat.eqb z x) eqn:X;
    try reflexivity. apply Nat.eqb_eq in X,Y. congruence.
Qed.
Print Assumptions FolHolds_ext.
Print Assumptions update_variable_commute.
