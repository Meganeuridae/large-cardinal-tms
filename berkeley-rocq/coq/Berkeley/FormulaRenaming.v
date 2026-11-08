(** Semantics and free-variable support under an injective renaming. *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
From Berkeley Require Import ProofFormula FormulaSemantics LogicBridge TheoryIrreflexiveND.
Import ListNotations.
Lemma eqb_injective rho x y : (forall a b, rho a=rho b -> a=b) ->
  Nat.eqb (rho x) (rho y)=Nat.eqb x y.
Proof.
  intro Inj. destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst. now rewrite Nat.eqb_refl.
  - apply Nat.eqb_neq in E. apply Nat.eqb_neq. intro Eq. apply E,Inj,Eq.
Qed.
Theorem FolHolds_rename {D:Type} (R:D->D->Prop) rho f pi :
  (forall a b, pi a=pi b -> a=b) ->
  (FolHolds R rho (rename_formula pi f) <-> FolHolds R (fun n=>rho (pi n)) f).
Proof.
  intro Inj. revert rho. induction f as [x y|x y|p IH|p IH q JH|x p IH]; intro rho;
    cbn [rename_formula FolHolds].
  - tauto.
  - tauto.
  - rewrite IH. tauto.
  - rewrite IH,JH. tauto.
  - split; intros H a.
    + specialize (H a). apply IH in H.
      assert (E : forall n, update_variable rho (pi x) a (pi n) = update_variable (fun k=>rho (pi k)) x a n).
      { intro n. unfold update_variable. now rewrite (eqb_injective pi n x Inj). }
      apply (proj1 (FolHolds_ext R p _ _ E)). exact H.
    + specialize (H a). apply IH.
      assert (E : forall n, update_variable rho (pi x) a (pi n) = update_variable (fun k=>rho (pi k)) x a n).
      { intro n. unfold update_variable. now rewrite (eqb_injective pi n x Inj). }
      apply (proj2 (FolHolds_ext R p _ _ E)). exact H.
Qed.
Lemma nd_free_rename pi x p : (forall a b, pi a=pi b -> a=b) ->
  nd_free (pi x) (rename_formula pi p)=nd_free x p.
Proof.
  intro Inj. induction p as [a b|a b|p IH|p IH q JH|z p IH]; cbn [nd_free rename_formula].
  - now rewrite !(eqb_injective pi _ _ Inj).
  - now rewrite !(eqb_injective pi _ _ Inj).
  - exact IH.
  - now rewrite IH,JH.
  - now rewrite (eqb_injective pi _ _ Inj),IH.
Qed.
Lemma rename_composition pi sigma p :
  rename_formula pi (rename_formula sigma p) = rename_formula (fun n=>pi(sigma n)) p.
Proof. induction p; cbn [rename_formula]; congruence. Qed.
Lemma rename_ext pi sigma p : (forall n, pi n=sigma n) -> rename_formula pi p=rename_formula sigma p.
Proof. intro E. induction p; cbn [rename_formula]; f_equal; auto. Qed.
Lemma rename_identity p : rename_formula (fun n=>n) p=p.
Proof. induction p; cbn [rename_formula]; congruence. Qed.
Lemma rename_inverse pi sigma p : (forall n, pi(sigma n)=n) ->
  rename_formula pi (rename_formula sigma p)=p.
Proof. intro Inv. rewrite rename_composition. erewrite rename_ext; [apply rename_identity|exact Inv]. Qed.
Print Assumptions FolHolds_rename.
Print Assumptions nd_free_rename.
Print Assumptions rename_inverse.
