(** A genuine proof fragment of the presented calculus, generated solely by
    the fourteen checked logical schemata, modus ponens, and generalization.
    The standard-FOL completeness and distinctor-elimination bridge is not
    assumed here. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import Syntax TheorySchemas ProofFormula ProofPresentation.
Import ListNotations.

Inductive LogicalProvable : fol_formula -> Prop :=
| logical_axiom i f vars holes : nth_error logical_schemas i=Some f ->
    LogicalProvable (independent_instance vars holes f)
| logical_mp p q : LogicalProvable (FImp p q) -> LogicalProvable p -> LogicalProvable q
| logical_gen x p : LogicalProvable p -> LogicalProvable (FAll x p).

Theorem logical_embeds_in_presented f : LogicalProvable f -> PresentedProvable f.
Proof.
  intro H. induction H.
  - eapply presented_axiom with (i:=i) (f:=f) (vars:=vars) (holes:=holes).
    now apply candidate_logical_index.
  - eapply presented_mp; eassumption.
  - now apply presented_gen.
Qed.

Fixpoint rename_formula (rho : nat->nat) f :=
  match f with
  | FEqual x y => FEqual (rho x) (rho y)
  | FMember x y => FMember (rho x) (rho y)
  | FNeg p => FNeg (rename_formula rho p)
  | FImp p q => FImp (rename_formula rho p) (rename_formula rho q)
  | FAll x p => FAll (rho x) (rename_formula rho p)
  end.
Definition parameter_var x := match x with V _ => false | P _ => true end.
Fixpoint parameter_variables_only f :=
  match f with
  | Atom _ x y => parameter_var x && parameter_var y
  | Neg p => parameter_variables_only p
  | Imp p q => parameter_variables_only p && parameter_variables_only q
  | All x p => parameter_var x && parameter_variables_only p
  | Hole _ => true
  end.
Lemma logical_parameters_only : forallb parameter_variables_only logical_schemas=true.
Proof. vm_compute. reflexivity. Qed.
Lemma rename_independent_variable rho vars x : parameter_var x=true ->
  rho (independent_variable vars x) = independent_variable (fun n => rho(vars n)) x.
Proof. destruct x; cbn [parameter_var independent_variable]; [discriminate|reflexivity]. Qed.
Lemma rename_independent_instance rho vars holes f : parameter_variables_only f=true ->
  rename_formula rho (independent_instance vars holes f) =
  independent_instance (fun n => rho(vars n)) (fun n => rename_formula rho (holes n)) f.
Proof.
  induction f as [b x y|p IH|p IH q JH|x p IH|n]; cbn [parameter_variables_only]; intro H.
  - apply andb_true_iff in H as [X Y]. destruct b; cbn [rename_formula independent_instance];
      rewrite ?(rename_independent_variable rho vars x X), ?(rename_independent_variable rho vars y Y); reflexivity.
  - cbn [rename_formula independent_instance]. f_equal. now apply IH.
  - apply andb_true_iff in H as [P Q]. cbn [rename_formula independent_instance].
    f_equal; [now apply IH|now apply JH].
  - apply andb_true_iff in H as [X P]. cbn [rename_formula independent_instance].
    rewrite (rename_independent_variable rho vars x X). f_equal. now apply IH.
  - reflexivity.
Qed.
Theorem logical_uniform_renaming rho f : LogicalProvable f -> LogicalProvable (rename_formula rho f).
Proof.
  intro P. induction P as [i f vars holes A|p q Major IHm Minor IHn|x p P IH].
  - pose proof (proj1 (forallb_forall _ _) logical_parameters_only f (nth_error_In _ _ A)) as M.
    rewrite (rename_independent_instance rho vars holes f M). eapply logical_axiom; exact A.
  - cbn [rename_formula]. eapply logical_mp; eassumption.
  - cbn [rename_formula]. now apply logical_gen.
Qed.
Print Assumptions logical_embeds_in_presented.
Print Assumptions logical_uniform_renaming.

Definition logic_holes (p q r : fol_formula) n :=
  match n with 1 => p | 2 => q | 3 => r | _ => p end.
Definition logic_vars (x y z : nat) n :=
  match n with 1 => x | 2 => y | 3 => z | _ => x end.

Lemma logical_b1 p q : LogicalProvable (FImp p (FImp q p)).
Proof.
  change (LogicalProvable (independent_instance (logic_vars 0 0 0) (logic_holes p q p)
    (nth 0 logical_schemas (Hole 0)))).
  eapply logical_axiom with (i:=0). reflexivity.
Qed.
Lemma logical_b2 p q r : LogicalProvable
  (FImp (FImp p (FImp q r)) (FImp (FImp p q) (FImp p r))).
Proof.
  change (LogicalProvable (independent_instance (logic_vars 0 0 0) (logic_holes p q r)
    (nth 1 logical_schemas (Hole 0)))).
  eapply logical_axiom with (i:=1). reflexivity.
Qed.
Lemma logical_b3 p q : LogicalProvable
  (FImp (FImp (FNeg p) (FNeg q)) (FImp q p)).
Proof.
  change (LogicalProvable (independent_instance (logic_vars 0 0 0) (logic_holes p q p)
    (nth 2 logical_schemas (Hole 0)))).
  eapply logical_axiom with (i:=2). reflexivity.
Qed.
Lemma logical_b4 x p q : LogicalProvable
  (FImp (FAll x (FImp (FAll x p) q)) (FImp (FAll x p) (FAll x q))).
Proof.
  change (LogicalProvable (independent_instance (logic_vars x 0 0) (logic_holes p p q)
    (nth 3 logical_schemas (Hole 0)))).
  eapply logical_axiom with (i:=3). reflexivity.
Qed.
Lemma logical_b5 x p : LogicalProvable (FImp (FAll x p) p).
Proof.
  change (LogicalProvable (independent_instance (logic_vars x 0 0) (logic_holes p p p)
    (nth 4 logical_schemas (Hole 0)))).
  eapply logical_axiom with (i:=4). reflexivity.
Qed.
Lemma logical_b6 x y p : LogicalProvable (FImp (FAll x (FAll y p)) (FAll y (FAll x p))).
Proof.
  change (LogicalProvable (independent_instance (logic_vars x y 0) (logic_holes p p p)
    (nth 5 logical_schemas (Hole 0)))).
  eapply logical_axiom with (i:=5). reflexivity.
Qed.
Lemma logical_b7 x p : LogicalProvable (FImp (FNeg p) (FAll x (FNeg (FAll x p)))).
Proof.
  change (LogicalProvable (independent_instance (logic_vars x 0 0) (logic_holes p p p)
    (nth 6 logical_schemas (Hole 0)))).
  eapply logical_axiom with (i:=6). reflexivity.
Qed.

Theorem logical_identity p : LogicalProvable (FImp p p).
Proof.
  eapply logical_mp.
  - eapply logical_mp.
    + apply (logical_b2 p (FImp p p) p).
    + apply logical_b1.
  - apply logical_b1.
Qed.
Print Assumptions logical_identity.

(** Propositional consequence rules, proved from the three displayed schemas. *)
Lemma logical_weakening p q : LogicalProvable p -> LogicalProvable (FImp q p).
Proof.
  intro H. eapply logical_mp; [apply logical_b1|exact H].
Qed.
Lemma logical_under_mp a p q :
  LogicalProvable (FImp a (FImp p q)) ->
  LogicalProvable (FImp a p) -> LogicalProvable (FImp a q).
Proof.
  intros H K. eapply logical_mp; [eapply logical_mp; [apply logical_b2|exact H]|exact K].
Qed.
Lemma logical_syllogism p q r : LogicalProvable (FImp p q) ->
  LogicalProvable (FImp q r) -> LogicalProvable (FImp p r).
Proof.
  intros H K. eapply (logical_under_mp p q r); [apply logical_weakening; exact K|exact H].
Qed.
Lemma logical_swap p q r : LogicalProvable (FImp p (FImp q r)) ->
  LogicalProvable (FImp q (FImp p r)).
Proof.
  intro H.
  eapply (logical_under_mp q (FImp p q) (FImp p r)).
  - eapply (logical_syllogism q (FImp p (FImp q r)) (FImp (FImp p q) (FImp p r))).
    + apply logical_weakening; exact H.
    + apply logical_b2.
  - apply logical_b1.
Qed.
Theorem logical_explosion p q : LogicalProvable (FImp p (FImp (FNeg p) q)).
Proof.
  apply logical_swap. eapply (logical_syllogism (FNeg p) (FImp (FNeg q) (FNeg p)) (FImp p q)).
  - apply logical_b1.
  - apply logical_b3.
Qed.
Corollary presented_explosion p q : PresentedProvable (FImp p (FImp (FNeg p) q)).
Proof. apply logical_embeds_in_presented, logical_explosion. Qed.

(** These are theorem-level admissible rules. Generalization here applies to a
    theorem, not to a derivation with undischarged assumptions. *)
Theorem logical_all_consequence x p q :
  LogicalProvable (FImp (FAll x p) q) ->
  LogicalProvable (FImp (FAll x p) (FAll x q)).
Proof.
  intro H. eapply logical_mp; [apply logical_b4|now apply logical_gen].
Qed.
Theorem logical_all_monotone x p q : LogicalProvable (FImp p q) ->
  LogicalProvable (FImp (FAll x p) (FAll x q)).
Proof.
  intro H. apply logical_all_consequence. eapply (logical_syllogism (FAll x p) p q).
  - apply logical_b5.
  - exact H.
Qed.
Theorem logical_all_idempotent x p :
  LogicalProvable (FImp (FAll x p) (FAll x (FAll x p))) /\
  LogicalProvable (FImp (FAll x (FAll x p)) (FAll x p)).
Proof.
  split.
  - apply logical_all_consequence, logical_identity.
  - apply logical_b5.
Qed.
Theorem logical_all_distribution x p q :
  LogicalProvable (FImp (FAll x (FImp p q))
    (FImp (FAll x p) (FAll x q))).
Proof.
  set (a := FAll x (FImp p q)).
  set (b := FAll x p).
  assert (H0 : LogicalProvable (FImp a (FImp p q))) by (unfold a; apply logical_b5).
  assert (H1 : LogicalProvable (FImp b p)) by (unfold b; apply logical_b5).
  assert (H2 : LogicalProvable (FImp a (FImp b (FImp p q)))).
  { eapply (logical_syllogism a (FImp p q) (FImp b (FImp p q))); [exact H0|apply logical_b1]. }
  assert (H3 : LogicalProvable (FImp a (FImp (FImp b p) (FImp b q)))).
  { eapply (logical_syllogism a (FImp b (FImp p q)) (FImp (FImp b p) (FImp b q))); [exact H2|apply logical_b2]. }
  assert (H4 : LogicalProvable (FImp a (FImp b p))) by (now apply logical_weakening).
  assert (H5 : LogicalProvable (FImp a (FImp b q))).
  { eapply (logical_under_mp a (FImp b p) (FImp b q)); eassumption. }
  assert (H6 : LogicalProvable (FAll x (FImp a (FImp b q)))) by (now apply logical_gen).
  assert (H7 : LogicalProvable (FImp a (FAll x (FImp b q)))).
  { eapply logical_mp; [unfold a; apply logical_b4|exact H6]. }
  eapply (logical_syllogism a (FAll x (FImp b q)) (FImp b (FAll x q))); [exact H7|unfold b; apply logical_b4].
Qed.
Print Assumptions logical_explosion.
Print Assumptions presented_explosion.
Print Assumptions logical_all_consequence.
Print Assumptions logical_all_monotone.
Print Assumptions logical_all_idempotent.
Print Assumptions logical_all_distribution.
