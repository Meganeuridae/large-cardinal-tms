(** The logical fragment of the guarded-D calculus is stable under every
    injective renaming; fixed nonlogical axiom names are not assumed stable. *)
From Stdlib Require Import Lists.List.
From Berkeley Require Import ProofFormula ProofPresentation LogicBridge LogicFresh LogicQuantifier LogicGuardedFresh AugmentedLogic.
Import ListNotations.
Definition RenameStable p := forall pi, (forall x y, pi x=pi y -> x=y) -> AugProvable (rename_formula pi p).
Lemma stable_logical p : LogicalProvable p -> RenameStable p.
Proof. intros H pi Inj. apply aug_logical,logical_uniform_renaming,H. Qed.
Lemma stable_distinctor x y : x<>y -> RenameStable (distinctor x y).
Proof.
  intros H pi Inj. cbn [distinctor rename_formula]. apply aug_distinctor. intro E. apply H,Inj,E.
Qed.
Lemma stable_mp p q : RenameStable (FImp p q) -> RenameStable p -> RenameStable q.
Proof. intros A B pi Inj. eapply aug_mp; [apply (A pi Inj)|apply (B pi Inj)]. Qed.
Lemma stable_gen x p : RenameStable p -> RenameStable (FAll x p).
Proof. intros H pi Inj. cbn [rename_formula]. now apply aug_gen,H. Qed.
Lemma stable_syllogism p q r : RenameStable (FImp p q) -> RenameStable (FImp q r) -> RenameStable (FImp p r).
Proof.
  intros H K. assert (W : RenameStable (FImp p (FImp q r))).
  { eapply stable_mp; [apply stable_logical,logical_b1|exact K]. }
  eapply stable_mp; [eapply stable_mp; [apply stable_logical,logical_b2|exact W]|exact H].
Qed.
Lemma stable_all_monotone x p q : RenameStable (FImp p q) ->
  RenameStable (FImp (FAll x p) (FAll x q)).
Proof. intro H. eapply stable_mp; [apply stable_logical,logical_all_distribution|now apply stable_gen]. Qed.
Lemma stable_guard_elim ds p : (forall d, In d ds -> RenameStable (distinguisher d)) ->
  RenameStable (guard_distinctors ds p) -> RenameStable p.
Proof.
  revert p. induction ds as [|d ds IH]; intros p Guards H; cbn [guard_distinctors] in H.
  - exact H.
  - assert (T : RenameStable (FImp (distinguisher d) p)).
    { apply IH; [intros e E; apply Guards; now right|exact H]. }
    eapply stable_mp; [exact T|apply Guards; now left].
Qed.
Theorem stable_fresh_C5 x p : ~occurs_free x p -> RenameStable (FImp p (FAll x p)).
Proof.
  intro Fresh. eapply stable_guard_elim with (ds:=map (fun v => (x,v)) (fresh_support x p)).
  - intros d D. apply in_map_iff in D as [v [E V]]. subst d. cbn [distinguisher].
    apply (stable_distinctor x v). intro E. subst v. now apply Fresh.
  - apply stable_logical,logical_fresh_with_distinctor_guards.
Qed.
Theorem stable_fresh_generalization x p q : ~occurs_free x p -> RenameStable (FImp p q) ->
  RenameStable (FImp p (FAll x q)).
Proof.
  intros Fresh H. eapply (stable_syllogism p (FAll x p) (FAll x q));
    [now apply stable_fresh_C5|now apply stable_all_monotone].
Qed.

Print Assumptions stable_fresh_C5.
