(** A separate, explicitly augmented calculus. This is NOT the presentation
    executed by the original 1,385-state machine. The additional axiom is
    admitted only when its two numeric variable names are distinct. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From Berkeley Require Import ProofFormula ProofPresentation FormulaSemantics LogicBridge LogicFresh
  LogicQuantifier LogicGuardedFresh LogicSemantics.
Import ListNotations.
Inductive AugProvable : fol_formula -> Prop :=
| aug_original p : PresentedProvable p -> AugProvable p
| aug_distinctor x y : x<>y -> AugProvable (distinctor x y)
| aug_mp p q : AugProvable (FImp p q) -> AugProvable p -> AugProvable q
| aug_gen x p : AugProvable p -> AugProvable (FAll x p).
Lemma aug_logical p : LogicalProvable p -> AugProvable p.
Proof. intro H. apply aug_original,logical_embeds_in_presented,H. Qed.
Lemma aug_syllogism p q r : AugProvable (FImp p q) -> AugProvable (FImp q r) -> AugProvable (FImp p r).
Proof.
  intros H K. assert (W : AugProvable (FImp p (FImp q r))).
  { eapply aug_mp; [apply aug_logical,logical_b1|exact K]. }
  eapply aug_mp; [eapply aug_mp; [apply aug_logical,logical_b2|exact W]|exact H].
Qed.
Lemma aug_all_monotone x p q : AugProvable (FImp p q) ->
  AugProvable (FImp (FAll x p) (FAll x q)).
Proof. intro H. eapply aug_mp; [apply aug_logical,logical_all_distribution|now apply aug_gen]. Qed.
Lemma aug_guard_elim ds p : (forall d, In d ds -> AugProvable (distinguisher d)) ->
  AugProvable (guard_distinctors ds p) -> AugProvable p.
Proof.
  revert p. induction ds as [|d ds IH]; intros p Guards H; cbn [guard_distinctors] in H.
  - exact H.
  - assert (T : AugProvable (FImp (distinguisher d) p)).
    { apply IH; [intros e E; apply Guards; now right|exact H]. }
    eapply aug_mp; [exact T|apply Guards; now left].
Qed.
Theorem aug_fresh_C5 x p : ~occurs_free x p -> AugProvable (FImp p (FAll x p)).
Proof.
  intro Fresh. eapply aug_guard_elim with (ds:=map (fun v => (x,v)) (fresh_support x p)).
  - intros d D. apply in_map_iff in D as [v [E V]]. subst d. cbn [distinguisher].
    apply (aug_distinctor x v). intro E. subst v. now apply Fresh.
  - apply aug_logical,logical_fresh_with_distinctor_guards.
Qed.
Theorem aug_fresh_generalization x p q : ~occurs_free x p -> AugProvable (FImp p q) ->
  AugProvable (FImp p (FAll x q)).
Proof.
  intros Fresh H. eapply (aug_syllogism p (FAll x p) (FAll x q));
    [now apply aug_fresh_C5|now apply aug_all_monotone].
Qed.
Section Semantics.
Context {D : Type} (R:D->D->Prop).
Variable classic : forall P:Prop, P \/ ~P.
Hypothesis Model : satisfies_nonlogical_schemas R.
Hypothesis Nontrivial : exists a b:D, a<>b.
Lemma distinguisher_valid_nontrivial x y rho : x<>y -> FolHolds R rho (distinctor x y).
Proof.
  intro XY. destruct Nontrivial as [a [b AB]]. cbn [distinctor FolHolds]. intro H.
  destruct (classic (rho y=a)) as [E|E].
  - specialize (H b). rewrite update_variable_eq,update_variable_neq in H by congruence. congruence.
  - specialize (H a). rewrite update_variable_eq,update_variable_neq in H by congruence. congruence.
Qed.
Theorem augmented_sound p : AugProvable p -> forall rho, FolHolds R rho p.
Proof.
  intro H. induction H as [p H|x y H|p q A IHA B IHB|x p H IH]; intro rho.
  - eapply presented_sound; eassumption.
  - now apply distinguisher_valid_nontrivial.
  - apply (IHA rho), IHB.
  - cbn [FolHolds]. intro a. apply IH.
Qed.
End Semantics.
Print Assumptions aug_fresh_C5.
Print Assumptions aug_fresh_generalization.
Print Assumptions augmented_sound.
