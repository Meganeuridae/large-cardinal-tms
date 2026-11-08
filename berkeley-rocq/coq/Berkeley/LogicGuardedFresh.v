(** A noncircular fresh-variable theorem: all required distinctors remain
    object-language antecedents. Generalization under these assumptions is
    sound because their stability was proved from the fourteen schemas. *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
From Berkeley Require Import ProofFormula ProofPresentation LogicBridge LogicQuantifier LogicFresh.
Import ListNotations.
Definition distinguisher (d : nat*nat) := distinctor (fst d) (snd d).
Inductive DistContext (ds : list (nat*nat)) : fol_formula -> Prop :=
| dist_hyp d : In d ds -> DistContext ds (distinguisher d)
| dist_theorem p : LogicalProvable p -> DistContext ds p
| dist_mp p q : DistContext ds (FImp p q) -> DistContext ds p -> DistContext ds q
| dist_gen x p : DistContext ds p -> DistContext ds (FAll x p).
Lemma dist_syllogism ds p q r : DistContext ds (FImp p q) ->
  DistContext ds (FImp q r) -> DistContext ds (FImp p r).
Proof.
  intros H K. assert (W : DistContext ds (FImp p (FImp q r))).
  { eapply dist_mp; [apply dist_theorem,logical_b1|exact K]. }
  eapply dist_mp; [eapply dist_mp; [apply dist_theorem,logical_b2|exact W]|exact H].
Qed.
Lemma dist_deduction d ds p : DistContext (d::ds) p -> DistContext ds (FImp (distinguisher d) p).
Proof.
  intro H. remember (d::ds) as ctx eqn:E.
  induction H as [a Member|f Global|a b Major IHm Minor IHn|z f A IH]; subst ctx.
  - cbn in Member. destruct Member as [Eq|Member].
    + subst a. apply dist_theorem,logical_identity.
    + eapply dist_mp; [apply dist_theorem,logical_b1|now apply dist_hyp].
  - eapply dist_mp; [apply dist_theorem,logical_b1|now apply dist_theorem].
  - eapply dist_mp; [eapply dist_mp; [apply dist_theorem,logical_b2|apply IHm;reflexivity]|apply IHn;reflexivity].
  - eapply (dist_syllogism ds (distinguisher d) (FAll z (distinguisher d)) (FAll z f)).
    + destruct d as [u v]. apply dist_theorem,logical_distinctor_stable.
    + eapply dist_mp; [apply dist_theorem,logical_all_distribution|apply dist_gen,IH;reflexivity].
Qed.
Lemma dist_finish p : DistContext [] p -> LogicalProvable p.
Proof. intro H. induction H; [contradiction|assumption|eapply logical_mp;eassumption|now apply logical_gen]. Qed.
Fixpoint guard_distinctors ds p :=
  match ds with [] => p | d::rest => guard_distinctors rest (FImp (distinguisher d) p) end.
Lemma dist_discharge ds p : DistContext ds p -> LogicalProvable (guard_distinctors ds p).
Proof.
  revert p. induction ds as [|d ds IH]; intros p H; cbn [guard_distinctors].
  - now apply dist_finish.
  - apply IH,dist_deduction,H.
Qed.
Theorem dist_fresh ds x p :
  (forall v, In v (fresh_support x p) -> In (x,v) ds) ->
  DistContext ds (FImp p (FAll x p)).
Proof.
  induction p as [y z|y z|p IH|p IH q JH|y p IH]; intro H.
  - eapply dist_mp.
    + eapply dist_mp.
      * apply dist_theorem,logical_b9.
      * change (DistContext ds (distinguisher (x,y))). apply dist_hyp,H. cbn. auto.
    + change (DistContext ds (distinguisher (x,z))). apply dist_hyp,H. cbn. auto.
  - eapply dist_mp.
    + eapply dist_mp.
      * apply dist_theorem,logical_b14.
      * change (DistContext ds (distinguisher (x,y))). apply dist_hyp,H. cbn. auto.
    + change (DistContext ds (distinguisher (x,z))). apply dist_hyp,H. cbn. auto.
  - eapply dist_mp.
    + apply dist_theorem,logical_fresh_negation.
    + apply dist_gen,IH. exact H.
  - assert (HP : DistContext ds (FImp p (FAll x p))).
    { apply IH. intros v V. apply H. cbn. apply in_or_app. now left. }
    assert (HQ : DistContext ds (FImp q (FAll x q))).
    { apply JH. intros v V. apply H. cbn. apply in_or_app. now right. }
    eapply dist_mp.
    + eapply dist_mp.
      * apply dist_theorem,logical_fresh_implication.
      * now apply dist_gen.
    + exact HQ.
  - destruct (Nat.eq_dec x y) as [E|E].
    + subst y. apply dist_theorem. apply (proj1 (logical_all_idempotent x p)).
    + assert (HP : DistContext ds (FImp p (FAll x p))).
      { apply IH. intros v V. apply H. cbn. apply Nat.eqb_neq in E. now rewrite E. }
      eapply dist_mp.
      * apply dist_theorem,logical_fresh_quantifier.
      * now apply dist_gen.
Qed.
Theorem logical_fresh_with_distinctor_guards x p :
  LogicalProvable (guard_distinctors (map (fun v => (x,v)) (fresh_support x p))
    (FImp p (FAll x p))).
Proof.
  apply dist_discharge,dist_fresh. intros v V. apply in_map. exact V.
Qed.
Corollary presented_fresh_with_distinctor_guards x p :
  PresentedProvable (guard_distinctors (map (fun v => (x,v)) (fresh_support x p))
    (FImp p (FAll x p))).
Proof. apply logical_embeds_in_presented,logical_fresh_with_distinctor_guards. Qed.
Print Assumptions dist_deduction.
Print Assumptions logical_fresh_with_distinctor_guards.
Print Assumptions presented_fresh_with_distinctor_guards.
