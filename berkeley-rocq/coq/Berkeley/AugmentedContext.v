(** Contextual deduction and propositional rules for the separately augmented
    calculus. This is not the original machine presentation. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import ProofFormula ProofPresentation LogicBridge TheoryIrreflexiveND AugmentedLogic.
Import ListNotations.

Inductive AugContext (ctx : list fol_formula) : fol_formula -> Prop :=
| ac_hyp p : In p ctx -> AugContext ctx p
| ac_theorem p : AugProvable p -> AugContext ctx p
| ac_mp p q : AugContext ctx (FImp p q) -> AugContext ctx p -> AugContext ctx q.

Lemma ac_weaken Γ Δ p : (forall q, In q Γ -> In q Δ) -> AugContext Γ p -> AugContext Δ p.
Proof. intros Inc H. induction H; [apply ac_hyp,Inc;assumption|apply ac_theorem;assumption|eapply ac_mp; eassumption]. Qed.

Lemma ac_logical Γ p : LogicalProvable p -> AugContext Γ p.
Proof. intro H. apply ac_theorem,aug_logical,H. Qed.

Theorem ac_deduction Γ p q : AugContext (p::Γ) q -> AugContext Γ (FImp p q).
Proof.
  intro H. remember (p::Γ) as ctx eqn:E. induction H as [f Member|f Global|a b Major IHm Minor IHn]; subst ctx.
  - cbn in Member. destruct Member as [Eq|Member].
    + subst f. apply ac_logical,logical_identity.
    + eapply ac_mp; [apply ac_logical,logical_b1|now apply ac_hyp].
  - eapply ac_mp; [apply ac_logical,logical_b1|now apply ac_theorem].
  - eapply ac_mp; [eapply ac_mp; [apply ac_logical,logical_b2|apply IHm; reflexivity]|apply IHn; reflexivity].
Qed.

Lemma ac_finish p : AugContext [] p -> AugProvable p.
Proof. intro H. induction H; [contradiction|assumption|eapply aug_mp; eassumption]. Qed.

Lemma ac_true Γ : AugContext Γ nd_true.
Proof. unfold nd_true. apply ac_logical,logical_identity. Qed.
Lemma ac_explosion Γ p q : AugContext Γ p -> AugContext Γ (FNeg p) -> AugContext Γ q.
Proof.
  intros A B. eapply ac_mp; [eapply ac_mp; [apply ac_logical,logical_explosion|exact A]|exact B].
Qed.
Lemma ac_classical Γ p : AugContext (FNeg p::Γ) nd_false -> AugContext Γ p.
Proof.
  intro H. apply ac_deduction in H. unfold nd_false in H.
  eapply ac_mp; [eapply ac_mp; [apply ac_logical,logical_b3|exact H]|apply ac_true].
Qed.
Lemma ac_double_neg_elim Γ p : AugContext Γ (FNeg (FNeg p)) -> AugContext Γ p.
Proof.
  intro H. apply ac_classical.
  eapply ac_explosion with (p:=FNeg p).
  - apply ac_hyp. now left.
  - eapply ac_weaken; [|exact H]. intros q Q. now right.
Qed.
Lemma ac_neg_intro Γ p : AugContext (p::Γ) nd_false -> AugContext Γ (FNeg p).
Proof.
  intro H. apply ac_deduction in H. apply ac_classical.
  eapply ac_mp.
  - eapply ac_weaken; [|exact H]. intros q Q. now right.
  - apply ac_double_neg_elim. apply ac_hyp. now left.
Qed.
Lemma ac_double_neg_intro Γ p : AugContext Γ p -> AugContext Γ (FNeg (FNeg p)).
Proof.
  intro H. apply ac_neg_intro. eapply ac_explosion with (p:=p).
  - eapply ac_weaken; [|exact H]. intros q Q. now right.
  - apply ac_hyp. now left.
Qed.

Lemma ac_and_intro Γ p q : AugContext Γ p -> AugContext Γ q -> AugContext Γ (nd_and p q).
Proof.
  intros P Q. unfold nd_and. apply ac_neg_intro.
  assert (P' : AugContext (FImp p (FNeg q)::Γ) p) by (eapply ac_weaken; [|exact P]; intros x X; now right).
  assert (Q' : AugContext (FImp p (FNeg q)::Γ) q) by (eapply ac_weaken; [|exact Q]; intros x X; now right).
  eapply ac_explosion with (p:=q); [exact Q'|].
  eapply ac_mp; [apply ac_hyp; now left|exact P'].
Qed.
Lemma ac_and_left Γ p q : AugContext Γ (nd_and p q) -> AugContext Γ p.
Proof.
  intro H. apply ac_classical.
  assert (H' : AugContext (FNeg p::Γ) (nd_and p q)) by (eapply ac_weaken; [|exact H]; intros x X; now right).
  eapply ac_explosion with (p:=FImp p (FNeg q)); [|exact H'].
  apply ac_deduction. eapply ac_explosion with (p:=p).
  - apply ac_hyp. now left.
  - apply ac_hyp. cbn. auto.
Qed.
Lemma ac_and_right Γ p q : AugContext Γ (nd_and p q) -> AugContext Γ q.
Proof.
  intro H. apply ac_classical.
  assert (H' : AugContext (FNeg q::Γ) (nd_and p q)) by (eapply ac_weaken; [|exact H]; intros x X; now right).
  eapply ac_explosion with (p:=FImp p (FNeg q)); [|exact H'].
  apply ac_deduction. apply ac_hyp. cbn. auto.
Qed.
Lemma ac_or_left Γ p q : AugContext Γ p -> AugContext Γ (nd_or p q).
Proof.
  intro H. unfold nd_or. apply ac_deduction. eapply ac_explosion with (p:=p).
  - eapply ac_weaken; [|exact H]. intros x X. now right.
  - apply ac_hyp. now left.
Qed.
Lemma ac_or_elim Γ p q r : AugContext Γ (nd_or p q) -> AugContext (p::Γ) r ->
  AugContext (q::Γ) r -> AugContext Γ r.
Proof.
  intros H P Q. apply ac_deduction in P. apply ac_deduction in Q. apply ac_classical.
  assert (P' : AugContext (FNeg r::Γ) (FImp p r)) by (eapply ac_weaken; [|exact P]; intros x X; now right).
  assert (Q' : AugContext (FNeg r::Γ) (FImp q r)) by (eapply ac_weaken; [|exact Q]; intros x X; now right).
  assert (H' : AugContext (FNeg r::Γ) (nd_or p q)) by (eapply ac_weaken; [|exact H]; intros x X; now right).
  assert (NP : AugContext (FNeg r::Γ) (FNeg p)).
  { apply ac_neg_intro. eapply ac_explosion with (p:=r).
    - eapply ac_mp; [eapply ac_weaken; [|exact P']; intros x X; now right|apply ac_hyp; now left].
    - apply ac_hyp. cbn. auto. }
  assert (Q0 : AugContext (FNeg r::Γ) q) by (unfold nd_or in H'; eapply ac_mp; eassumption).
  eapply ac_explosion with (p:=r).
  - eapply ac_mp; eassumption.
  - apply ac_hyp. now left.
Qed.

Print Assumptions ac_deduction.
Print Assumptions ac_finish.
Print Assumptions ac_classical.
Print Assumptions ac_neg_intro.
Print Assumptions ac_double_neg_elim.
Print Assumptions ac_and_intro.
Print Assumptions ac_and_left.
Print Assumptions ac_and_right.
Print Assumptions ac_or_left.
Print Assumptions ac_or_elim.
