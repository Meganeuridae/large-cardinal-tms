(** Contextual Hilbert deduction and propositional rules for translating the
    irreflexivity certificate. No quantifier or equality rules are assumed. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import ProofFormula ProofPresentation LogicBridge TheoryIrreflexiveND.
Import ListNotations.

Inductive HContext (ctx : list fol_formula) : fol_formula -> Prop :=
| hc_hyp p : In p ctx -> HContext ctx p
| hc_theorem p : PresentedProvable p -> HContext ctx p
| hc_mp p q : HContext ctx (FImp p q) -> HContext ctx p -> HContext ctx q.

Lemma hc_weaken Γ Δ p : (forall q, In q Γ -> In q Δ) -> HContext Γ p -> HContext Δ p.
Proof. intros Inc H. induction H; [apply hc_hyp,Inc;assumption|apply hc_theorem;assumption|eapply hc_mp; eassumption]. Qed.

Lemma hc_logical Γ p : LogicalProvable p -> HContext Γ p.
Proof. intro H. apply hc_theorem,logical_embeds_in_presented,H. Qed.

Theorem hc_deduction Γ p q : HContext (p::Γ) q -> HContext Γ (FImp p q).
Proof.
  intro H. remember (p::Γ) as ctx eqn:E. induction H as [f Member|f Global|a b Major IHm Minor IHn]; subst ctx.
  - cbn in Member. destruct Member as [Eq|Member].
    + subst f. apply hc_logical,logical_identity.
    + eapply hc_mp; [apply hc_logical,logical_b1|now apply hc_hyp].
  - eapply hc_mp; [apply hc_logical,logical_b1|now apply hc_theorem].
  - eapply hc_mp; [eapply hc_mp; [apply hc_logical,logical_b2|apply IHm; reflexivity]|apply IHn; reflexivity].
Qed.

Lemma hc_finish p : HContext [] p -> PresentedProvable p.
Proof. intro H. induction H; [contradiction|assumption|eapply presented_mp; eassumption]. Qed.

Lemma hc_true Γ : HContext Γ nd_true.
Proof. unfold nd_true. apply hc_logical,logical_identity. Qed.
Lemma hc_explosion Γ p q : HContext Γ p -> HContext Γ (FNeg p) -> HContext Γ q.
Proof.
  intros A B. eapply hc_mp; [eapply hc_mp; [apply hc_theorem,presented_explosion|exact A]|exact B].
Qed.
Lemma hc_classical Γ p : HContext (FNeg p::Γ) nd_false -> HContext Γ p.
Proof.
  intro H. apply hc_deduction in H. unfold nd_false in H.
  eapply hc_mp; [eapply hc_mp; [apply hc_logical,logical_b3|exact H]|apply hc_true].
Qed.
Lemma hc_double_neg_elim Γ p : HContext Γ (FNeg (FNeg p)) -> HContext Γ p.
Proof.
  intro H. apply hc_classical.
  eapply hc_explosion with (p:=FNeg p).
  - apply hc_hyp. now left.
  - eapply hc_weaken; [|exact H]. intros q Q. now right.
Qed.
Lemma hc_neg_intro Γ p : HContext (p::Γ) nd_false -> HContext Γ (FNeg p).
Proof.
  intro H. apply hc_deduction in H. apply hc_classical.
  eapply hc_mp.
  - eapply hc_weaken; [|exact H]. intros q Q. now right.
  - apply hc_double_neg_elim. apply hc_hyp. now left.
Qed.
Lemma hc_double_neg_intro Γ p : HContext Γ p -> HContext Γ (FNeg (FNeg p)).
Proof.
  intro H. apply hc_neg_intro. eapply hc_explosion with (p:=p).
  - eapply hc_weaken; [|exact H]. intros q Q. now right.
  - apply hc_hyp. now left.
Qed.

Lemma hc_and_intro Γ p q : HContext Γ p -> HContext Γ q -> HContext Γ (nd_and p q).
Proof.
  intros P Q. unfold nd_and. apply hc_neg_intro.
  assert (P' : HContext (FImp p (FNeg q)::Γ) p) by (eapply hc_weaken; [|exact P]; intros x X; now right).
  assert (Q' : HContext (FImp p (FNeg q)::Γ) q) by (eapply hc_weaken; [|exact Q]; intros x X; now right).
  eapply hc_explosion with (p:=q); [exact Q'|].
  eapply hc_mp; [apply hc_hyp; now left|exact P'].
Qed.
Lemma hc_and_left Γ p q : HContext Γ (nd_and p q) -> HContext Γ p.
Proof.
  intro H. apply hc_classical.
  assert (H' : HContext (FNeg p::Γ) (nd_and p q)) by (eapply hc_weaken; [|exact H]; intros x X; now right).
  eapply hc_explosion with (p:=FImp p (FNeg q)); [|exact H'].
  apply hc_deduction. eapply hc_explosion with (p:=p).
  - apply hc_hyp. now left.
  - apply hc_hyp. cbn. auto.
Qed.
Lemma hc_and_right Γ p q : HContext Γ (nd_and p q) -> HContext Γ q.
Proof.
  intro H. apply hc_classical.
  assert (H' : HContext (FNeg q::Γ) (nd_and p q)) by (eapply hc_weaken; [|exact H]; intros x X; now right).
  eapply hc_explosion with (p:=FImp p (FNeg q)); [|exact H'].
  apply hc_deduction. apply hc_hyp. cbn. auto.
Qed.
Lemma hc_or_left Γ p q : HContext Γ p -> HContext Γ (nd_or p q).
Proof.
  intro H. unfold nd_or. apply hc_deduction. eapply hc_explosion with (p:=p).
  - eapply hc_weaken; [|exact H]. intros x X. now right.
  - apply hc_hyp. now left.
Qed.
Lemma hc_or_elim Γ p q r : HContext Γ (nd_or p q) -> HContext (p::Γ) r ->
  HContext (q::Γ) r -> HContext Γ r.
Proof.
  intros H P Q. apply hc_deduction in P. apply hc_deduction in Q. apply hc_classical.
  assert (P' : HContext (FNeg r::Γ) (FImp p r)) by (eapply hc_weaken; [|exact P]; intros x X; now right).
  assert (Q' : HContext (FNeg r::Γ) (FImp q r)) by (eapply hc_weaken; [|exact Q]; intros x X; now right).
  assert (H' : HContext (FNeg r::Γ) (nd_or p q)) by (eapply hc_weaken; [|exact H]; intros x X; now right).
  assert (NP : HContext (FNeg r::Γ) (FNeg p)).
  { apply hc_neg_intro. eapply hc_explosion with (p:=r).
    - eapply hc_mp; [eapply hc_weaken; [|exact P']; intros x X; now right|apply hc_hyp; now left].
    - apply hc_hyp. cbn. auto. }
  assert (Q0 : HContext (FNeg r::Γ) q) by (unfold nd_or in H'; eapply hc_mp; eassumption).
  eapply hc_explosion with (p:=r).
  - eapply hc_mp; eassumption.
  - apply hc_hyp. now left.
Qed.

Print Assumptions hc_deduction.
Print Assumptions hc_finish.
Print Assumptions hc_classical.
Print Assumptions hc_neg_intro.
Print Assumptions hc_double_neg_elim.
Print Assumptions hc_and_intro.
Print Assumptions hc_and_left.
Print Assumptions hc_and_right.
Print Assumptions hc_or_left.
Print Assumptions hc_or_elim.
