(** Independent natural-deduction derivations of the concrete logical schemes. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
From Berkeley Require Import ProofFormula TheoryIrreflexiveND LogicFresh LogicFinite AugmentedInstantiation AugmentedCapture StandardND.
Import ListNotations.
Lemma safe_subst_self x p : safe_subst x x p=true.
Proof.
  induction p as [a b|a b|p IH|p IH q JH|z p IH]; cbn [safe_subst]; auto.
  - now rewrite IH,JH.
  - destruct (Nat.eqb z x) eqn:E; auto.
Qed.
Lemma std_all_same Γ x p : StandardND Γ (FAll x p) -> StandardND Γ p.
Proof.
  intro H. rewrite <- (nd_subst_self x p). eapply std_all_elim; [apply safe_subst_self|exact H].
Qed.
Lemma std_C5 x p : nd_free x p=false -> StandardND [] (FImp p (FAll x p)).
Proof.
  intro Fresh. apply std_imp_intro,std_all_intro.
  - unfold nd_fresh. intros t [E|[]]. now subst.
  - apply std_hyp. now left.
Qed.
Lemma std_b1 p q : StandardND [] (FImp p (FImp q p)).
Proof. apply std_imp_intro,std_imp_intro,std_hyp. cbn. auto. Qed.
Lemma std_b2 p q r : StandardND []
  (FImp (FImp p (FImp q r)) (FImp (FImp p q) (FImp p r))).
Proof.
  do 3 apply std_imp_intro. eapply std_imp_elim.
  - eapply std_imp_elim; [apply std_hyp; cbn; auto|apply std_hyp; cbn; auto].
  - eapply std_imp_elim; [apply std_hyp; cbn; auto|apply std_hyp; cbn; auto].
Qed.
Lemma std_b3 p q : StandardND []
  (FImp (FImp (FNeg p) (FNeg q)) (FImp q p)).
Proof.
  do 2 apply std_imp_intro. apply std_classical. eapply std_exfalso with (p:=q).
  - apply std_hyp. cbn. auto.
  - eapply std_imp_elim; [apply std_hyp; cbn; auto|apply std_hyp; cbn; auto].
Qed.
Lemma std_b4 x p q : StandardND []
  (FImp (FAll x (FImp (FAll x p) q)) (FImp (FAll x p) (FAll x q))).
Proof.
  do 2 apply std_imp_intro. apply std_all_intro.
  - unfold nd_fresh. intros t [E|[E|[]]]; subst t; cbn [nd_free]; now rewrite Nat.eqb_refl.
  - eapply std_imp_elim.
    + eapply std_all_same. apply std_hyp. cbn. auto.
    + apply std_hyp. cbn. auto.
Qed.
Lemma std_b5 x p : StandardND [] (FImp (FAll x p) p).
Proof. apply std_imp_intro. eapply (std_all_same _ x p). apply std_hyp. now left. Qed.
Lemma std_b6 x y p : StandardND [] (FImp (FAll x (FAll y p)) (FAll y (FAll x p))).
Proof.
  apply std_imp_intro. apply std_all_intro.
  - unfold nd_fresh. intros t [E|[]]. subst t. cbn [nd_free].
    destruct (Nat.eqb y x); cbn; [reflexivity|now rewrite Nat.eqb_refl].
  - apply std_all_intro.
    + unfold nd_fresh. intros t [E|[]]. subst t. cbn [nd_free]. now rewrite Nat.eqb_refl.
    + eapply (std_all_same _ y p). eapply (std_all_same _ x (FAll y p)). apply std_hyp. now left.
Qed.
Lemma std_b7 x p : StandardND [] (FImp (FNeg p) (FAll x (FNeg (FAll x p)))).
Proof.
  apply std_imp_intro. eapply std_imp_elim.
  - apply std_closed,std_C5. cbn [nd_free]. now rewrite Nat.eqb_refl.
  - apply std_neg_intro. eapply std_exfalso with (p:=p).
    + eapply (std_all_same _ x p). apply std_hyp. now left.
    + apply std_hyp. cbn. auto.
Qed.
Lemma std_b8 x y z : StandardND []
  (FImp (FEqual x y) (FImp (FEqual x z) (FEqual y z))).
Proof.
  do 2 apply std_imp_intro. eapply std_eq_trans.
  - apply std_eq_sym,std_hyp. cbn. auto.
  - apply std_hyp. cbn. auto.
Qed.
Lemma std_all_eq_refl x : StandardND [] (FAll x (FEqual x x)).
Proof. apply std_all_intro; [unfold nd_fresh; intros p []|apply std_eq_refl]. Qed.
Lemma std_false_self_dist Γ x p : StandardND Γ (distinctor x x) -> StandardND Γ p.
Proof.
  intro N. eapply std_exfalso with (p:=FAll x (FEqual x x)).
  - apply std_closed,std_all_eq_refl.
  - exact N.
Qed.
Lemma std_b9 x y z : StandardND []
  (FImp (distinctor x y) (FImp (distinctor x z) (FImp (FEqual y z) (FAll x (FEqual y z))))).
Proof.
  do 3 apply std_imp_intro. destruct (Nat.eq_dec x y) as [E|E].
  - subst y. eapply std_false_self_dist. apply std_hyp. cbn. auto.
  - destruct (Nat.eq_dec x z) as [F|F].
    + subst z. eapply std_false_self_dist. apply std_hyp. cbn. auto.
    + eapply std_imp_elim; [apply std_closed,std_C5|apply std_hyp; now left].
      cbn [nd_free]. apply Nat.eqb_neq in E,F. now rewrite E,F.
Qed.
Lemma std_b10 x y p : StandardND [] (FImp (FAll x (FImp (FEqual x y) (FAll x p))) p).
Proof.
  apply std_imp_intro. destruct (Nat.eq_dec x y) as [E|E].
  - subst y. eapply (std_all_same _ x p). eapply std_imp_elim with (p:=FEqual x x).
    + eapply (std_all_same _ x (FImp (FEqual x x) (FAll x p))). apply std_hyp. now left.
    + apply std_eq_refl.
  - assert (H : StandardND [FAll x (FImp (FEqual x y) (FAll x p))]
      (FImp (FEqual y y) (FAll x p))).
    { replace (FImp (FEqual y y) (FAll x p)) with
        (nd_subst x y (FImp (FEqual x y) (FAll x p))).
      - eapply std_all_elim; [|apply std_hyp; now left]. cbn [safe_subst]. now rewrite Nat.eqb_refl.
      - cbn [nd_subst]. rewrite Nat.eqb_refl. apply Nat.eqb_neq in E. rewrite Nat.eqb_sym,E. reflexivity. }
    eapply (std_all_same _ x p). eapply std_imp_elim; [exact H|apply std_eq_refl].
Qed.
Lemma std_b12 x y z : StandardND []
  (FImp (FEqual x y) (FImp (FMember x z) (FMember y z))).
Proof. do 2 apply std_imp_intro. eapply std_mem_left; apply std_hyp; cbn; auto. Qed.
Lemma std_b13 x y z : StandardND []
  (FImp (FEqual x y) (FImp (FMember z x) (FMember z y))).
Proof. do 2 apply std_imp_intro. eapply std_mem_right; apply std_hyp; cbn; auto. Qed.
Lemma std_b14 x y z : StandardND []
  (FImp (distinctor x y) (FImp (distinctor x z) (FImp (FMember y z) (FAll x (FMember y z))))).
Proof.
  do 3 apply std_imp_intro. destruct (Nat.eq_dec x y) as [E|E].
  - subst y. eapply std_false_self_dist. apply std_hyp. cbn. auto.
  - destruct (Nat.eq_dec x z) as [F|F].
    + subst z. eapply std_false_self_dist. apply std_hyp. cbn. auto.
    + eapply std_imp_elim; [apply std_closed,std_C5|apply std_hyp; now left].
      cbn [nd_free]. apply Nat.eqb_neq in E,F. now rewrite E,F.
Qed.
Print Assumptions std_b1.
Print Assumptions std_b10.
Print Assumptions std_b14.

Fixpoint max_var p :=
  match p with
  | FEqual x y | FMember x y => Nat.max x y
  | FNeg p => max_var p
  | FImp p q => Nat.max (max_var p) (max_var q)
  | FAll x p => Nat.max x (max_var p)
  end.
Lemma vars_below_monotone n m p : n<=m -> vars_below n p -> vars_below m p.
Proof.
  intros N. induction p; cbn [vars_below] in *; intuition lia.
Qed.
Lemma vars_below_max p : vars_below (S (max_var p)) p.
Proof.
  induction p as [a b|a b|p IH|p IH q JH|x p IH]; cbn [vars_below max_var].
  - pose proof (Nat.le_max_l a b). pose proof (Nat.le_max_r a b). lia.
  - pose proof (Nat.le_max_l a b). pose proof (Nat.le_max_r a b). lia.
  - exact IH.
  - split.
    + eapply (vars_below_monotone (S(max_var p))); [pose proof (Nat.le_max_l (max_var p) (max_var q)); lia|exact IH].
    + eapply (vars_below_monotone (S(max_var q))); [pose proof (Nat.le_max_r (max_var p) (max_var q)); lia|exact JH].
  - split; [pose proof (Nat.le_max_l x (max_var p)); lia|].
    eapply (vars_below_monotone (S(max_var p))); [pose proof (Nat.le_max_r x (max_var p)); lia|exact IH].
Qed.
Lemma below_var_is_fresh n p : vars_below n p -> nd_free n p=false /\ nd_not_bound n p=true.
Proof.
  induction p as [a b|a b|p IH|p IH q JH|x p IH]; cbn [vars_below nd_free nd_not_bound].
  - intros [A B]. assert ((n=?a)=false) by (apply Nat.eqb_neq;lia).
    assert ((n=?b)=false) by (apply Nat.eqb_neq;lia). now rewrite H,H0.
  - intros [A B]. assert ((n=?a)=false) by (apply Nat.eqb_neq;lia).
    assert ((n=?b)=false) by (apply Nat.eqb_neq;lia). now rewrite H,H0.
  - apply IH.
  - intros [P Q]. destruct (IH P) as [F1 B1]. destruct (JH Q) as [F2 B2]. now rewrite F1,F2,B1,B2.
  - intros [X P]. destruct (IH P) as [F B].
    assert ((n=?x)=false) by (apply Nat.eqb_neq;lia).
    assert ((x=?n)=false) by (apply Nat.eqb_neq;lia). now rewrite H,H0,F,B.
Qed.
Lemma std_specialize_equal Γ x y t : x<>y -> StandardND Γ (FAll x (FEqual x y)) -> StandardND Γ (FEqual t y).
Proof.
  intros XY H. replace (FEqual t y) with (nd_subst x t (FEqual x y)).
  - eapply std_all_elim; [reflexivity|exact H].
  - cbn [nd_subst]. rewrite Nat.eqb_refl. assert ((y=?x)=false) by (apply Nat.eqb_neq; congruence). now rewrite H0.
Qed.
Lemma std_singletonize Γ x y z w : x<>y -> nd_fresh z Γ -> nd_fresh w Γ ->
  StandardND Γ (FAll x (FEqual x y)) -> StandardND Γ (FAll z (FAll w (FEqual z w))).
Proof.
  intros XY Z W H. apply std_all_intro; [exact Z|]. apply std_all_intro; [exact W|].
  eapply std_eq_trans with (y:=y).
  - eapply std_specialize_equal; eassumption.
  - apply std_eq_sym. eapply std_specialize_equal; eassumption.
Qed.
Lemma std_singleton_equal Γ z w y : z<>w ->
  StandardND Γ (FAll z (FAll w (FEqual z w))) -> StandardND Γ (FEqual y z).
Proof.
  intros ZW H. apply std_eq_sym.
  assert (One : StandardND Γ (FAll w (FEqual z w))) by (eapply std_all_same; exact H).
  replace (FEqual z y) with (nd_subst w y (FEqual z w)).
  - eapply std_all_elim; [reflexivity|exact One].
  - cbn [nd_subst]. rewrite Nat.eqb_refl. assert ((z=?w)=false) by (apply Nat.eqb_neq;congruence). now rewrite H0.
Qed.
Lemma std_b11 x y p : StandardND []
  (FImp (FAll x (FEqual x y)) (FImp (FAll x p) (FAll y p))).
Proof.
  do 2 apply std_imp_intro. destruct (Nat.eq_dec x y) as [XY|XY].
  - subst y. apply std_hyp. now left.
  - set (z:=S (Nat.max (Nat.max x y) (max_var p))). set (w:=S z).
    assert (Mx : x<z).
    { unfold z. pose proof (Nat.le_max_l x y). pose proof (Nat.le_max_l (Nat.max x y) (max_var p)). lia. }
    assert (My : y<z).
    { unfold z. pose proof (Nat.le_max_r x y). pose proof (Nat.le_max_l (Nat.max x y) (max_var p)). lia. }
    assert (Mp : S (max_var p)<=z).
    { unfold z. pose proof (Nat.le_max_r (Nat.max x y) (max_var p)). lia. }
    assert (Pz : vars_below z p) by (eapply vars_below_monotone; [exact Mp|apply vars_below_max]).
    assert (Pw : vars_below w p) by (eapply (vars_below_monotone z w p); [unfold w;lia|exact Pz]).
    destruct (below_var_is_fresh z p Pz) as [FreeZ BoundZ].
    destruct (below_var_is_fresh w p Pw) as [FreeW BoundW].
    assert (ZX : (z=?x)=false) by (apply Nat.eqb_neq;lia).
    assert (ZY : (z=?y)=false) by (apply Nat.eqb_neq;lia).
    assert (WX : (w=?x)=false) by (apply Nat.eqb_neq;unfold w;lia).
    assert (WY : (w=?y)=false) by (apply Nat.eqb_neq;unfold w;lia).
    assert (Fz : nd_fresh z [FAll x p;FAll x (FEqual x y)]).
    { unfold nd_fresh. intros f [E|[E|[]]]; subst f; cbn [nd_free]; now rewrite ZX,?ZY,?FreeZ. }
    assert (Fw : nd_fresh w [FAll x p;FAll x (FEqual x y)]).
    { unfold nd_fresh. intros f [E|[E|[]]]; subst f; cbn [nd_free]; now rewrite WX,?WY,?FreeW. }
    assert (Single : StandardND [FAll x p;FAll x (FEqual x y)] (FAll z (FAll w (FEqual z w)))).
    { eapply std_singletonize; [exact XY|exact Fz|exact Fw|apply std_hyp; cbn; auto]. }
    eapply (std_all_alpha_reverse _ y z p); [exact BoundZ|exact FreeZ|].
    apply std_all_intro; [exact Fz|].
    eapply (std_eq_substitute _ y z p).
    + now apply nd_not_bound_implies_safe.
    + eapply (std_singleton_equal _ z w y); [unfold w;lia|exact Single].
    + eapply (std_all_same _ x p). apply std_hyp. now left.
Qed.
Print Assumptions std_b11.
