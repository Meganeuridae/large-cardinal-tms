(** Natural-deduction proof that a function relation on the input set yields
    a globally partial-functional guarded relation. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import ProofFormula TheoryIrreflexiveND AugmentedInstantiation StandardND StandardLogical.
Import ListNotations.

Definition replacement_domain := FMember 3 0.
Definition replacement_unique_body p := FAll 2 (FImp p (FEqual 2 1)).
Definition replacement_global_unique p := FAll 3 (nd_ex 1 (replacement_unique_body p)).
Definition replacement_bounded_unique p := FAll 3 (FImp replacement_domain (nd_ex 1 (replacement_unique_body p))).
Definition replacement_guard p := nd_and replacement_domain p.

Theorem bounded_unique_implies_guarded_global p : StandardND []
  (FImp (replacement_bounded_unique p) (replacement_global_unique (replacement_guard p))).
Proof.
  unfold replacement_global_unique. apply std_imp_intro. apply std_all_intro.
  - unfold nd_fresh. intros f [E|[]]. subst f. cbn [replacement_bounded_unique nd_free]. reflexivity.
  - set (A := replacement_bounded_unique p).
    set (M := replacement_domain).
    set (Q := replacement_unique_body (replacement_guard p)).
    change (StandardND [A] (nd_ex 1 Q)).
    apply std_classical.
    assert (NotM : StandardND [FNeg (nd_ex 1 Q);A] (FNeg M)).
    { apply std_neg_intro.
      assert (Has : StandardND [M;FNeg (nd_ex 1 Q);A] (nd_ex 1 (replacement_unique_body p))).
      { eapply std_imp_elim.
        - eapply (std_all_same _ 3 (FImp M (nd_ex 1 (replacement_unique_body p)))).
          apply std_hyp. cbn. auto.
        - apply std_hyp. now left. }
      eapply (std_ex_elim [M;FNeg (nd_ex 1 Q);A] 1 1 (replacement_unique_body p) nd_false).
      - apply safe_subst_self.
      - now left.
      - unfold nd_fresh. intros t [E|[E|[E|[]]]]; subst t; unfold M,Q,A,replacement_domain,replacement_unique_body,replacement_bounded_unique,replacement_guard,nd_ex;
          cbn [nd_free nd_and]; reflexivity.
      - cbn [nd_false nd_true nd_free]. reflexivity.
      - exact Has.
      - rewrite nd_subst_self.
        eapply std_exfalso with (p:=nd_ex 1 Q).
        + unfold Q. eapply (std_ex_intro _ 1 1); [apply safe_subst_self|]. rewrite nd_subst_self.
          apply std_all_intro.
          * unfold nd_fresh. intros t [E|[E|[E|[E|[]]]]]; subst t;
              unfold M,A,Q,replacement_domain,replacement_unique_body,replacement_bounded_unique,replacement_guard,nd_ex;
              cbn [nd_free nd_and]; reflexivity.
          * apply std_imp_intro. eapply std_imp_elim.
            -- eapply (std_all_same _ 2 (FImp p (FEqual 2 1))). apply std_hyp. cbn. auto.
            -- eapply std_and_right. apply std_hyp. now left.
        + apply std_hyp. cbn. auto. }
    assert (FromNotM : StandardND [FNeg M;FNeg (nd_ex 1 Q);A] (nd_ex 1 Q)).
    { unfold Q. eapply (std_ex_intro _ 1 1); [apply safe_subst_self|]. rewrite nd_subst_self.
      apply std_all_intro.
      - unfold nd_fresh. intros t [E|[E|[E|[]]]]; subst t;
          unfold M,A,Q,replacement_domain,replacement_unique_body,replacement_bounded_unique,replacement_guard,nd_ex;
          cbn [nd_free nd_and]; reflexivity.
      - apply std_imp_intro. eapply std_exfalso with (p:=M).
        + eapply std_and_left. apply std_hyp. now left.
        + apply std_hyp. cbn. auto. }
    eapply std_exfalso with (p:=nd_ex 1 Q).
    + eapply std_imp_elim with (p:=FNeg M); [apply std_imp_intro; exact FromNotM|exact NotM].
    + apply std_hyp. now left.
Qed.

Print Assumptions bounded_unique_implies_guarded_global.
