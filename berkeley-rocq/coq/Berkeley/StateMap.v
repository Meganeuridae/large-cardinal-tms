From Stdlib Require Import Lists.List Streams.Streams Bool.Bool.
From BusyCoq Require Import TM.

Module Type BinaryCtx := Ctx with Definition Sym := bool.

Module StateMap (A : BinaryCtx) (B : BinaryCtx).
  Module TA := TM.TM A.
  Module TB := TM.TM B.
  Definition tape := (Stream bool * bool * Stream bool)%type.
  Definition lift (f : A.Q -> B.Q) (c : A.Q * tape) : B.Q * tape :=
    (f (fst c), snd c).
  Definition respects (f : A.Q -> B.Q) (a : TA.TM) (b : TB.TM) :=
    forall q s, b (f q, s) =
      option_map (fun '(w,d,q') => (w,d,f q')) (a (q,s)).

  Section Proof.
    Variables (f : A.Q -> B.Q) (a : TA.TM) (b : TB.TM).
    Hypothesis H : respects f a b.

    Lemma step_forward c c' : TA.step a c c' -> TB.step b (lift f c) (lift f c').
    Proof.
      intro S. destruct S; unfold lift; simpl.
      - apply TB.step_left. rewrite H. exact (f_equal (option_map (fun '(w,d,q) => (w,d,f q))) H0).
      - apply TB.step_right. rewrite H. exact (f_equal (option_map (fun '(w,d,q) => (w,d,f q))) H0).
    Qed.

    Lemma halted_equiv c : TA.halted a c <-> TB.halted b (lift f c).
    Proof.
      destruct c as [q [[l s] r]]. unfold TA.halted, TB.halted, lift; simpl.
      rewrite H.
      assert (K : forall (X Y : Type) (g : X -> Y) (o : option X),
        o = None <-> option_map g o = None).
      { intros X Y g [x|]; simpl; split; congruence. }
      apply K.
    Qed.

    Lemma run_forward n c c' :
      TA.multistep a n c c' -> TB.multistep b n (lift f c) (lift f c').
    Proof.
      intro S. induction S.
      - constructor.
      - econstructor; eauto using step_forward.
    Qed.

    Lemma step_backward c d : TB.step b (lift f c) d ->
      exists c', TA.step a c c' /\ d = lift f c'.
    Proof.
      destruct c as [q [[l s] r]]. intro S.
      destruct (a (q,s)) as [[[w dir] q']|] eqn:E.
      - destruct dir.
        + exists (q', TA.move_left (l,w,r)). split.
          * apply TA.step_left. exact E.
          * eapply TB.step_deterministic; [exact S|].
            apply step_forward, TA.step_left. exact E.
        + exists (q', TA.move_right (l,w,r)). split.
          * apply TA.step_right. exact E.
          * eapply TB.step_deterministic; [exact S|].
            apply step_forward, TA.step_right. exact E.
      - exfalso. eapply TB.halted_no_step; [|exact S].
        apply halted_equiv. exact E.
    Qed.

    Lemma run_backward n c d : TB.multistep b n (lift f c) d ->
      exists c', TA.multistep a n c c' /\ d = lift f c'.
    Proof.
      revert c d. induction n; intros c d S.
      - inversion S; subst. exists c. split; [constructor|reflexivity].
      - inversion S; subst.
        match goal with
        | Hs : TB.step b (lift f c) ?d1,
          Hr : TB.multistep b n ?d1 d |- _ =>
          destruct (step_backward c d1 Hs) as [c1 [Hc1 E]];
          subst d1;
          destruct (IHn c1 d Hr) as [c2 [Hc2 E2]];
          exists c2; split; [econstructor; eassumption|exact E2]
        end.
    Qed.

    Theorem halts_equiv c : TA.halts a c <-> TB.halts b (lift f c).
    Proof.
      split.
      - intros [n [d [Hr Hh]]]. exists n, (lift f d). split.
        + apply run_forward. exact Hr.
        + apply halted_equiv. exact Hh.
      - intros [n [d [Hr Hh]]].
        destruct (run_backward n c d Hr) as [c' [Hr' E]]. subst d.
        exists n, c'. split; [exact Hr'|]. apply halted_equiv. exact Hh.
    Qed.
  End Proof.
End StateMap.
