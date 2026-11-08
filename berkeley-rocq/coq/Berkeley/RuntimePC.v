(** Well-formed PC prefixes, zero-padding normalization, and update closure. *)
From Stdlib Require Import Lists.List Streams.Streams Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From Berkeley Require Import FiniteMachine Data Machine RuntimeTape RuntimeRegisters
  RuntimeControl RuntimeCalls RuntimeProgram RuntimeSimulation RuntimeJumps RuntimeJumpBounds RuntimeTraces.
Import ListNotations.

Lemma read_path_app q a t b u : ReadPath q a t -> ReadPath t b u -> ReadPath q (a++b) u.
Proof. intros A. revert b u. induction A; intros rest u B; simpl; [exact B|econstructor; eauto]. Qed.
Lemma read_path_split q a b u : ReadPath q (a++b) u ->
  exists t, ReadPath q a t /\ ReadPath t b u.
Proof.
  revert q. induction a as [|x a IH]; intros q H.
  - exists q. split; [constructor|exact H].
  - inversion H as [|q0 bit mid rest out N E P]; subst. destruct (IH _ P) as [t [A B]].
    exists t. split; [econstructor; eassumption|exact B].
Qed.
Lemma read_path_height q w t : ReadPath q w t -> length w + height t <= height q.
Proof.
  intro P. induction P; [simpl; lia|].
  pose proof (right_edge_sound _ _ _ _ H H0) as [_ [A _]]. simpl. lia.
Qed.
Lemma read_path_admissible q w t : ReadPath q w t -> admissible q=true -> admissible t=true.
Proof.
  intro P. induction P; intro A; [exact A|]. apply IHP.
  exact (proj2 (proj2 (proj2 (right_edge_sound _ _ _ _ H H0)))).
Qed.
Lemma node_height_positive q : node q=true -> 1<=height q.
Proof.
  intro N. pose proof (checked_node_sound q false N) as C.
  unfold checked_edge in C. destruct (lookup new_table q false) as [[[w d]t]|] eqn:E; [|discriminate].
  destruct d.
  - destruct (jump_guard_sound _ _ _ _ N E) as [F _]. discriminate.
  - pose proof (right_edge_sound _ _ _ _ N E) as [_ [A _]]. lia.
Qed.

Inductive GoodPC : list bool -> Prop :=
| good_read w q : ReadPath 72 w q -> GoodPC w
| good_jump w q t : ReadPath 72 w q -> node q=true ->
    lookup new_table q true = Some(false,L,t) -> GoodPC (w++[true]).

Lemma good_empty : GoodPC []. Proof. apply (good_read [] 72). constructor. Qed.
Theorem good_pc_bound w : GoodPC w -> length w<=404.
Proof.
  intro H. destruct H.
  - pose proof (read_path_bounds _ _ _ H) as [A _]. exact A.
  - pose proof (read_path_height _ _ _ H) as A. pose proof (node_height_positive _ H0).
    change (length w + height q<=404) in A. rewrite app_length. simpl. lia.
Qed.

Lemma flip_prefix_good pre suf q : ReadPath 72 (pre++false::suf) q -> GoodPC (pre++[true]).
Proof.
  intro P. destruct (read_path_split _ _ _ _ P) as [t [A B]].
  inversion B as [|q0 bit v rest out N E0 P0]; subst.
  pose proof (checked_node_sound t true N) as C.
  unfold checked_edge in C. destruct (lookup new_table t true) as [[[w d]u]|] eqn:E; [|discriminate].
  destruct d.
  - destruct (jump_guard_sound _ _ _ _ N E) as [_ [W _]]. subst w.
    eapply good_jump; eassumption.
  - destruct (right_edge_sound _ _ _ _ N E) as [W _]. subst w.
    apply (good_read _ u). eapply read_path_app; [exact A|]. econstructor; [exact N|exact E|constructor].
Qed.

Lemma break_word_shape k w out n : break_pc k (rev w++[false])=Some(out,n) ->
  return_word out=[] \/ exists pre suf, w=pre++false::suf /\ return_word out=pre++[true].
Proof.
  revert k out n. induction w using rev_ind; intros k out n E.
  - destruct k; cbn [rev app break_pc] in E; [inversion E; subst; left; reflexivity|discriminate].
  - rewrite rev_app_distr in E. cbn [rev app] in E. destruct x.
    + cbn [break_pc] in E. destruct (break_pc k (rev w++[false])) as [[o z]|] eqn:F; [|discriminate].
      inversion E; subst. destruct (IHw _ _ _ F) as [H|[pre [suf [A B]]]]; [left;exact H|].
      right. exists pre,(suf++[true]). split; [rewrite A,<-app_assoc; reflexivity|exact B].
    + destruct k as [|k].
      * cbn [break_pc] in E. inversion E; subst. right. exists w,([]:list bool). split; [reflexivity|].
        unfold return_word. change (rev(removelast ((true::rev w)++[false]))=w++[true]).
        rewrite removelast_last. cbn [rev]. now rewrite rev_involutive.
      * cbn [break_pc] in E. destruct (break_pc k (rev w++[false])) as [[o z]|] eqn:F; [|discriminate].
        inversion E; subst. destruct (IHw _ _ _ F) as [H|[pre [suf [A B]]]]; [left;exact H|].
        right. exists pre,(suf++[false]). split; [rewrite A,<-app_assoc; reflexivity|exact B].
Qed.
Theorem break_preserves_good w q k out n : ReadPath 72 w q ->
  break_pc k (rev w++[false])=Some(out,n) -> GoodPC (return_word out).
Proof.
  intros P E. destruct (break_word_shape _ _ _ _ E) as [H|[pre [suf [A B]]]].
  - rewrite H. apply good_empty.
  - rewrite B. subst w. eapply flip_prefix_good; exact P.
Qed.
Lemma continue_suffix k bits out n : continue_pc k bits=Some(out,n) ->
  exists pre, bits=pre++out.
Proof.
  revert k out n. induction bits as [|b bits IH]; intros k out n E.
  - destruct k; [inversion E; subst; exists ([]:list bool); reflexivity|discriminate].
  - destruct k as [|k]; [inversion E; subst; exists ([]:list bool); reflexivity|].
    cbn [continue_pc] in E. destruct (continue_pc (if b then k else S k) bits) as [[o z]|] eqn:F; [|discriminate].
    inversion E; subst. destruct (IH _ _ _ F) as [pre H]. exists (b::pre). simpl. now rewrite H.
Qed.
Theorem continue_preserves_good w q k out n : ReadPath 72 w q ->
  continue_pc k (rev w)=Some(out,n) -> GoodPC (rev out).
Proof.
  intros P E. destruct (continue_suffix _ _ _ _ E) as [pre H].
  assert (W : w=rev out++rev pre) by (rewrite <-(rev_involutive w),H,rev_app_distr; reflexivity).
  rewrite W in P. destruct (read_path_split _ _ _ _ P) as [t [A B]]. eapply good_read; exact A.
Qed.

Theorem ir_step_preserves_good a b : IRStep a b -> GoodPC (fst b).
Proof.
  intro H. destruct H; cbn [fst];
    first [eapply break_preserves_good; eassumption|eapply continue_preserves_good; eassumption].
Qed.
Theorem ir_step_register_count a b : IRStep a b -> length(snd a)<=length(snd b).
Proof. intro H. destruct H; cbn [snd]; rewrite ?app_length; simpl; rewrite ?app_length; simpl; lia. Qed.

Lemma zero_completion fuel : forall q, admissible q=true -> height q<=fuel ->
  exists n t, ReadPath q (repeat false n) t /\ terminal t=true /\ n<=height q.
Proof.
  induction fuel as [|fuel IH]; intros q A Hfuel;
    unfold admissible in A; destruct (node q) eqn:N.
  - pose proof (node_height_positive _ N). lia.
  - exists 0,q. split; [constructor|]. split; [exact A|lia].
  - pose proof (checked_node_sound q false N) as C. unfold checked_edge in C.
    destruct (lookup new_table q false) as [[[w d]t]|] eqn:E; [|discriminate]. destruct d.
    + destruct (jump_guard_sound _ _ _ _ N E) as [F _]. discriminate.
    + destruct (right_edge_sound _ _ _ _ N E) as [W [Ht [_ At]]]. subst w.
      destruct (IH t At ltac:(lia)) as [n [u [P [T Hn]]]].
      exists (S n),u. split; [simpl; econstructor; eassumption|]. split; [exact T|lia].
  - exists 0,q. split; [constructor|]. split; [exact A|lia].
Qed.
Theorem root_zero_completion w q : ReadPath 72 w q -> exists n t,
  ReadPath 72 (w++repeat false n) t /\ terminal t=true /\ length w+n<=404.
Proof.
  intro P. pose proof (read_path_height _ _ _ P) as H.
  change (length w+height q<=404) in H.
  assert (A : admissible q=true) by (eapply read_path_admissible; [exact P|reflexivity]).
  destruct (zero_completion (height q) q A ltac:(lia)) as [n [t [B [T Hn]]]].
  exists n,t. split; [eapply read_path_app; eassumption|]. split; [exact T|lia].
Qed.

Lemma normal_zero_extension width w n rs : length w+n<=width ->
  normal width w rs=normal width (w++repeat false n) rs.
Proof.
  intro H. unfold normal,root_cfg. rewrite app_length,repeat_length,Str_app_assoc,prefix_repeat.
  rewrite <-copies_add. replace (n+S(S(width-(length w+n)))) with (S(S(width-length w))) by lia.
  reflexivity.
Qed.

Print Assumptions good_pc_bound.
Print Assumptions ir_step_preserves_good.
Print Assumptions root_zero_completion.
Print Assumptions normal_zero_extension.
