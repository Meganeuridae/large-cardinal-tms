(** Every repaired source step touches only the eleven live registers and a
    successful decrement appends exactly one physical zero register. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax ConstructorFrame.
From Repair Require Import CompilerData SourceExecution.
Import ListNotations.

Definition bounded_atom a :=
  match a with SInc i | SDec i => i <? 11 | _ => true end.
Definition bounded_pair p := bounded_atom (fst p) && bounded_atom (snd p).
Lemma source_live_register_certificate : forallb bounded_pair source_graph=true.
Proof. vm_compute. reflexivity. Qed.

Lemma selected_atom_bounded program start bits a :
  forallb bounded_pair program=true -> SourceSelect program start bits a -> bounded_atom a=true.
Proof.
  intros Check Sel. induction Sel as [i pair b leaf P B Leaf|i pair b j bits leaf P B Sel IH].
  - pose proof (proj1 (forallb_forall _ _) Check pair (nth_error_In _ _ P)) as T.
    unfold bounded_pair in T. apply andb_true_iff in T as [X Y].
    rewrite <- B. destruct b; cbn [select_branch]; assumption.
  - exact IH.
Qed.
Lemma repair_selected_inc_bounded bits i :
  SourceSelect source_graph source_root bits (SInc i) -> i<11.
Proof.
  intro Sel. pose proof (selected_atom_bounded _ _ _ _ source_live_register_certificate Sel) as B.
  cbn [bounded_atom] in B. now apply Nat.ltb_lt.
Qed.
Lemma repair_selected_dec_bounded bits i :
  SourceSelect source_graph source_root bits (SDec i) -> i<11.
Proof.
  intro Sel. pose proof (selected_atom_bounded _ _ _ _ source_live_register_certificate Sel) as B.
  cbn [bounded_atom] in B. now apply Nat.ltb_lt.
Qed.

Lemma repair_unpadded_step_zero_suffix a b : SourceStep a b -> 11<=length (snd a) ->
  exists k, skipn 11 (snd b)=skipn 11 (snd a)++repeat 0 k /\ length (snd a)<=length (snd b).
Proof.
  intros S Len. destruct S as [w before v after out count Sel Ret|
                 w before after out count Sel Ret|
                 w before v after out count Sel Ret|
                 w k out count rs Sel Ret|
                 w k out count rs Sel Ret]; cbn [snd] in *.
  - pose proof (repair_selected_inc_bounded _ _ Sel) as Bound.
    exists 0. cbn [repeat]. rewrite app_nil_r. split.
    + now apply skipn_register_replace.
    + rewrite !app_length. cbn. lia.
  - exists 0. cbn [repeat]. rewrite app_nil_r. split; [reflexivity|lia].
  - pose proof (repair_selected_dec_bounded _ _ Sel) as Bound.
    exists 1. split.
    + replace (before++v::(after++[0])) with ((before++v::after)++[0])
        by (rewrite <- app_assoc; reflexivity).
      rewrite skipn_app.
      assert (Z : 11-length(before++v::after)=0).
      { apply Nat.sub_0_le. rewrite length_app in *. cbn in *. lia. }
      rewrite Z. change (skipn 11 (before++v::after) ++ [0] =
        skipn 11 (before++S v::after) ++ [0]).
      rewrite (skipn_register_replace before (S v) after v) by assumption. reflexivity.
    + rewrite !app_length. cbn. rewrite app_length. cbn. lia.
  - exists 0. cbn [repeat]. rewrite app_nil_r. split; [reflexivity|lia].
  - exists 0. cbn [repeat]. rewrite app_nil_r. split; [reflexivity|lia].
Qed.

Theorem repair_source_step_zero_suffix a b : SourceProgramStep a b -> 11<=length (snd a) ->
  exists k, skipn 11 (snd b)=skipn 11 (snd a)++repeat 0 k /\ length (snd a)<=length (snd b).
Proof.
  intros H Len. destruct H as [pc pad registers target S].
  exact (repair_unpadded_step_zero_suffix _ _ S Len).
Qed.

Theorem repair_source_runs_zero_suffix a b : SourceProgramRuns a b -> 11<=length (snd a) ->
  exists k, skipn 11 (snd b)=skipn 11 (snd a)++repeat 0 k /\ length (snd a)<=length (snd b).
Proof.
  intro R. induction R as [s|s t u S R IH]; intro Len.
  - exists 0. cbn [repeat]. rewrite app_nil_r. split; [reflexivity|lia].
  - destruct (repair_source_step_zero_suffix _ _ S Len) as [k [E L]].
    destruct (IH ltac:(lia)) as [m [F M]]. exists (k+m). split; [|lia].
    rewrite F,E,<-app_assoc,repeat_app. reflexivity.
Qed.
Print Assumptions source_live_register_certificate.
Print Assumptions repair_source_step_zero_suffix.
Print Assumptions repair_source_runs_zero_suffix.
