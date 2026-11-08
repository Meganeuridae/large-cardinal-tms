(** First-eleven register discipline and exact zero-suffix growth for any
    finite execution of the extracted source DAG. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import RuntimeTraces RuntimePC CompilerExecution CompilerInstance CompilerRegisters.
Import ListNotations.

Lemma skipn_set_below n i v rs : i<n ->
  skipn n (set_register i v rs) = skipn n rs.
Proof.
  revert i rs. induction n as [|n IH]; intros [|i] [|x rs] H;
    cbn [set_register skipn] in *; try lia; try reflexivity.
  apply IH. lia.
Qed.

Lemma skipn_register_replace (before : list nat) (old : nat) (after : list nat) (value : nat) : length before<11 ->
  skipn 11 (before++value::after) = skipn 11 (before++old::after).
Proof.
  intro B. rewrite <- (set_register_split before old after value).
  now apply skipn_set_below.
Qed.

Theorem ir_step_zero_suffix a b : IRStep a b -> 11<=length (snd a) ->
  exists k, skipn 11 (snd b) = skipn 11 (snd a) ++ repeat 0 k /\
            length (snd a) <= length (snd b).
Proof.
  intros S Len. pose proof (ir_step_register_count _ _ S) as Count.
  destruct S; cbn [snd] in *.
  - exists 0. cbn [repeat]. rewrite app_nil_r. split; [|exact Count].
    now apply skipn_register_replace.
  - exists 0. cbn [repeat]. rewrite app_nil_r. split; [reflexivity|exact Count].
  - exists 1. split; [|exact Count].
    replace (before++v::(after++[0])) with ((before++v::after)++[0])
      by (rewrite <- app_assoc; reflexivity).
    rewrite skipn_app.
    assert (Z : 11-length(before++v::after)=0).
    { apply Nat.sub_0_le. rewrite length_app in *. cbn in *. lia. }
    rewrite Z.
    change (skipn 11 (before++v::after) ++ [0] =
            skipn 11 (before++S v::after) ++ [0]).
    rewrite (skipn_register_replace before (S v) after v) by assumption.
    reflexivity.
  - exists 0. cbn [repeat]. rewrite app_nil_r. split; [reflexivity|exact Count].
  - exists 0. cbn [repeat]. rewrite app_nil_r. split; [reflexivity|exact Count].
Qed.

Theorem source_step_zero_suffix a b : SourceProgramStep a b -> 11<=length (snd a) ->
  exists k, skipn 11 (snd b) = skipn 11 (snd a) ++ repeat 0 k /\
            length (snd a) <= length (snd b).
Proof.
  intros H L. destruct H as [w n rs b S].
  apply source_step_implies_ir in S.
  exact (ir_step_zero_suffix _ _ S L).
Qed.

Theorem source_runs_zero_suffix a b : SourceProgramRuns a b -> 11<=length (snd a) ->
  exists k, skipn 11 (snd b) = skipn 11 (snd a) ++ repeat 0 k /\
            length (snd a) <= length (snd b).
Proof.
  intro R. induction R as [s|s t u S R IH]; intro Len.
  - exists 0. cbn [repeat]. rewrite app_nil_r. split; [reflexivity|lia].
  - destruct (source_step_zero_suffix _ _ S Len) as [k [E L]].
    destruct (IH ltac:(lia)) as [m [F M]].
    exists (k+m). split; [|lia].
    rewrite F,E,<-app_assoc,repeat_app. reflexivity.
Qed.
Print Assumptions ir_step_zero_suffix.
Print Assumptions source_runs_zero_suffix.
