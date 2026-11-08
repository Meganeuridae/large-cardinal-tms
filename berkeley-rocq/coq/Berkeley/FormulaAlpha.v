(** Semantic meaning of the checked de Bruijn equality. Holes in this
    auxiliary syntax semantics are rigid propositions; the Berkeley use is
    separately checked to contain neither holes nor parameter variables. *)
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool.
From Berkeley Require Import Syntax ProofFormula FormulaSemantics.
Import ListNotations.

Definition update_name {D : Type} (rho:variable->D) x a y :=
  if var_eqb y x then a else rho y.
Fixpoint SynHolds {D : Type} (R:D->D->Prop) (holes:nat->Prop) (rho:variable->D) f : Prop :=
  match f with
  | Atom b x y => if b then R (rho x) (rho y) else rho x=rho y
  | Neg p => ~SynHolds R holes rho p
  | Imp p q => SynHolds R holes rho p -> SynHolds R holes rho q
  | All x p => forall a, SynHolds R holes (update_name rho x a) p
  | Hole n => holes n
  end.
Theorem SynHolds_ext {D} (R:D->D->Prop) holes f rho sigma :
  (forall x,rho x=sigma x) -> (SynHolds R holes rho f <-> SynHolds R holes sigma f).
Proof.
  revert rho sigma. induction f as [b x y|p IH|p IH q JH|x p IH|n]; intros rho sigma E; cbn [SynHolds].
  - now rewrite !E.
  - now rewrite (IH rho sigma E).
  - now rewrite (IH rho sigma E),(JH rho sigma E).
  - split; intros H a; specialize (IH (update_name rho x a) (update_name sigma x a)).
    + apply (proj1 (IH ltac:(intro n; unfold update_name; destruct (var_eqb n x); auto))). apply H.
    + apply (proj2 (IH ltac:(intro n; unfold update_name; destruct (var_eqb n x); auto))). apply H.
  - tauto.
Qed.
Definition db_value {D} (rho:variable->D) default (values:list D) x :=
  match x with Bound n => nth n values default | Free x => rho x end.
Fixpoint DBHolds {D} (R:D->D->Prop) holes (rho:variable->D) default (values:list D) f : Prop :=
  match f with
  | DBAtom b x y => if b then R (db_value rho default values x) (db_value rho default values y)
                           else db_value rho default values x=db_value rho default values y
  | DBNeg p => ~DBHolds R holes rho default values p
  | DBImp p q => DBHolds R holes rho default values p -> DBHolds R holes rho default values q
  | DBAll p => forall a, DBHolds R holes rho default (a::values) p
  | DBHole n => holes n
  end.
Definition overlay {D} names (values:list D) (rho:variable->D) default x :=
  match index x names with Some n => nth n values default | None => rho x end.
Lemma overlay_cons {D} names (values:list D) rho default x a y :
  overlay (x::names) (a::values) rho default y = update_name (overlay names values rho default) x a y.
Proof.
  unfold overlay,update_name. cbn [index].
  destruct (var_eqb y x); [reflexivity|]. destruct (index y names); reflexivity.
Qed.
Lemma canonical_value {D} names (values:list D) rho default x :
  db_value rho default values (db_name x names)=overlay names values rho default x.
Proof. unfold db_value,db_name,overlay. destruct (index x names); reflexivity. Qed.
Theorem canonical_semantics {D} (R:D->D->Prop) holes default f names values rho :
  SynHolds R holes (overlay names values rho default) f <->
  DBHolds R holes rho default values (canonical f names).
Proof.
  revert names values rho. induction f as [b x y|p IH|p IH q JH|x p IH|n]; intros names values rho;
    cbn [SynHolds canonical DBHolds].
  - now rewrite !canonical_value.
  - now rewrite IH.
  - now rewrite IH,JH.
  - split; intros H a.
    + apply (proj1 (IH (x::names) (a::values) rho)).
      apply (proj2 (SynHolds_ext R holes p
        (overlay (x::names) (a::values) rho default)
        (update_name (overlay names values rho default) x a)
        (overlay_cons names values rho default x a))). apply H.
    + apply (proj1 (SynHolds_ext R holes p
        (overlay (x::names) (a::values) rho default)
        (update_name (overlay names values rho default) x a)
        (overlay_cons names values rho default x a))).
      apply (proj2 (IH (x::names) (a::values) rho)). apply H.
  - tauto.
Qed.
Theorem canonical_equality_sound {D} (R:D->D->Prop) holes rho f g :
  canonical f []=canonical g [] -> (SynHolds R holes rho f <-> SynHolds R holes rho g).
Proof.
  intro E. pose proof (canonical_semantics R holes (rho (V 0)) f [] [] rho) as F.
  pose proof (canonical_semantics R holes (rho (V 0)) g [] [] rho) as G.
  cbn [overlay index] in F,G. rewrite E in F. tauto.
Qed.

Definition plain_variable x := match x with V _ => true | P _ => false end.
Fixpoint plain_formula f :=
  match f with
  | Atom _ x y => plain_variable x && plain_variable y
  | Neg p => plain_formula p
  | Imp p q => plain_formula p && plain_formula q
  | All x p => plain_variable x && plain_formula p
  | Hole _ => false
  end.
Definition plain_var x := match x with V n => n | P _ => 0 end.
Fixpoint plain_projection f :=
  match f with
  | Atom b x y => if b then FMember (plain_var x) (plain_var y) else FEqual (plain_var x) (plain_var y)
  | Neg p => FNeg (plain_projection p)
  | Imp p q => FImp (plain_projection p) (plain_projection q)
  | All x p => FAll (plain_var x) (plain_projection p)
  | Hole _ => FEqual 0 0
  end.
Lemma plain_semantics {D} (R:D->D->Prop) holes f rho : plain_formula f=true ->
  (SynHolds R holes rho f <-> FolHolds R (fun n => rho(V n)) (plain_projection f)).
Proof.
  revert rho. induction f as [b x y|p IH|p IH q JH|x p IH|n]; intros rho Good;
    cbn [plain_formula] in Good; cbn [SynHolds plain_projection].
  - destruct x,y; try discriminate. destruct b; reflexivity.
  - cbn [FolHolds]. now rewrite IH by exact Good.
  - apply andb_true_iff in Good as [Gp Gq]. cbn [FolHolds]. now rewrite IH,JH by assumption.
  - destruct x as [x|x]; [|discriminate]. cbn in Good. cbn [plain_var FolHolds].
    split; intros H a.
    + apply (proj1 (IH (update_name rho (V x) a) Good)),H.
    + apply (proj2 (IH (update_name rho (V x) a) Good)),H.
  - discriminate.
Qed.

Print Assumptions canonical_semantics.
Print Assumptions canonical_equality_sound.
Print Assumptions plain_semantics.
