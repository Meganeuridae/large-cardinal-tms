(** Nonvacuity consequences of the separately checked internal Berkeley
    interpretation. The model and classical reasoning are explicit premises;
    this module does not identify external with internal elementarity. *)
From Stdlib Require Import Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxZFBase BerkeleySyntaxSetupFinal
  BerkeleySyntaxZFEnvironments BerkeleySyntaxSatisfactionExists
  BerkeleySyntaxSentence BerkeleySyntaxUniform BerkeleySyntaxSets BerkeleySyntaxOmega
  BerkeleySyntaxEnvironment BerkeleySyntaxElementary BerkeleySyntaxFormulaSet
  BerkeleySyntaxSatisfactionSemantics BerkeleySyntaxZFConstant BerkeleySyntaxZFComposition
  BerkeleySyntaxFunction BerkeleySyntaxPairs BerkeleySyntaxWitnesses
  BerkeleySyntaxCardinal BerkeleySyntaxZFPaths BerkeleySyntaxZFTags.

Section Nonvacuity.
Context {D : Type} (R : D -> D -> Prop).
Variable EM : forall P : Prop, P \/ ~ P.
Variable Model : satisfies_zf_prefix R.

(** The implication defining uniform elementarity has an actual setup,
    environment set, and internal satisfaction graph in every such model. *)
Theorem uniform_elementarity_total_function j m :
  RelUniformElementary R j m -> RelFunction R j m m.
Proof.
  intro Uniform.
  destruct (@zf_formula_setup_exists D R EM Model m)
    as [w [te [tm [tn [ti [ta [f [Tags Formulas]]]]]]]].
  destruct (@zf_prefix_environments_exist D R EM Model w m) as [e Env].
  destruct (@zf_prefix_satisfaction_exists D R EM Model f e w m te tm tn ti ta Tags Formulas Env)
    as [sat Sat].
  unfold RelUniformElementary in Uniform.
  exact (proj1 (Uniform w te tm tn ti ta f e sat (conj Tags Formulas) Env Sat)).
Qed.

(** A nonempty domain supplies an actual formula and graph-related pair of
    assignments on which the preservation clause has been instantiated. *)
Theorem uniform_elementarity_has_nonempty_test j m a :
  R a m -> RelUniformElementary R j m ->
  exists f e w te tm tn ti ta sat p s t,
    RelSentenceSetup R w te tm tn ti ta f /\ RelEnvironments R e w m /\
    RelSatisfaction R sat e f w m te tm tn ti ta /\ R p f /\ R s e /\ R t e /\
    RelImageEnvironment R j s t w m /\
    (RelGraph R sat p s <-> RelGraph R sat p t).
Proof.
  intros A Uniform.
  destruct (@zf_formula_setup_exists D R EM Model m)
    as [w [te [tm [tn [ti [ta [f [Tags Formulas]]]]]]]].
  destruct (@zf_prefix_environments_exist D R EM Model w m) as [e Env].
  destruct (@zf_prefix_satisfaction_exists D R EM Model f e w m te tm tn ti ta Tags Formulas Env)
    as [sat Sat].
  pose proof (proj1 Tags) as Omega. destruct Omega as [[[z [Z Empty]] Succ] Least].
  destruct (proj1 Formulas) as [EqClosed Other].
  destruct (EqClosed z z Z Z) as [p [P Node]].
  destruct (@zf_prefix_constant_graph D R EM Model w m a A) as [s [Sfun Const]].
  assert (Sin : R s e) by (apply (proj2 (Env s)); exact Sfun).
  pose proof (Uniform w te tm tn ti ta f e sat (conj Tags Formulas) Env Sat) as [J Elem].
  destruct (@zf_prefix_graph_composition D R EM Model s j w m Sfun J) as [t [Tfun Image]].
  assert (Tin : R t e) by (apply (proj2 (Env t)); exact Tfun).
  pose proof (Elem p s t P Sin Tin Image) as Preserves.
  exists f,e,w,te,tm,tn,ti,ta,sat,p,s,t.
  split; [exact (conj Tags Formulas)|]. split; [exact Env|]. split; [exact Sat|].
  split; [exact P|]. split; [exact Sin|]. split; [exact Tin|].
  split; [exact Image|exact Preserves].
Qed.

(** The literal ordinal definition uses transitivity and linearity. Foundation
    rules out the finite membership cycles that would obstruct hereditary
    transitivity. Thus every member really is an ordinal as well. *)
Theorem ordinal_member_is_ordinal d k :
  RelOrdinal R d -> R k d -> RelOrdinal R k.
Proof.
  intros [Trans Linear] K. split.
  - unfold RelTransitive in *. intros x y X Y.
    assert (Xd : R x d) by (eapply Trans; eassumption).
    assert (Yd : R y d) by (eapply Trans; eassumption).
    destruct (Linear y k Yd K) as [[Yk|Eq]|Ky]; [exact Yk| |].
    + subst y. exfalso. eapply (zf_no_finite_membership_cycle R EM Model 2 k); [lia|].
      eapply path_step; [exact Y|]. eapply path_step; [exact X|constructor].
    + exfalso. eapply (zf_no_finite_membership_cycle R EM Model 3 k); [lia|].
      eapply path_step; [exact Ky|]. eapply path_step; [exact Y|].
      eapply path_step; [exact X|constructor].
  - unfold RelOrdinalLinear in *. intros x y X Y. apply Linear;
      unfold RelTransitive in Trans; eapply Trans; eassumption.
Qed.

Theorem critical_points_are_ordinals j k d eta :
  RelOrdinal R d -> RelCritical R j k d eta -> RelOrdinal R k /\ RelOrdinal R eta.
Proof.
  intros Ord [Kd [EtaK _]]. assert (Kord : RelOrdinal R k) by (eapply ordinal_member_is_ordinal; eassumption).
  split; [exact Kord|eapply ordinal_member_is_ordinal; eassumption].
Qed.

(** If m contains d and is transitive, a critical-point witness really moves
    a member of m; it cannot merely exploit a missing or partial function. *)
Theorem critical_witness_moves_member j k d eta m :
  RelTransitive R m -> R d m -> RelCritical R j k d eta ->
  RelUniformElementary R j m ->
  exists image, R k m /\ R image m /\ RelGraph R j k image /\ image <> k.
Proof.
  intros Trans Dm [Kd [EtaK [NotFixed Fixed]]] Uniform.
  assert (Km : R k m) by (unfold RelTransitive in Trans; eapply Trans; eassumption).
  destruct (uniform_elementarity_total_function j m Uniform) as [_ Total].
  destruct (Total k Km) as [image [In [At Unique]]].
  exists image. repeat split; try assumption. intro E. subst image. contradiction.
Qed.

(** The universal quantification over transitive containers is nonempty:
    the ordinal successor d union {d} is such a container. *)
Theorem ordinal_has_transitive_container d :
  RelOrdinal R d -> exists m, R d m /\ RelTransitive R m.
Proof.
  intros [Trans Linear]. destruct (@zf_prefix_successor_exists D R EM Model d) as [m Succ].
  exists m. split.
  - apply (proj2 (Succ d)). now right.
  - unfold RelTransitive in *. intros x y Xm Yx.
    apply (proj1 (Succ x)) in Xm as [Xd|Eq].
    + apply (proj2 (Succ y)). left. eapply Trans; eassumption.
    + subst x. apply (proj2 (Succ y)). now left.
Qed.

(** Even before appealing to any interpretation of external elementarity,
    the internal property entails an actual nonidentity total graph. *)
Theorem uniform_berkeley_has_moved_member :
  RelUniformBerkeley R ->
  exists m j k image, R k m /\ R image m /\ RelGraph R j k image /\ image <> k.
Proof.
  intros [w [d [Omega [Card [Wd Scope]]]]].
  destruct Card as [Ord Cardinal]. destruct Ord as [Trans Linear].
  destruct Omega as [[[eta [Etaw Empty]] Succ] Least].
  assert (EtaD : R eta d) by (unfold RelTransitive in Trans; eapply Trans; eassumption).
  destruct (ordinal_has_transitive_container d (conj Trans Linear)) as [m [Dm Tm]].
  destruct (Scope m Tm Dm eta EtaD) as [j [k [Critical Uniform]]].
  destruct (critical_witness_moves_member j k d eta m Tm Dm Critical Uniform) as [image Moved].
  now exists m,j,k,image.
Qed.
End Nonvacuity.

Print Assumptions uniform_elementarity_total_function.
Print Assumptions uniform_elementarity_has_nonempty_test.
Print Assumptions ordinal_member_is_ordinal.
Print Assumptions critical_points_are_ordinals.
Print Assumptions critical_witness_moves_member.
Print Assumptions ordinal_has_transitive_container.
Print Assumptions uniform_berkeley_has_moved_member.
