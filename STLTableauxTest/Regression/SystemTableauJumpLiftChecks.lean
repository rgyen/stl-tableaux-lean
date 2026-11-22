import STLTableaux.Automata.Composition.SystemTableauJumpLift
import STLTableaux.Automata.Recognition.EmptyContinuationRecognition
import STLTableaux.Semantics.Partitions.SingletonBoundaryPartition

/-! The actual finite atomic-root graph admits the atomic initial singleton
and its existing empty continuation. A no-jump ramp system idles during the
monitor-only singleton jump, then executes its actual positive flow. The
concrete full one-flow product trajectory retains its initial singleton goal;
this is not a general whole-run theorem. -/
namespace SystemTableauJumpLiftChecks
open STLTableau STLTableau.HybridAutomaton
open STLTableau.Section4 STLTableau.Section4.Finiteness
open Section3

def p : AtomicProposition Unit := ⟨1, fun _ => (), fun v => -v 0, .ge⟩
def root : Formula.NormalizedInput Unit := ⟨.atom p, .atom p⟩
noncomputable def T := withEmptyContinuation (Clock := Nat) Set.univ root
theorem ready : T.TranslationReady :=
  withEmptyContinuation_ready _ _
    (finiteRootTableau_translationReady Set.univ Set.finite_univ root.val (by simp))
def S : Section3.StateForm Nat Unit := .ofLocal (.predicate (.plain (.atom p)))
def Q : Section3.TransitionForm Nat Unit := .ofState S
def l0 : EdgeLabel Nat := JudgementTableau.incoming Q

theorem derives : Derives S Q := by
  have norm : SafeNormalization (.predicate (.plain (.atom p))) Q := .predicate _
  have proj : Q.atomicProjection = Q := by
    have locals : {l ∈ S.locals | Section3.TransitionForm.KeepAtomic l} = S.locals := by
      ext l
      constructor
      · exact And.left
      · intro h
        refine ⟨h, ?_⟩
        have same : l = Local.predicate (.plain (.atom p)) := h
        subst l
        trivial
    unfold Section3.TransitionForm.atomicProjection Section3.TransitionForm.restrictCurrent Q
    simp only [Section3.TransitionForm.ofState, locals]
  apply Derives.resolved (Resolve.leaf (ResolutionLeaf.atomic (.plain (.atom p)) trivial)) norm norm
  rw [proj]
  exact norm

theorem inventory : FiniteInventory.TransitionWithin
    (FiniteInventory.locals (Finiteness.rootPlainFormulas root.val)
      (rootSlotTriples (Clock := Nat) root.val))
    (FiniteInventory.guards (rootSlotTriples (Clock := Nat) root.val))
    (FiniteInventory.resets (rootSlotTriples (Clock := Nat) root.val)) Q := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro l hl
      change l = .predicate (.plain (.atom p)) at hl
      subst l
      classical
      simp [FiniteInventory.locals, Finiteness.rootPlainFormulas, root]
    · intro g hg; exact hg.elim
    · intro c a h; cases h
  · intro N h; cases h

theorem original_initial : (l0, Q) ∈ T.initial :=
  ⟨⟨derives, rfl⟩, ⟨⟨S, derives⟩, inventory⟩⟩
def q0 : T.states := ⟨Q, ready.initial_states _ original_initial⟩
def q1 : T.states := ⟨emptyMode, Or.inl rfl⟩
theorem source_has_atom : Local.predicate (.plain (.atom p)) ∈ T.label q0.val :=
  ⟨rfl, trivial⟩

theorem original_final : Q ∈ (inputTableau (Clock := Nat) Set.univ root).final :=
  ⟨rfl, ⟨⟨S, derives⟩, inventory⟩⟩

theorem original_edge : (q0.val, emptyIncoming, q1.val) ∈ T.edges := by
  apply final_empty_edge Set.univ root Q original_final
  intro h
  have := congrArg (fun F : Section3.TransitionForm Nat Unit => F.current.locals) h
  have atom : Local.predicate (.plain (.atom p)) ∈ Q.current.locals := rfl
  rw [this] at atom
  exact atom.elim

def H : HybridAutomaton Unit Unit Unit where
  modes_finite := inferInstance
  variables_finite := inferInstance
  edge := ∅
  initial := {s | s.2 () = 0}
  invariant := Set.univ
  flow := fun s t v => ∀ x, v x = s.2 x + t
  trajectory_closed := HybridFlow.Closed.of_rebase_add _ _
    (by intro q v a b r s first total x
        dsimp only [Prod.snd] at *
        rw [total x, first x]; push_cast; ring)
    (by intro q v a b r s first second x
        dsimp only [Prod.snd] at *
        rw [second x, first x]; push_cast; ring)
  jump := fun _ _ _ => False
def zeroState : H.State := ⟨((), fun _ => 0), Set.mem_univ _⟩
def oneState : H.State := ⟨((), fun _ => 1), Set.mem_univ _⟩
noncomputable def σ : FiniteSignal Unit := ⟨1, by norm_num, fun t _ => t.val⟩
theorem atom_only_initial (t : σ.Time) : σ.Satisfies root.val t ↔ t.val = 0 := by
  change -t.val ≥ 0 ↔ t.val = 0
  constructor
  · intro h; linarith [t.property.1]
  · intro h; simp [h]
noncomputable def direct : H.PrelimExecution σ where
  count := 1
  nonempty := by decide
  initialState := zeroState
  initial_mem := rfl
  start := fun _ => zeroState
  finish := fun _ => oneState
  boundary := fun i => i.val
  first_zero := by norm_num
  increasing := by
    intro i j hij
    change (i.val : ℝ) < (j.val : ℝ)
    exact_mod_cast (show i.val < j.val from hij)
  last_le_horizon := by norm_num [σ]
  duration := fun _ => 1
  duration_eq := by intro i; fin_cases i; norm_num
  curve := fun _ t _ => t.val
  continuousStep := fun _ => ⟨rfl, rfl, rfl, fun _ =>
    ⟨fun _ => by simp [zeroState]; rfl, Set.mem_univ _⟩⟩
  initialSteps := .refl
  discreteSteps := by intro i hi; have := i.isLt; omega
  signal_eq := by intro i t ht; fin_cases i; funext x; simp [σ]
noncomputable def f : ObservedFlow H σ where
  start := zeroState
  finish := oneState
  beginTime := 0
  endTime := 1
  duration := 1
  positive := by norm_num
  duration_eq := by norm_num
  curve := fun t _ => t.val
  step := direct.continuousStep ⟨0, by decide⟩
  observe := by intro t ht; funext x; simp [σ]
theorem continuous_flows : H.ContinuousFlows := by
  intro q r γ evolves
  apply continuous_pi
  intro x
  have same : (fun t => γ t x) = fun t => γ ⟨0, by simp⟩ x + t.val := by
    funext t
    exact (evolves t).1 x
  rw [same]
  exact continuous_const.add continuous_subtype_val

def bs : Fin 3 → ℝ := ![0, 0, 1]
def ms : Fin 3 → Marker := ![●, ○, ●]
def P : IntervalPartition σ.domain :=
  IntervalPartition.ofSingletonBoundaries bs
    (by intro i j hij; change i.val ≤ j.val at hij
        fin_cases i <;> fin_cases j <;> norm_num [bs] at *)
    ms (by intro i hi; fin_cases i <;> norm_num [ms, bs] at *) rfl rfl

theorem source_labels (β : ClockValuation Nat) : ∀ loc ∈ T.label q0.val,
    loc.holds σ P β ⟨0, by decide⟩ := by
  intro loc hl
  change loc ∈ JudgementTableau.labels Q at hl
  have same : loc = Local.predicate (.plain (.atom p)) := hl.1
  subst loc
  change ∀ t : σ.Time, t.val ∈ P.interval ⟨0, by decide⟩ → -t.val ≥ 0
  intro t ht
  have hz : t.val = 0 := by
    have h : 0 ≤ t.val ∧ (t.val < 0 ∨ t.val = 0) := by
      simpa [P, IntervalPartition.ofSingletonBoundaries,
        IntervalPartition.markedBoundaryPiece, MarkedInterval.mem_iff, bs, ms] using ht
    rcases h.2 with hneg | heq
    · linarith [h.1]
    · exact heq
  simp [hz]

theorem empty_labels : T.label q1.val = ∅ := empty_label Set.univ root

theorem actual_initial_singleton_jump_and_flow :
    ∃ a b c : (T.systemTableauAutomaton H ready σ.horizon).State,
      a.val ∈ (T.systemTableauAutomaton H ready σ.horizon).initial ∧
      H.leftStateOn (T.prelimAutomaton ready σ.horizon)
        T.systemVarName T.tableauVarName a = zeroState ∧
      H.leftStateOn (T.prelimAutomaton ready σ.horizon)
        T.systemVarName T.tableauVarName b = zeroState ∧
      H.leftStateOn (T.prelimAutomaton ready σ.horizon)
        T.systemVarName T.tableauVarName c = oneState ∧
      (H.rightStateOn (T.prelimAutomaton ready σ.horizon)
        T.systemVarName T.tableauVarName a).val.1 = q0 ∧
      (T.systemTableauAutomaton H ready σ.horizon).DiscreteStep a b ∧
      ∃ γ, (T.systemTableauAutomaton H ready σ.horizon).ContinuousStep b c f.duration γ := by
  obtain ⟨a, b, c, init, left, middle, right, source, jump, step⟩ :=
    T.systemTableau_initial_singleton_to_cell H ready direct rfl f rfl
      continuous_flows P (by decide) (by change (0 : ℝ) - 0 = 0; norm_num)
      rfl rfl q0 q1 l0 emptyIncoming original_initial original_edge (fun _ => 0)
      (by intro g hg; exact hg.elim) (source_labels _)
      (by intro g hg; exact hg.elim)
      (by intro loc hl; rw [empty_labels] at hl; exact hl.elim)
      (by intro a ha; rw [empty_labels] at ha; exact ha.elim)
      (by intro a ha; rw [empty_labels] at ha; exact ha.elim)
  exact ⟨a, b, c, init, left, middle, right, source, jump, _, step⟩

/-- Preserve the actual original goal at the initial singleton while the
product takes its monitor-only jump and then realizes the full ramp signal. -/
theorem actual_product_full_initial_goal :
    ∃ (aug : FiniteSignal T.CompositionVar)
      (e : (T.systemTableauAutomaton H ready σ.horizon).PrelimExecution aug),
      e.ReachesHorizon ∧
      e.initialState ∈ T.systemTableauGoal H ready σ.horizon ∧
      e.VisitsState e.initialState ∧
      ∀ (t : aug.Time) (x : Unit), aug.value t (T.systemCoordinate x) = t.val := by
  obtain ⟨a, b, c, init, _, middle, _, source, jump, γ, step⟩ :=
    actual_initial_singleton_jump_and_flow
  let aug : FiniteSignal T.CompositionVar :=
    ⟨1, by norm_num, fun t => γ ⟨t.val, t.property.1, t.property.2.le⟩⟩
  let e : (T.systemTableauAutomaton H ready σ.horizon).PrelimExecution aug := {
    count := 1
    nonempty := by decide
    initialState := a
    initial_mem := init
    start := fun _ => b
    finish := fun _ => c
    boundary := fun i => i.val
    first_zero := by norm_num
    increasing := by
      intro i j hij
      change (i.val : ℝ) < (j.val : ℝ)
      exact_mod_cast (show i.val < j.val from hij)
    last_le_horizon := by norm_num [aug]
    duration := fun _ => 1
    duration_eq := by intro i; fin_cases i; norm_num
    curve := fun _ => γ
    continuousStep := fun _ => step
    initialSteps := .single jump
    discreteSteps := by intro i hi; have := i.isLt; omega
    signal_eq := by
      intro i t ht
      fin_cases i
      change γ _ = γ _
      congr 1
      apply Subtype.ext
      simp }
  refine ⟨aug, e, ?_, ?_, ?_, ?_⟩
  · unfold PrelimExecution.ReachesHorizon
    dsimp only [e]
    norm_num [aug]
  · change H.rightStateOn (T.prelimAutomaton ready σ.horizon)
      T.systemVarName T.tableauVarName a ∈ T.prelimGoal ready σ.horizon
    apply Or.inl
    change (H.rightStateOn (T.prelimAutomaton ready σ.horizon)
      T.systemVarName T.tableauVarName a).val.1.val ∈ T.final
    rw [source]
    exact Or.inr original_final
  · exact Or.inr (Or.inl ⟨.refl, .single jump⟩)
  · intro t x
    let u : Set.Icc (0 : ℝ) f.duration := ⟨t.val, t.property.1, t.property.2.le⟩
    have flow := ((H.parallelOn_continuous_left (T.prelimAutomaton ready σ.horizon)
      T.systemVarName T.tableauVarName step).2.2.2 u).1 x
    rw [middle] at flow
    change γ u (T.systemCoordinate x) = 0 + t.val at flow
    simpa only [zero_add] using flow

run_elab do
  for name in #[``derives, ``inventory, ``original_initial, ``original_final,
      ``original_edge, ``source_has_atom, ``atom_only_initial,
      ``source_labels, ``actual_initial_singleton_jump_and_flow,
      ``actual_product_full_initial_goal] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end SystemTableauJumpLiftChecks
