import STLTableaux.Automata.Composition.SystemTableauRunAssembly

/-! Pack the constructed product path into the actual flow-ending
execution, keeping the original SYSTEM signal on every physical coordinate.
An early goal gives a prefix; the signal's horizon does not assert that this
constructed product execution continues past its last flow. -/
namespace STLTableau.Section4.Tableau
open Section3 HybridAutomaton
variable {Clock Var State Mode Label : Type*} (T : Tableau Clock Var State)

theorem systemSignal_eq_of_projection (σ : FiniteSignal Var)
    (aug : FiniteSignal T.CompositionVar) (horizon : aug.horizon = σ.horizon)
    (projects : ∀ (t : aug.Time) (u : σ.Time), t.val = u.val →
      ∀ x, aug.value t (T.systemCoordinate x) = σ.value u x) :
    T.systemSignal aug = σ := by
  rcases σ with ⟨τ, positive, values⟩
  rcases aug with ⟨r, rpositive, augmented⟩
  dsimp only at horizon
  subst r
  dsimp only [systemSignal, FiniteSignal.reindex]
  congr 1
  funext t x
  exact projects t t rfl x

variable (H : HybridAutomaton Mode Label Var) (h : T.TranslationReady)

/-- Construct a goal-reaching product prefix from the GIVEN recognized
tableau path and actual SYSTEM flows. No product execution is assumed. -/
theorem systemTableau_forward_of_recognized {σ : FiniteSignal Var}
    (e : H.PrelimExecution σ) (full : e.ReachesHorizon)
    (direct : e.initialState = e.start ⟨0, e.nonempty⟩)
    (R : IntervalPartition σ.domain) (fine : R.FinerThan (e.fullFlowPartition full))
    (actions : ∀ (i j : Fin R.size), i.val + 1 = j.val →
      e.cellExitState full R fine i = e.cellEntryState full R fine j ∨
        H.DiscreteStep (e.cellExitState full R fine i) (e.cellEntryState full R fine j))
    (φ : Formula Var) (hw : SignalAtomRightContinuous σ φ)
    (flows : H.ContinuousFlows)
    (functions : ∀ a, Formula.IsSubformula (.atom a) φ → Continuous a.function)
    (finite : ∀ q, (T.label q).Finite) (recognized : T.recognizes finite σ R)
    (input : ∀ (q : T.states) a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      a.relation = .ge ∧ Formula.IsSubformula (.atom a) φ)
    (empty : T.states) (heGoal : empty ∈ T.goalModes) (heLab : T.label empty.val = ∅)
    (continuation : ∀ f : T.states, f ∈ T.goalModes → f ≠ empty →
      ∃ l : EdgeLabel Clock, (f.val, l, empty.val) ∈ T.edges ∧ l.guards = ∅ ∧
        l.resets = ClockResetSet.empty) :
    ∃ aug, T.systemSignal aug = σ ∧
      (T.systemTableauAutomaton H h σ.horizon).PrelimReachesState aug
        (T.systemTableauGoal H h σ.horizon) := by
  obtain ⟨p, run, accepting, allα⟩ := recognized
  let α : ClockValuation Clock := fun _ => 0
  have size := R.size_pos_of_domain_nonempty
    (show σ.domain.Nonempty from ⟨0, le_rfl, σ.horizon_pos⟩)
  let i : Fin R.size := ⟨0, size⟩
  let q : T.states := ⟨p.firstState, by cases p <;> first | exact run.1 | exact run.1.1⟩
  have sat := allα α
  have head : (∀ g ∈ p.firstIncoming.guards, g.holds α) ∧
      ∀ loc ∈ T.label q.val, loc.holds σ R (p.firstIncoming.resets.apply α)
        ⟨0, by omega⟩ := by
    cases p <;> first | exact sat | exact sat.1
  obtain ⟨monitor, initial, entry⟩ := T.initial_piece h σ R size q p.firstIncoming
    run.2 α head.1 head.2
  have starts : e.cellEntryState full R fine i = e.initialState :=
    (e.first_cell_entry full R fine size).trans direct.symm
  have agree : ∀ x : T.realVariables,
      (e.cellEntryState full R fine i).val.2 x.val = monitor.val.2 (.inl (.inl x)) := by
    intro x
    rw [entry]
    change (e.cellEntryState full R fine i).val.2 x.val = σ.value (pieceEntry σ R i) x.val
    exact congrFun (e.cell_entry_signal full R fine i).symm x.val
  let first := T.joinState H h σ.horizon (e.cellEntryState full R fine i) monitor agree
  have firstInitial : first.val ∈ (T.systemTableauAutomaton H h σ.horizon).initial := by
    exact T.joinState_initial H h σ.horizon _ _ agree (starts.symm ▸ e.initial_mem) initial
  have plan := T.trace_to_system_word H h e full R fine actions φ hw input flows
    functions finite empty heGoal heLab continuation p accepting i α sat first
    (T.joinState_system H h σ.horizon _ _ agree)
    ((congrArg Subtype.val (T.joinState_tableau H h σ.horizon _ _ agree)).trans entry)
  obtain ⟨a, b, stop, lead, ⟨word⟩, bound, goal⟩ := plan
  have zero : (R.interval i).left = 0 := R.first_left_eq_domain_left size σ.horizon_pos
  obtain ⟨aug, out, horizon, projects, _, _, final, _, _, _⟩ := word.toExecution
    (fun v => T.joinValuation v (fun _ => 0)) (fun _ _ => rfl)
    first firstInitial zero lead bound
  exact ⟨aug, T.systemSignal_eq_of_projection σ aug horizon projects,
    out, out.finalState, final.symm ▸ goal, out.visits_finalState⟩

/-- All local connection and regularity premises are derived from the actual
bounded SYSTEM execution. The original flow, invariant and initial sets are
unchanged by the bounded zero-time extension. -/
theorem systemTableau_forward_of_bounded_recognized {σ : FiniteSignal Var}
    (e : H.PrelimExecution σ) (full : e.ReachesHorizon)
    (direct : e.initialState = e.start ⟨0, e.nonempty⟩)
    (n : ℕ) (bound : ∀ (k : Fin e.count) (live : k.val + 1 < e.count),
      H.BoundedZeroTime n (e.finish k) (e.start ⟨k.val + 1, live⟩))
    (R : IntervalPartition σ.domain) (fine : R.FinerThan (e.fullFlowPartition full))
    (φ : Formula Var) (flows : H.ContinuousFlows)
    (functions : ∀ a, Formula.IsSubformula (.atom a) φ → Continuous a.function)
    (finite : ∀ q, (T.label q).Finite) (recognized : T.recognizes finite σ R)
    (input : ∀ (q : T.states) a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      a.relation = .ge ∧ Formula.IsSubformula (.atom a) φ)
    (empty : T.states) (heGoal : empty ∈ T.goalModes) (heLab : T.label empty.val = ∅)
    (continuation : ∀ f : T.states, f ∈ T.goalModes → f ≠ empty →
      ∃ l : EdgeLabel Clock, (f.val, l, empty.val) ∈ T.edges ∧ l.guards = ∅ ∧
        l.resets = ClockResetSet.empty) :
    ∃ aug, T.systemSignal aug = σ ∧
      (T.systemTableauAutomaton (H.boundedZeroTimeExtension n) h σ.horizon).PrelimReachesState
        aug (T.systemTableauGoal (H.boundedZeroTimeExtension n) h σ.horizon) := by
  have flowWise := e.wellBehaved_of_continuousFlows φ flows functions
  have hw := flowWise.signalAtomRightContinuous full
  exact T.systemTableau_forward_of_recognized (H.boundedZeroTimeExtension n) h
    (e.inZeroTimeExtension H n) full direct R fine (e.extended_cell_action full R fine n bound)
    φ hw flows functions finite recognized input empty heGoal heLab continuation

run_elab do
  for name in #[``systemSignal_eq_of_projection, ``systemTableau_forward_of_recognized,
      ``systemTableau_forward_of_bounded_recognized] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax}"
end STLTableau.Section4.Tableau
