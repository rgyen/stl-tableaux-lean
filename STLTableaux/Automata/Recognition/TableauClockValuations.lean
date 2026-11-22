import STLTableaux.Automata.Recognition.TableauDiscreteCorrespondence

/-! Real automaton coordinates versus nonnegative tableau clock valuations.
Compatibility is explicit: unrestricted initial real coordinates are not
silently assumed nonnegative. -/
namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)

def ClockCompatible (v : T.HAVar → ℝ) (α : ClockValuation Clock) : Prop :=
  ∀ c : T.clocks, v (.inr (.inl c)) = (α c.val : ℝ)

def ClocksNonnegative (v : T.HAVar → ℝ) : Prop :=
  ∀ c : T.clocks, 0 ≤ v (.inr (.inl c))

theorem clockCompatible_nonnegative {v : T.HAVar → ℝ} {α : ClockValuation Clock}
    (hv : T.ClockCompatible v α) : T.ClocksNonnegative v := by
  intro c
  rw [hv c]
  exact (α c.val).coe_nonneg

/-- Extension outside declared clocks is irrelevant and chosen to be zero. -/
theorem exists_clockCompatible_iff (v : T.HAVar → ℝ) :
    (∃ α, T.ClockCompatible v α) ↔ T.ClocksNonnegative v := by
  constructor
  · rintro ⟨α, ha⟩
    exact T.clockCompatible_nonnegative ha
  · intro hv
    classical
    let α : ClockValuation Clock := fun c =>
      if hc : c ∈ T.clocks then ⟨v (.inr (.inl ⟨c, hc⟩)), hv ⟨c, hc⟩⟩ else 0
    refine ⟨α, ?_⟩
    intro c
    simp only [α, dif_pos c.property]
    rfl

theorem reset_clockCompatible (Λ : ClockResetSet Clock)
    {v : T.HAVar → ℝ} {α : ClockValuation Clock} (hv : T.ClockCompatible v α) :
    T.ClockCompatible (T.reset Λ v) (Λ.apply α) :=
  T.reset_clock_agrees Λ v α hv

theorem reset_clocksNonnegative (Λ : ClockResetSet Clock)
    {v : T.HAVar → ℝ} (hv : T.ClocksNonnegative v) :
    T.ClocksNonnegative (T.reset Λ v) := by
  obtain ⟨α, ha⟩ := (T.exists_clockCompatible_iff v).mpr hv
  exact T.clockCompatible_nonnegative (T.reset_clockCompatible Λ ha)

variable (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)

theorem flow_clockCompatible {s t v} {α : ClockValuation Clock}
    (hf : (T.toAutomaton h τ hτ).flow s t v) (hv : T.ClockCompatible s.2 α) :
    T.ClockCompatible v (ClockResetSet.elapse α t) := by
  intro c
  rw [hf.1 c, hv c]
  rfl

theorem continuousStep_clockCompatible
    {s s' : (T.toAutomaton h τ hτ).State} {r : NNReal}
    {γ : Set.Icc (0 : ℝ) r → T.HAVar → ℝ} {α : ClockValuation Clock}
    (hc : (T.toAutomaton h τ hτ).ContinuousStep s s' r γ)
    (hv : T.ClockCompatible s.val.2 α) :
    T.ClockCompatible s'.val.2 (ClockResetSet.elapse α r) := by
  have hf := T.flow_clockCompatible h τ hτ (hc.2.2.2 ⟨r, by simp⟩).1 hv
  rw [hc.2.2.1] at hf
  exact hf

/-- The same edge label supplies tableau guards before its reset and the
compatible valuation after it; no new existential guard valuation is used. -/
theorem discreteStep_clockCompatible
    {s s' : (T.toAutomaton h τ hτ).State} {α : ClockValuation Clock}
    (hj : (T.toAutomaton h τ hτ).DiscreteStep s s')
    (hv : T.ClockCompatible s.val.2 α) :
    ∃ l : EdgeLabel Clock, (s.val.1.val, l, s'.val.1.val) ∈ T.edges ∧
      (∀ g ∈ l.guards, g.holds α) ∧ T.ClockCompatible s'.val.2 (l.resets.apply α) := by
  obtain ⟨l, he, hg, hr, _⟩ := (T.discreteStep_iff h τ hτ).mp hj
  refine ⟨l, he, (T.guardsHold_iff l _ α (h.edge_guards _ he) hv).mp hg, ?_⟩
  rw [hr]
  exact T.reset_clockCompatible l.resets hv

theorem discreteStep_clocksNonnegative
    {s s' : (T.toAutomaton h τ hτ).State}
    (hj : (T.toAutomaton h τ hτ).DiscreteStep s s')
    (hv : T.ClocksNonnegative s.val.2) : T.ClocksNonnegative s'.val.2 := by
  obtain ⟨α, ha⟩ := (T.exists_clockCompatible_iff _).mpr hv
  obtain ⟨l, _, _, hb⟩ := T.discreteStep_clockCompatible h τ hτ hj ha
  exact T.clockCompatible_nonnegative hb

/-- A zero-time edge together with its actual guard valuation and reset result.
This relation does not advance a partition position and is not trace `next`. -/
def GuardedClockStep (a b : T.states × ClockValuation Clock) : Prop :=
  ∃ l : EdgeLabel Clock, (a.1.val, l, b.1.val) ∈ T.edges ∧
    (∀ g ∈ l.guards, g.holds a.2) ∧ b.2 = l.resets.apply a.2

/-- Extract a whole jump block without choosing unrelated valuations for its
edges. Each guard is evaluated after all preceding resets, with no time elapse.
The final compatible valuation is the endpoint of the same guarded path. -/
theorem discreteSteps_guardedClockSteps
    {s s' : (T.toAutomaton h τ hτ).State} {α : ClockValuation Clock}
    (hj : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep s s')
    (hv : T.ClockCompatible s.val.2 α) :
    ∃ β : ClockValuation Clock, T.ClockCompatible s'.val.2 β ∧
      Relation.ReflTransGen T.GuardedClockStep (s.val.1, α) (s'.val.1, β) := by
  induction hj with
  | refl => exact ⟨α, hv, .refl⟩
  | @tail t u _ hstep ih =>
    obtain ⟨β, hb, hpath⟩ := ih
    obtain ⟨l, he, hg, hc⟩ := T.discreteStep_clockCompatible h τ hτ hstep hb
    exact ⟨l.resets.apply β, hc, hpath.tail ⟨l, he, hg, rfl⟩⟩

/-- Nonempty jump blocks retain a nonempty guarded witness, even when the
source and destination mode coincide. No duplicate-mode erasure is used. -/
theorem discreteSteps_guardedClockSteps_nonempty
    {s s' : (T.toAutomaton h τ hτ).State} {α : ClockValuation Clock}
    (hj : Relation.TransGen (T.toAutomaton h τ hτ).DiscreteStep s s')
    (hv : T.ClockCompatible s.val.2 α) :
    ∃ β : ClockValuation Clock, T.ClockCompatible s'.val.2 β ∧
      Relation.TransGen T.GuardedClockStep (s.val.1, α) (s'.val.1, β) := by
  induction hj with
  | single hstep =>
    obtain ⟨l, he, hg, hc⟩ := T.discreteStep_clockCompatible h τ hτ hstep hv
    exact ⟨l.resets.apply α, hc, .single ⟨l, he, hg, rfl⟩⟩
  | tail _ hstep ih =>
    obtain ⟨β, hb, hpath⟩ := ih
    obtain ⟨l, he, hg, hc⟩ := T.discreteStep_clockCompatible h τ hτ hstep hb
    exact ⟨l.resets.apply β, hc, hpath.tail ⟨l, he, hg, rfl⟩⟩

theorem discreteSteps_clocksNonnegative
    {s s' : (T.toAutomaton h τ hτ).State}
    (hj : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep s s')
    (hv : T.ClocksNonnegative s.val.2) : T.ClocksNonnegative s'.val.2 := by
  induction hj with
  | refl => exact hv
  | tail _ hstep ih => exact T.discreteStep_clocksNonnegative h τ hτ hstep ih

/-- At an actual flow boundary time advances exactly once, by that flow's
duration. All intervening jumps then retain their guarded/reset sequence. -/
theorem execution_between_flows_guardedClockSteps {σ : FiniteSignal T.HAVar}
    (e : (T.toAutomaton h τ hτ).Execution σ)
    (i : Fin e.count) (hi : i.val + 1 < e.count) {α : ClockValuation Clock}
    (hv : T.ClockCompatible (e.start i).val.2 α) :
    ∃ β : ClockValuation Clock,
      T.ClockCompatible (e.start ⟨i.val + 1, hi⟩).val.2 β ∧
      Relation.TransGen T.GuardedClockStep
        ((e.finish i).val.1, ClockResetSet.elapse α (e.duration i))
        ((e.start ⟨i.val + 1, hi⟩).val.1, β) :=
  T.discreteSteps_guardedClockSteps_nonempty h τ hτ (e.discreteSteps i hi)
    (T.continuousStep_clockCompatible h τ hτ (e.continuousStep i) hv)

theorem continuousStep_clocksNonnegative
    {s s' : (T.toAutomaton h τ hτ).State} {r : NNReal}
    {γ : Set.Icc (0 : ℝ) r → T.HAVar → ℝ}
    (hc : (T.toAutomaton h τ hτ).ContinuousStep s s' r γ)
    (hv : T.ClocksNonnegative s.val.2) : T.ClocksNonnegative s'.val.2 := by
  obtain ⟨α, ha⟩ := (T.exists_clockCompatible_iff _).mpr hv
  exact T.clockCompatible_nonnegative (T.continuousStep_clockCompatible h τ hτ hc ha)

/-- Nonnegativity is propagated from an explicit initial-state premise;
it is not added to the automaton's definition. -/
theorem execution_start_clocksNonnegative {σ : FiniteSignal T.HAVar}
    (e : (T.toAutomaton h τ hτ).Execution σ)
    (hv : T.ClocksNonnegative e.initialState.val.2) (i : Fin e.count) :
    T.ClocksNonnegative (e.start i).val.2 := by
  have aux : ∀ n (hn : n < e.count), T.ClocksNonnegative (e.start ⟨n, hn⟩).val.2 := by
    intro n
    induction n with
    | zero =>
      intro hn
      exact T.discreteSteps_clocksNonnegative h τ hτ e.initialSteps hv
    | succ n ih =>
      intro hn
      have hp : n < e.count := by omega
      exact T.discreteSteps_clocksNonnegative h τ hτ
        (e.discreteSteps ⟨n, hp⟩ hn).to_reflTransGen
        (T.continuousStep_clocksNonnegative h τ hτ (e.continuousStep ⟨n, hp⟩) (ih hp))
  exact aux i.val i.isLt

theorem execution_final_clocksNonnegative {σ : FiniteSignal T.HAVar}
    (e : (T.toAutomaton h τ hτ).Execution σ)
    (hv : T.ClocksNonnegative e.initialState.val.2) :
    T.ClocksNonnegative e.finalState.val.2 := by
  have hn : e.count - 1 < e.count := by have := e.nonempty; omega
  exact T.discreteSteps_clocksNonnegative h τ hτ e.finalSteps
    (T.continuousStep_clocksNonnegative h τ hτ (e.continuousStep ⟨e.count - 1, hn⟩)
      (T.execution_start_clocksNonnegative h τ hτ e hv _))

end STLTableau.Section4.Tableau
