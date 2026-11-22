import STLTableaux.Automata.Execution.PrelimExecution
import STLTableaux.Automata.Translation.EndPositionTranslation

namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)

/-- The automaton with a residence clock, an endpoint marker, and a horizon guard for
targets labelled `*`. -/
def prelimAutomaton (h : T.TranslationReady) (τ : ℝ) :
    HybridAutomaton T.states (EdgeLabel Clock) T.TypedVar :=
  { T.typedAutomaton h τ with
    jump := fun e s s' =>
      s.1 = e.val.1 ∧ s'.1 = e.val.2.2 ∧ T.guardsHold e.val.2.1 (T.old s.2) ∧
      (∀ c : T.clocks, s'.2 (.inl (.inr (.inl c))) =
        T.reset e.val.2.1.resets (T.old s.2) (.inr (.inl c))) ∧
      s'.2 (.inl T.globalClock) = s.2 (.inl T.globalClock) ∧ s'.2 T.dwell = 0 ∧
      (s'.1 ∈ T.terminalModes → τ ≤ s'.2 (.inl T.globalClock)) ∧
      (s.2 T.dwell = 0 → s.2 T.bit = 1 ∧ s'.2 T.bit = 0) ∧
      (s'.2 T.bit = 0 → T.atomsAt s.1 s'.2) }

theorem endPosition_step_to_prelim (h : T.TranslationReady) (τ : ℝ)
    {a b : (T.endPositionAutomaton h τ).State}
    (step : (T.endPositionAutomaton h τ).DiscreteStep a b) :
    (T.prelimAutomaton h τ).DiscreteStep a b := by
  obtain ⟨e, hs, hd, h₁, h₂, hg, hr, hc, hz, ht, hm, ha⟩ := step
  refine ⟨e, hs, hd, h₁, h₂, hg, hr, hc, hz, ?_, hm, ha⟩
  intro hb
  rcases ht with ⟨_, hn⟩ | ⟨heq, _⟩
  · exact (hn hb).elim
  · exact heq.ge

private theorem liftRTG (h : T.TranslationReady) (τ : ℝ)
    {a b : (T.endPositionAutomaton h τ).State}
    (steps : Relation.ReflTransGen (T.endPositionAutomaton h τ).DiscreteStep a b) :
    Relation.ReflTransGen (T.prelimAutomaton h τ).DiscreteStep a b := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (T.endPosition_step_to_prelim h τ step)

private theorem liftTG (h : T.TranslationReady) (τ : ℝ)
    {a b : (T.endPositionAutomaton h τ).State}
    (steps : Relation.TransGen (T.endPositionAutomaton h τ).DiscreteStep a b) :
    Relation.TransGen (T.prelimAutomaton h τ).DiscreteStep a b := by
  induction steps with
  | single step => exact .single (T.endPosition_step_to_prelim h τ step)
  | tail _ step ih => exact ih.tail (T.endPosition_step_to_prelim h τ step)

/-- Transfer the prefix through the last positive flow to `prelimAutomaton`. -/
def endPosition_to_prelim (h : T.TranslationReady) (τ : ℝ)
    {σ : FiniteSignal T.TypedVar}
    (e : (T.endPositionAutomaton h τ).PrelimExecution σ) :
    (T.prelimAutomaton h τ).PrelimExecution σ where
  count := e.count
  nonempty := e.nonempty
  initialState := e.initialState
  initial_mem := e.initial_mem
  start := e.start
  finish := e.finish
  boundary := e.boundary
  first_zero := e.first_zero
  increasing := e.increasing
  last_le_horizon := e.last_le_horizon
  duration := e.duration
  duration_eq := e.duration_eq
  curve := e.curve
  continuousStep := e.continuousStep
  initialSteps := T.liftRTG h τ e.initialSteps
  discreteSteps := fun i hi => T.liftTG h τ (e.discreteSteps i hi)
  signal_eq := e.signal_eq

theorem endPosition_prelimReaches (h : T.TranslationReady) (τ : ℝ)
    {σ : FiniteSignal T.TypedVar}
    (hr : (T.endPositionAutomaton h τ).PrelimReaches σ T.goalModes) :
    (T.prelimAutomaton h τ).PrelimReaches σ T.goalModes := by
  obtain ⟨e, q, hg, hv⟩ := hr
  refine ⟨T.endPosition_to_prelim h τ e, q, hg, ?_⟩
  rcases hv with flow | initial | between
  · exact Or.inl flow
  · right; left
    obtain ⟨s, hq, pre, post⟩ := initial
    exact ⟨s, hq, T.liftRTG h τ pre, T.liftRTG h τ post⟩
  · right; right
    obtain ⟨i, hi, s, hq, pre, post⟩ := between
    exact ⟨i, hi, s, hq, T.liftRTG h τ pre, T.liftRTG h τ post⟩

end STLTableau.Section4.Tableau
