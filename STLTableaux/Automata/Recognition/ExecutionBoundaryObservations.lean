import STLTableaux.Automata.Recognition.ExecutionObservedPiece
import STLTableaux.Automata.Recognition.TableauExecutionTime

/-! Actual zero-time boundary observations. No partition or marker alignment
is asserted; intermediate states retain their actual discrete-chain witnesses. -/
namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {σ : FiniteSignal T.HAVar} (e : (T.toAutomaton h τ hτ).Execution σ)

theorem execution_initial_boundary_observation :
    e.initialState.val.2 T.globalClock = 0 ∧
    T.ExecutionObservedPiece h τ hτ e e.initialState.val.1.val 0 0 := by
  refine ⟨T.initial_globalClock_zero h τ hτ e.initial_mem, ?_⟩
  simpa only [e.first_zero] using
    (ExecutionObservedPiece.beforeFlow (T := T) (h := h) (τ := τ) (hτ := hτ)
      (e := e) ⟨0, e.nonempty⟩ e.initialState e.initialSteps)

/-- A chosen state splitting the actual intermediate jump block is observed
at that block's boundary, with its genuine remaining chain to the next flow. -/
theorem execution_intermediate_boundary_observation
    (i : Fin e.count) (hi : i.val + 1 < e.count)
    (s : (T.toAutomaton h τ hτ).State)
    (hprefix : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep
      (e.finish i) s)
    (hsuffix : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep
      s (e.start ⟨i.val + 1, hi⟩)) :
    s.val.2 T.globalClock = e.boundary ⟨i.val + 1, by omega⟩ ∧
    T.ExecutionObservedPiece h τ hτ e s.val.1.val
      (e.boundary ⟨i.val + 1, by omega⟩) (e.boundary ⟨i.val + 1, by omega⟩) := by
  refine ⟨?_, .beforeFlow ⟨i.val + 1, hi⟩ s hsuffix⟩
  exact (T.discreteSteps_globalClock_preserved h τ hτ hprefix).trans
    (T.execution_finish_clock h τ hτ e i)

/-- Early stopping makes final-chain points actual signal times. The prefix
and suffix locate the chosen state without changing any execution edge. -/
theorem execution_final_boundary_observation
    (s : (T.toAutomaton h τ hτ).State)
    (hprefix : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep
      (e.finish ⟨e.count - 1, by have := e.nonempty; omega⟩) s)
    (hsuffix : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep s e.finalState)
    (hearly : e.boundary ⟨e.count, by omega⟩ < σ.horizon) :
    s.val.2 T.globalClock = e.boundary ⟨e.count, by omega⟩ ∧
    T.ExecutionObservedPiece h τ hτ e s.val.1.val
      (e.boundary ⟨e.count, by omega⟩) (e.boundary ⟨e.count, by omega⟩) := by
  refine ⟨?_, .atFinal s hsuffix hearly⟩
  have hc := (T.discreteSteps_globalClock_preserved h τ hτ hprefix).trans
    (T.execution_finish_clock h τ hτ e ⟨e.count - 1, by have := e.nonempty; omega⟩)
  simpa only [Nat.sub_add_cancel (by have := e.nonempty; omega : 1 ≤ e.count)] using hc

end STLTableau.Section4.Tableau
