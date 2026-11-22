import STLTableaux.Automata.Translation.PrelimStateGoal

/-! Goal reachability for the translation in Section 5. The preliminaries'
execution is unchanged; only the check at its final flow may take a jump. -/

namespace STLTableau.HybridAutomaton
variable {Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
variable {σ : FiniteSignal Var}

/-- At a flow endpoint, either it is already a goal, or one actual discrete
step at the horizon reaches a state in the goal set. -/
def GoalAtEnd (H : HybridAutomaton Mode Label Var) (goal : Set H.State)
    (s : H.State) (atHorizon : Prop) : Prop :=
  s ∈ goal ∨ atHorizon ∧ ∃ b ∈ goal, H.DiscreteStep s b

/-- In addition to visits in the ordinary execution, take one final step
from the same witness's endpoint at the horizon. No signal value is read
there, and no positive flow after that step is required. -/
def PrelimReachesStateOrFinalJump (H : HybridAutomaton Mode Label Var) (σ : FiniteSignal Var)
    (goal : Set H.State) : Prop :=
  ∃ e : H.PrelimExecution σ,
    (∃ s ∈ goal, e.VisitsState s) ∨
      (e.ReachesHorizon ∧ ∃ b ∈ goal, H.DiscreteStep e.finalState b)

theorem PrelimExecution.reaches_of_goalAtEnd {goal : Set H.State} (e : H.PrelimExecution σ)
    (reach : H.GoalAtEnd goal e.finalState e.ReachesHorizon) :
    H.PrelimReachesStateOrFinalJump σ goal := by
  rcases reach with hit | last
  · exact ⟨e, Or.inl ⟨e.finalState,hit,e.visits_finalState⟩⟩
  · exact ⟨e, Or.inr last⟩

end STLTableau.HybridAutomaton
