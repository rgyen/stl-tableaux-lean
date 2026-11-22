import STLTableaux.Automata.Translation.PrelimEntryTimes

/-! An alternative goal predicate records an enabled outgoing tableau edge
at the horizon as a certificate on the final flow state. -/
namespace STLTableau.HybridAutomaton
variable {Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
variable {σ : FiniteSignal Var}

def PrelimExecution.VisitsState (e : H.PrelimExecution σ) (s : H.State) : Prop :=
  (∃ i u, s.val = ((e.start i).val.1, e.curve i u)) ∨
  (Relation.ReflTransGen H.DiscreteStep e.initialState s ∧
    Relation.ReflTransGen H.DiscreteStep s (e.start ⟨0, e.nonempty⟩)) ∨
  ∃ (i : Fin e.count) (hi : i.val + 1 < e.count),
    Relation.ReflTransGen H.DiscreteStep (e.finish i) s ∧
    Relation.ReflTransGen H.DiscreteStep s (e.start ⟨i.val + 1, hi⟩)

theorem PrelimExecution.visits_finalState (e : H.PrelimExecution σ) :
    e.VisitsState e.finalState := by
  refine Or.inl ⟨e.lastIndex, ⟨e.duration e.lastIndex, by simp⟩, ?_⟩
  exact Prod.ext (e.continuousStep e.lastIndex).1.symm
    (e.continuousStep e.lastIndex).2.2.1.symm

def PrelimReachesState (H : HybridAutomaton Mode Label Var) (σ : FiniteSignal Var)
    (goal : Set H.State) : Prop :=
  ∃ e : H.PrelimExecution σ, ∃ s ∈ goal, e.VisitsState s

end STLTableau.HybridAutomaton

namespace STLTableau.Section4.Tableau
open Section3
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
variable (h : T.TranslationReady) (τ : ℝ)
local notation "H" => T.prelimAutomaton h τ

/-- A valid state is a goal in a final mode or when it enables an edge
to a terminal-position goal at the horizon. -/
def prelimGoal : Set (H).State :=
  {s | s.val.1 ∈ T.goalModes ∨
    τ ≤ s.val.2 (.inl T.globalClock) ∧
      ∃ (l : EdgeLabel Clock) (q : T.states),
        (s.val.1.val, l, q.val) ∈ T.edges ∧
        T.guardsHold l (T.old s.val.2) ∧ T.EndGoal q}

theorem prelim_finish_time {σ : FiniteSignal T.TypedVar} (e : (H).PrelimExecution σ)
    (i : Fin e.count) :
    (e.finish i).val.2 (.inl T.globalClock) = e.boundary i.succ := by
  rw [T.prelim_flow_global h τ e i, T.prelim_entry_time h τ e i, e.duration_eq]
  change e.boundary i.castSucc + (e.boundary i.succ - e.boundary i.castSucc) = _
  ring

theorem prelim_final_time {σ : FiniteSignal T.TypedVar} (e : (H).PrelimExecution σ) :
    e.finalState.val.2 (.inl T.globalClock) = e.boundary ⟨e.count, by omega⟩ := by
  have he : e.lastIndex.succ = (⟨e.count, by omega⟩ : Fin (e.count + 1)) := by
    apply Fin.ext
    change e.count - 1 + 1 = e.count
    have := e.nonempty
    omega
  exact (T.prelim_finish_time h τ e e.lastIndex).trans (congrArg e.boundary he)

/-- A horizon jump supplies the edge, guard, and target label for the
certificate on the source state. -/
theorem prelimGoal_of_end_edge {a b : (T.endPositionAutomaton h τ).State}
    (step : (T.endPositionAutomaton h τ).DiscreteStep a b)
    (ht : a.val.2 (.inl T.globalClock) = τ) : a ∈ T.prelimGoal h τ := by
  have endGoal := (T.horizon_step_last h τ step ht).1
  obtain ⟨e, hs, hd, _, _, hg, _⟩ := step
  refine Or.inr ⟨ht.ge, e.val.2.1, b.val.1, ?_, hg, endGoal⟩
  have he : (e.val.1.val, e.val.2.1, e.val.2.2.val) ∈ T.edges := e.property
  simpa only [hs, hd] using he

end STLTableau.Section4.Tableau
