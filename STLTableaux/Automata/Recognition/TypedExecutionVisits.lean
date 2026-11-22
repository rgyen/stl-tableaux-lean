import STLTableaux.Automata.Translation.TypedTableauAutomata

namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
variable (h : T.TranslationReady) (τ : ℝ)

theorem typed_jump_dwell_zero {a b : (T.typedAutomaton h τ).State} (hj : (T.typedAutomaton h τ).DiscreteStep a b) :
    b.val.2 T.dwell = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, hz, _⟩ := hj
  exact hz

/-- The boundary block retains every actual jump. A two-jump block
has exactly one intermediate (zero-residence) visit. -/
theorem typed_boundary_block {a b : (T.typedAutomaton h τ).State} (hj : Relation.TransGen (T.typedAutomaton h τ).DiscreteStep a b) :
    (T.typedAutomaton h τ).DiscreteStep a b ∨
      ∃ s, (T.typedAutomaton h τ).DiscreteStep a s ∧ s.val.2 T.dwell = 0 ∧ (T.typedAutomaton h τ).DiscreteStep s b := by
  induction hj with
  | single hstep => exact Or.inl hstep
  | tail _ hstep ih =>
    rcases ih with hj | ⟨s, _, hz, hs⟩
    · exact Or.inr ⟨_, hj, T.typed_jump_dwell_zero h τ hj, hstep⟩
    · exact (T.no_adjacent_zero h τ hs hz hstep).elim

theorem typed_execution_boundary {σ : FiniteSignal T.TypedVar} (e : (T.typedAutomaton h τ).Execution σ)
    (i : Fin e.count) (hi : i.val + 1 < e.count) :
    (T.typedAutomaton h τ).DiscreteStep (e.finish i) (e.start ⟨i.val + 1, hi⟩) ∨
      ∃ s, (T.typedAutomaton h τ).DiscreteStep (e.finish i) s ∧ s.val.2 T.dwell = 0 ∧
        (T.typedAutomaton h τ).DiscreteStep s (e.start ⟨i.val + 1, hi⟩) :=
  T.typed_boundary_block h τ (e.discreteSteps i hi)

theorem typed_start_dwell {σ : FiniteSignal T.TypedVar} (e : (T.typedAutomaton h τ).Execution σ)
    (i : Fin e.count) : (e.start i).val.2 T.dwell = 0 := by
  by_cases hi : i.val = 0
  · have hinit : e.initialState.val.2 T.dwell = 0 := by
      obtain ⟨_, _, _, _, _, hz, _⟩ := e.initial_mem
      exact hz
    have hchain : Relation.ReflTransGen (T.typedAutomaton h τ).DiscreteStep
        e.initialState (e.start i) := by
      simpa only [show i = ⟨0, e.nonempty⟩ from Fin.ext hi] using e.initialSteps
    generalize hs : e.start i = s at hchain ⊢
    induction hchain with
    | refl => exact hinit
    | tail _ hj _ => exact T.typed_jump_dwell_zero h τ hj
  · let j : Fin e.count := ⟨i.val - 1, by have := i.isLt; omega⟩
    have hj : j.val + 1 = i.val := by dsimp [j]; omega
    have hb := T.typed_execution_boundary h τ e j (hj.symm ▸ i.isLt)
    rw [show (⟨j.val + 1, hj.symm ▸ i.isLt⟩ : Fin e.count) = i from Fin.ext hj] at hb
    obtain hstep | ⟨_, _, _, hstep⟩ := hb
    all_goals exact T.typed_jump_dwell_zero h τ hstep

theorem typed_finish_dwell {σ : FiniteSignal T.TypedVar}
    (e : (T.typedAutomaton h τ).Execution σ) (i : Fin e.count) :
    (e.finish i).val.2 T.dwell = (e.duration i : ℝ) := by
  let u : Set.Icc (0 : ℝ) (e.duration i) := ⟨e.duration i, by simp⟩
  have hc := e.continuousStep i
  have hv := ((hc.2.2.2 u).1).2.2.1
  rw [show e.curve i u = (e.finish i).val.2 from hc.2.2.1,
      T.typed_start_dwell h τ e i, zero_add] at hv
  exact hv

end STLTableau.Section4.Tableau
