import STLTableaux.Automata.Recognition.TypedExecutionVisits

namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
variable (h : T.TranslationReady) (τ : ℝ)
local notation "𝓗" => (T.typedAutomaton h τ)

theorem typed_initial_visits {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ) :
    e.initialState = e.start ⟨0, e.nonempty⟩ ∨
      (𝓗).DiscreteStep e.initialState (e.start ⟨0, e.nonempty⟩) := by
  have hz : e.initialState.val.2 T.dwell = 0 := by
    obtain ⟨_, _, _, _, _, hz, _⟩ := e.initial_mem
    exact hz
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp e.initialSteps with he | hj
  · exact Or.inl he.symm
  · rcases T.typed_boundary_block h τ hj with hs | ⟨_, hs, _, hs'⟩
    · exact Or.inr hs
    · exact (T.no_adjacent_zero h τ hs hz hs').elim

theorem typed_jump_global {a b : (𝓗).State} (hj : (𝓗).DiscreteStep a b) :
    b.val.2 (.inl T.globalClock) = a.val.2 (.inl T.globalClock) := by
  obtain ⟨_, _, _, _, _, _, _, hg, _⟩ := hj
  exact hg

theorem typed_chain_global {a b : (𝓗).State}
    (hs : Relation.ReflTransGen (𝓗).DiscreteStep a b) :
    b.val.2 (.inl T.globalClock) = a.val.2 (.inl T.globalClock) := by
  induction hs with
  | refl => rfl
  | tail _ hj ih => exact (T.typed_jump_global h τ hj).trans ih

theorem typed_flow_global {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ)
    (i : Fin e.count) : (e.finish i).val.2 (.inl T.globalClock) =
      (e.start i).val.2 (.inl T.globalClock) + e.duration i := by
  let u : Set.Icc (0 : ℝ) (e.duration i) := ⟨e.duration i, by simp⟩
  have hc := e.continuousStep i
  have hv := ((hc.2.2.2 u).1).2.1
  rw [show e.curve i u = (e.finish i).val.2 from hc.2.2.1] at hv
  exact hv

theorem typed_entry_time {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ)
    (i : Fin e.count) :
    (e.start i).val.2 (.inl T.globalClock) = e.boundary i.castSucc := by
  obtain ⟨k, hk⟩ := i
  induction k with
  | zero =>
    obtain ⟨_, _, _, _, hv, _, _⟩ := e.initial_mem
    have hg := congrFun hv T.globalClock
    change e.initialState.val.2 (.inl T.globalClock) = 0 at hg
    exact (T.typed_chain_global h τ e.initialSteps).trans (hg.trans e.first_zero.symm)
  | succ k ih =>
    let j : Fin e.count := ⟨k, by omega⟩
    have hg := T.typed_chain_global h τ (e.discreteSteps j hk).to_reflTransGen
    have hf := T.typed_flow_global h τ e j
    have hd := e.duration_eq j
    have hp := ih j.isLt
    change (e.start ⟨k+1, hk⟩).val.2 (.inl T.globalClock) =
      e.boundary ⟨k+1, by omega⟩
    rw [hg, hf, hp, hd]
    change e.boundary j.castSucc + (e.boundary j.succ - e.boundary j.castSucc) =
      e.boundary j.succ
    ring

theorem typed_final_time {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ) :
    e.finalState.val.2 (.inl T.globalClock) = e.boundary ⟨e.count, by omega⟩ := by
  let j : Fin e.count := ⟨e.count - 1, by have := e.nonempty; omega⟩
  have hg := T.typed_chain_global h τ e.finalSteps
  have hf := T.typed_flow_global h τ e j
  have hp := T.typed_entry_time h τ e j
  have hd := e.duration_eq j
  have he : j.succ = (⟨e.count, by omega⟩ : Fin (e.count + 1)) := by
    apply Fin.ext
    have := e.nonempty
    dsimp [j]
    omega
  rw [hg, hf, hp, hd]
  change e.boundary j.castSucc + (e.boundary j.succ - e.boundary j.castSucc) = _
  rw [he]
  ring

/-- A final cut entered by a terminal jump is at the horizon, not an
additional signal interval. No signal value at that time is used. -/
theorem typed_terminal_cut {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ)
    (hh : σ.horizon = τ) {a : (𝓗).State}
    (hj : (𝓗).DiscreteStep a e.finalState)
    (ht : e.finalState.val.1 ∈ T.terminalModes) :
    e.boundary ⟨e.count, by omega⟩ = τ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hterm, _⟩ := hj
  apply le_antisymm (e.last_le_horizon.trans_eq hh)
  simpa only [T.typed_final_time h τ e] using hterm.mp ht

end STLTableau.Section4.Tableau
