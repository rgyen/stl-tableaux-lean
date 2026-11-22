import STLTableaux.Automata.Recognition.ExecutionObservedSuffix

/-! Extraction over the actual finite execution, retaining actual jump edges,
residence times and observations together. Reflexive semantic-state steps in
zero-time tails may be omitted. This does not yet turn all remaining zero-time
frames into a disjoint partition. -/
namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
    (h : T.TranslationReady) {σ : FiniteSignal T.HAVar}
    (e : (T.toPrunedAutomaton h σ.horizon σ.horizon_pos).Execution σ)

theorem pruned_execution_observed_path (incoming : EdgeLabel Clock) :
    T.pruneTerminal.ObservedSuffix (T.pruneTerminal_translationReady h)
      σ.horizon σ.horizon_pos e e.initialState e.finalState
      0 (e.boundary ⟨e.count, by omega⟩) incoming := by
  let U := T.pruneTerminal
  let hU := T.pruneTerminal_translationReady h
  have aux : ∀ d : ℕ, ∀ i : Fin e.count, e.count - (i.val + 1) = d →
      ∀ inc, U.ObservedSuffix hU σ.horizon σ.horizon_pos e
        (e.start i) e.finalState (e.boundary ⟨i.val, by omega⟩)
        (e.boundary ⟨e.count, by omega⟩) inc := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro i hid inc
      by_cases hlast : i.val + 1 = e.count
      · have hi : i = ⟨e.count - 1, by have := e.nonempty; omega⟩ :=
          Fin.ext (by change i.val = e.count - 1; omega)
        rw [hi]
        exact T.pruned_last_flow_observed h e inc
      · have hnext : i.val + 1 < e.count := by have := i.isLt; omega
        let j : Fin e.count := ⟨i.val + 1, hnext⟩
        have hlt : e.count - (j.val + 1) < d := by dsimp [j]; omega
        have build := ih (e.count - (j.val + 1)) hlt j rfl
        obtain ⟨p, ds, hw, ht, hp, hin⟩ :=
          U.prepend_observed_nonempty_discrete_block hU σ.horizon σ.horizon_pos e
            (e.start j) e.finalState (e.finish i)
            (e.boundary ⟨j.val, by omega⟩) (e.boundary ⟨e.count, by omega⟩)
            (e.discreteSteps i hnext) (fun s hs => .beforeFlow j s hs) build inc
        obtain ⟨hw', ht', hp'⟩ :=
          hp.prepend_flow_with_witness U hU σ.horizon σ.horizon_pos e i e.finalState hw ht
        exact ⟨p, e.duration i :: ds, hw', ht', hp', hin⟩
  have build := aux (e.count - (0 + 1)) ⟨0, e.nonempty⟩ rfl
  have result := U.prepend_beforeFlow_discrete_block hU σ.horizon σ.horizon_pos e
    ⟨0, e.nonempty⟩ e.finalState e.initialState (e.boundary ⟨e.count, by omega⟩)
    e.initialSteps build incoming
  simpa only [e.first_zero] using result

/-- Accepting path existence is strengthened with observations, without
choosing a second path for the clock or observation calculations. -/
theorem pruned_execution_accepting_observed_path
    (hgoal : e.finalState.val.1 ∈ T.pruneTerminal.goalModes) :
    ∃ p ds, p.run T ∧ p.accepting T ∧
      T.pruneTerminal.ExecutionPathWitness (T.pruneTerminal_translationReady h)
        σ.horizon σ.horizon_pos e.initialState e.finalState p ∧
      T.pruneTerminal.TimedPath p e.initialState.val.2 e.finalState.val.2 ds ∧
      T.pruneTerminal.ObservedPath (T.pruneTerminal_translationReady h)
        σ.horizon σ.horizon_pos e p 0 (e.boundary ⟨e.count, by omega⟩) ds ∧
      ∃ u : T.HAVar → ℝ, T.pruneTerminal.guardsHold p.firstIncoming u ∧
        e.initialState.val.2 = T.pruneTerminal.initialReset p.firstIncoming.resets u := by
  obtain ⟨inc, hi, u, hg, hr⟩ := e.initial_mem
  obtain ⟨p, ds, hw, ht, hp, hin⟩ := T.pruned_execution_observed_path h e inc
  obtain ⟨hvalid, hfirst, hlast⟩ := hw.valid _ _ _ _
  have hrun : p.run T.pruneTerminal := ⟨hvalid, by simpa only [hin, hfirst] using hi⟩
  have hacc : p.accepting T.pruneTerminal := ⟨hvalid, by rwa [hlast]⟩
  exact ⟨p, ds, p.run_of_pruned T hrun, p.accepting_of_pruned T hacc,
    hw, ht, hp, u, hin ▸ hg, hin ▸ hr⟩

end STLTableau.Section4.Tableau
