import STLTableaux.Automata.Translation.TableauAutomata

/-! Absolute time along translated executions, including initial and terminal
zero-time jumps. No full-horizon coverage assumption is used. -/
namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {σ : FiniteSignal T.HAVar} (e : (T.toAutomaton h τ hτ).Execution σ)

theorem execution_start_clock (i : Fin e.count) :
    (e.start i).val.2 T.globalClock = e.boundary ⟨i.val, by omega⟩ := by
  have aux : ∀ n (hn : n < e.count),
      (e.start ⟨n, hn⟩).val.2 T.globalClock = e.boundary ⟨n, by omega⟩ := by
    intro n
    induction n with
    | zero =>
      intro hn
      have hi := T.initial_globalClock_zero h τ hτ e.initial_mem
      have hd := T.discreteSteps_globalClock_preserved h τ hτ e.initialSteps
      simpa only [e.first_zero] using hd.trans hi
    | succ n ih =>
      intro hn
      have hp : n < e.count := by omega
      have hc := T.continuousStep_globalClock h τ hτ (e.continuousStep ⟨n, hp⟩)
      have hd := T.discreteSteps_globalClock_preserved h τ hτ
        (e.discreteSteps ⟨n, hp⟩ hn).to_reflTransGen
      have ht := e.duration_eq ⟨n, hp⟩
      have hs := ih hp
      change (e.start ⟨n + 1, hn⟩).val.2 T.globalClock =
        e.boundary ⟨n + 1, by omega⟩
      linarith
  exact aux i.val i.isLt

theorem execution_finish_clock (i : Fin e.count) :
    (e.finish i).val.2 T.globalClock = e.boundary ⟨i.val + 1, by omega⟩ := by
  have hc := T.continuousStep_globalClock h τ hτ (e.continuousStep i)
  have hs := T.execution_start_clock h τ hτ e i
  have ht := e.duration_eq i
  linarith

/-- The final tail does not shift the stopping time. -/
theorem execution_final_clock :
    e.finalState.val.2 T.globalClock = e.boundary ⟨e.count, by omega⟩ := by
  rw [T.execution_final_clock_eq_last_finish h τ hτ e]
  have hn := e.nonempty
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ e.count)] using
    T.execution_finish_clock h τ hτ e ⟨e.count - 1, by omega⟩

theorem execution_curve_clock (i : Fin e.count)
    (u : Set.Icc (0 : ℝ) (e.duration i)) :
    e.curve i u T.globalClock = e.boundary ⟨i.val, by omega⟩ + u.val := by
  have hf := (e.continuousStep i).2.2.2 u
  have hc := hf.1.2
  rw [T.execution_start_clock h τ hτ e i] at hc
  exact hc

/-- Only the executed prefix is constrained; nothing is asserted about the
unexecuted suffix of the augmented signal. -/
theorem execution_signal_clock (i : Fin e.count) (t : σ.Time)
    (ht : e.boundary ⟨i.val, by omega⟩ ≤ t.val ∧
      t.val < e.boundary ⟨i.val + 1, by omega⟩) :
    σ.value t T.globalClock = t.val := by
  by_cases zero : t.val = 0
  · have same : t = ⟨0, le_rfl, σ.horizon_pos⟩ := Subtype.ext zero
    rw [same, e.initial_signal_eq]
    exact T.initial_globalClock_zero h τ hτ e.initial_mem
  have positive : 0 < t.val := lt_of_le_of_ne t.property.1 (Ne.symm zero)
  rw [e.signal_eq i t ht positive, T.execution_curve_clock h τ hτ e]
  dsimp
  ring

theorem execution_final_clock_le_horizon :
    e.finalState.val.2 T.globalClock ≤ σ.horizon := by
  rw [T.execution_final_clock h τ hτ e]
  exact e.last_le_horizon

/-- Closed invariants admit the final endpoint, but do not permit a positive
ordinary-mode flow to start at the horizon. -/
theorem execution_nonterminal_start_lt (i : Fin e.count)
    (hi : (e.start i).val.1 ∉ T.terminalModes) :
    e.boundary ⟨i.val, by omega⟩ < τ := by
  have hm := (e.continuousStep i).1
  have hf : (e.finish i).val.1 ∉ T.terminalModes := by rwa [← hm]
  have hb := (e.finish i).property.2 hf
  rw [T.execution_finish_clock h τ hτ e i] at hb
  exact (e.increasing (by change i.val < i.val + 1; omega)).trans_le hb

/-- If the final tail enters `*` from an ordinary last segment, its stopping
time must be the horizon. The signal may still stop early in other goals. -/
theorem execution_final_terminal_time
    (hn : (e.finish ⟨e.count - 1, by have := e.nonempty; omega⟩).val.1
      ∉ T.terminalModes)
    (ht : e.finalState.val.1 ∈ T.terminalModes) :
    e.boundary ⟨e.count, by omega⟩ = τ := by
  have hbound := (e.finish ⟨e.count - 1, by have := e.nonempty; omega⟩).property.2 hn
  have hclock := T.execution_final_clock_eq_last_finish h τ hτ e
  have hlower : τ ≤ e.finalState.val.2 T.globalClock := by
    rcases e.finalSteps.cases_tail with heq | ⟨_, _, hlast⟩
    · rw [heq] at ht
      exact (hn ht).elim
    · obtain ⟨edge, _, _, hj⟩ := hlast
      exact hj.2.1 ht
  rw [← T.execution_final_clock h τ hτ e]
  exact le_antisymm (hclock.trans_le hbound) hlower

/-- A positive flow starts strictly before the signal horizon. Thus an actual
jump into that flow cannot target `*` when the two horizons agree. -/
theorem execution_preflow_jump_nonterminal (hh : σ.horizon = τ)
    (i : Fin e.count) {s : (T.toAutomaton h τ hτ).State}
    (hj : (T.toAutomaton h τ hτ).DiscreteStep s (e.start i)) :
    (e.start i).val.1 ∉ T.terminalModes := by
  intro ht
  obtain ⟨edge, _, _, hguard⟩ := hj
  have hge := hguard.2.1 ht
  rw [T.execution_start_clock h τ hτ e i] at hge
  have hlt := (e.increasing (show
    (⟨i.val, by omega⟩ : Fin (e.count + 1)) < ⟨e.count, by omega⟩ from i.isLt)).trans_le
    e.last_le_horizon
  rw [hh] at hlt
  exact (not_lt_of_ge hge) hlt

/-- All positive-flow modes are nonterminal if the initial mode is nonterminal.
The initial-mode premise is explicit: the horizon guard constrains jumps, not
the initial relation. Intermediate jumps need not be erased. -/
theorem execution_flow_nonterminal (hh : σ.horizon = τ)
    (hinit : e.initialState.val.1 ∉ T.terminalModes) (i : Fin e.count) :
    (e.start i).val.1 ∉ T.terminalModes := by
  by_cases hi : i.val = 0
  · have hie : i = ⟨0, e.nonempty⟩ := Fin.ext hi
    subst i
    rcases e.initialSteps.cases_tail with heq | ⟨s, _, hj⟩
    · simpa only [heq] using hinit
    · exact T.execution_preflow_jump_nonterminal h τ hτ e hh _ hj
  · have hp : i.val - 1 < e.count := by omega
    have hn : i.val - 1 + 1 < e.count := by omega
    obtain ⟨s, _, hj⟩ := Relation.TransGen.tail'_iff.mp
      (e.discreteSteps ⟨i.val - 1, hp⟩ hn)
    have heq : (⟨i.val - 1 + 1, hn⟩ : Fin e.count) = i :=
      Fin.ext (by dsimp; omega)
    rw [heq] at hj
    exact T.execution_preflow_jump_nonterminal h τ hτ e hh i hj

/-- Terminal acceptance exhausts the horizon, provided the initial mode does
not already carry `*`. Early acceptance in ordinary goal modes remains allowed. -/
theorem execution_terminal_acceptance_exhausts (hh : σ.horizon = τ)
    (hinit : e.initialState.val.1 ∉ T.terminalModes)
    (ht : e.finalState.val.1 ∈ T.terminalModes) :
    e.boundary ⟨e.count, by omega⟩ = σ.horizon := by
  have hn := T.execution_flow_nonterminal h τ hτ e hh hinit
    ⟨e.count - 1, by have := e.nonempty; omega⟩
  rw [(e.continuousStep _).1] at hn
  exact (T.execution_final_terminal_time h τ hτ e hn ht).trans hh.symm

end STLTableau.Section4.Tableau
