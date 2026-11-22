import STLTableaux.Automata.Translation.PrelimTableauAutomata

namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
variable (h : T.TranslationReady) (τ : ℝ)
local notation "H" => (T.prelimAutomaton h τ)

theorem prelim_jump_global {a b : (H).State} (step : (H).DiscreteStep a b) :
    b.val.2 (.inl T.globalClock) = a.val.2 (.inl T.globalClock) := by
  obtain ⟨_, _, _, _, _, _, _, hg, _⟩ := step
  exact hg

theorem prelim_chain_global {a b : (H).State}
    (steps : Relation.ReflTransGen (H).DiscreteStep a b) :
    b.val.2 (.inl T.globalClock) = a.val.2 (.inl T.globalClock) := by
  induction steps with
  | refl => rfl
  | tail _ step ih => exact (T.prelim_jump_global h τ step).trans ih

theorem prelim_flow_global {σ : FiniteSignal T.TypedVar} (e : (H).PrelimExecution σ)
    (i : Fin e.count) : (e.finish i).val.2 (.inl T.globalClock) =
      (e.start i).val.2 (.inl T.globalClock) + e.duration i := by
  let u : Set.Icc (0 : ℝ) (e.duration i) := ⟨e.duration i, by simp⟩
  have step := e.continuousStep i
  have hv := ((step.2.2.2 u).1).2.1
  rw [show e.curve i u = (e.finish i).val.2 from step.2.2.1] at hv
  exact hv

theorem prelim_entry_time {σ : FiniteSignal T.TypedVar} (e : (H).PrelimExecution σ)
    (i : Fin e.count) :
    (e.start i).val.2 (.inl T.globalClock) = e.boundary i.castSucc := by
  obtain ⟨k, hk⟩ := i
  induction k with
  | zero =>
    obtain ⟨_, _, _, _, hv, _, _⟩ := e.initial_mem
    have hg := congrFun hv T.globalClock
    change e.initialState.val.2 (.inl T.globalClock) = 0 at hg
    exact (T.prelim_chain_global h τ e.initialSteps).trans (hg.trans e.first_zero.symm)
  | succ k ih =>
    let j : Fin e.count := ⟨k, by omega⟩
    have hg := T.prelim_chain_global h τ (e.discreteSteps j hk).to_reflTransGen
    have hf := T.prelim_flow_global h τ e j
    have hd := e.duration_eq j
    have hp := ih j.isLt
    change (e.start ⟨k + 1, hk⟩).val.2 (.inl T.globalClock) =
      e.boundary ⟨k + 1, by omega⟩
    rw [hg, hf, hp, hd]
    change e.boundary j.castSucc + (e.boundary j.succ - e.boundary j.castSucc) =
      e.boundary j.succ
    ring

theorem prelim_jump_target_nonterminal {a b : (H).State}
    (step : (H).DiscreteStep a b) (early : b.val.2 (.inl T.globalClock) < τ) :
    b.val.1 ∉ T.terminalModes := by
  obtain ⟨_, _, _, _, _, _, _, _, _, guard, _⟩ := step
  exact fun ht => early.not_ge (guard ht)

private theorem chain_nonterminal {a b : (H).State}
    (steps : Relation.ReflTransGen (H).DiscreteStep a b)
    (first : a.val.1 ∉ T.terminalModes) (early : b.val.2 (.inl T.globalClock) < τ) :
    b.val.1 ∉ T.terminalModes := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp steps with eq | chain
  · exact eq ▸ first
  · obtain ⟨s, _, step⟩ := Relation.TransGen.tail'_iff.mp chain
    exact T.prelim_jump_target_nonterminal h τ step early

theorem prelim_start_nonterminal {σ : FiniteSignal T.TypedVar}
    (e : (H).PrelimExecution σ) (hh : σ.horizon = τ)
    (first : e.initialState.val.1 ∉ T.terminalModes) (i : Fin e.count) :
    (e.start i).val.1 ∉ T.terminalModes := by
  have early : (e.start i).val.2 (.inl T.globalClock) < τ := by
    rw [T.prelim_entry_time h τ e i]
    exact (e.entry_lt_horizon i).trans_eq hh
  obtain ⟨k, hk⟩ := i
  cases k with
  | zero => exact T.chain_nonterminal h τ e.initialSteps first early
  | succ k =>
    let j : Fin e.count := ⟨k, by omega⟩
    obtain ⟨s, _, step⟩ := Relation.TransGen.tail'_iff.mp (e.discreteSteps j hk)
    exact T.prelim_jump_target_nonterminal h τ step early

/-- No star mode can be visited, including skipped intermediate modes:
all jump blocks precede a positive flow whose start time is below τ. -/
theorem prelim_visits_nonterminal {σ : FiniteSignal T.TypedVar}
    (e : (H).PrelimExecution σ) (hh : σ.horizon = τ)
    (first : e.initialState.val.1 ∉ T.terminalModes) (q : T.states)
    (visit : e.VisitsMode q) : q ∉ T.terminalModes := by
  rcases visit with ⟨i, eq⟩ | ⟨s, eq, pre, post⟩ | ⟨i, hi, s, eq, pre, post⟩
  · exact eq ▸ T.prelim_start_nonterminal h τ e hh first i
  · have early : s.val.2 (.inl T.globalClock) < τ := by
      rw [← T.prelim_chain_global h τ post, T.prelim_entry_time h τ e _]
      exact (e.entry_lt_horizon _).trans_eq hh
    exact eq ▸ T.chain_nonterminal h τ pre first early
  · have early : s.val.2 (.inl T.globalClock) < τ := by
      rw [← T.prelim_chain_global h τ post, T.prelim_entry_time h τ e _]
      exact (e.entry_lt_horizon _).trans_eq hh
    have start := T.prelim_start_nonterminal h τ e hh first i
    have source : (e.finish i).val.1 ∉ T.terminalModes := (e.continuousStep i).1 ▸ start
    exact eq ▸ T.chain_nonterminal h τ pre source early

end STLTableau.Section4.Tableau
