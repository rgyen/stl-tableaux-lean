import STLTableaux.Automata.Execution.HybridAutomata

open STLTableau

namespace HybridAutomataDiagnostics

/-- Signals may differ strictly after the stopping time, but must agree at
the observed early endpoint as well as throughout the executed prefix. -/
theorem prefix_congr {Mode Label Var : Type*}
    {H : HybridAutomaton Mode Label Var} {σ σ' : FiniteSignal Var}
    (e : H.Execution σ) (horizon : σ'.horizon = σ.horizon)
    (hprefix : ∀ t : σ'.Time,
      t.val ≤ e.boundary ⟨e.count, by omega⟩ →
      σ'.value t = σ.value ⟨t.val, by simpa only [horizon] using t.property⟩) :
    Nonempty (H.Execution σ') := by
  refine ⟨{
    count := e.count
    nonempty := e.nonempty
    initialState := e.initialState
    initial_mem := e.initial_mem
    initial_signal_eq := by
      have nonnegative := e.increasing.monotone
        (show (0 : Fin (e.count + 1)) ≤ ⟨e.count, by omega⟩ from Fin.zero_le _)
      have start : e.boundary 0 = 0 := e.first_zero
      rw [start] at nonnegative
      exact (hprefix ⟨0, le_rfl, σ'.horizon_pos⟩ nonnegative).trans e.initial_signal_eq
    start := e.start
    finish := e.finish
    boundary := e.boundary
    first_zero := e.first_zero
    increasing := e.increasing
    last_le_horizon := by simpa only [horizon] using e.last_le_horizon
    duration := e.duration
    duration_eq := e.duration_eq
    curve := e.curve
    continuousStep := e.continuousStep
    initialSteps := e.initialSteps
    discreteSteps := e.discreteSteps
    finalState := e.finalState
    finalSteps := e.finalSteps
    final_signal_eq := by
      intro t ht
      rw [hprefix t (le_of_eq ht)]
      exact e.final_signal_eq _ ht
    signal_eq := ?_ }⟩
  intro i t ht positive
  have hlast : e.boundary ⟨i.val + 1, by omega⟩ ≤
      e.boundary ⟨e.count, by omega⟩ :=
    e.increasing.monotone (by change i.val + 1 ≤ e.count; omega)
  rw [hprefix t (ht.2.le.trans hlast)]
  exact e.signal_eq i _ ht positive

/-- Closed-endpoint invariants rule out reaching the horizon while remaining
in a mode whose global-clock invariant is strict. -/
theorem no_closed_step_to_strict_horizon {Mode Label Var : Type*}
    (H : HybridAutomaton Mode Label Var) (s s' : H.State)
    (r : NNReal) (γ : Set.Icc (0 : ℝ) r → Var → ℝ) (c : Var) (τ : ℝ)
    (hinv : ∀ v, (s.val.1, v) ∈ H.invariant → v c < τ)
    (hend : γ ⟨r, by simp⟩ c = τ) :
    ¬ H.ContinuousStep s s' r γ := by
  intro h
  have hlt := hinv _ (h.2.2.2 ⟨r, by simp⟩).2
  rw [hend] at hlt
  exact (lt_irrefl τ) hlt

end HybridAutomataDiagnostics

namespace HybridAutomataBoundaryChecks

/-- At the horizon, an otherwise enabled jump into `*` is admitted.
This also checks that the new guard convention is not vacuously blocking all jumps. -/
theorem terminal_jump_allowed {Mode Label Var : Type*}
    (H : HybridAutomaton Mode Label Var) (terminal : Set Mode) (c : Var) (τ : ℝ)
    (s s' : (H.withHorizon terminal c τ).State)
    (e : {e // e ∈ H.edge})
    (hsrc : e.val.1 = s.val.1) (htgt : e.val.2.2 = s'.val.1)
    (hj : H.jump e s.val s'.val) (ht : s'.val.1 ∈ terminal)
    (hc : s'.val.2 c = τ) :
    (H.withHorizon terminal c τ).DiscreteStep s s' := by
  refine ⟨e, hsrc, htgt, hj, ?_, ?_⟩
  · intro _
    exact le_of_eq hc.symm
  · intro hn
    exact (hn ht).elim

theorem nonterminal_jump_at_horizon_forbidden {Mode Label Var : Type*}
    (H : HybridAutomaton Mode Label Var) (terminal : Set Mode) (c : Var) (τ : ℝ)
    (s s' : (H.withHorizon terminal c τ).State)
    (ht : s'.val.1 ∉ terminal) (hc : s'.val.2 c = τ) :
    ¬ (H.withHorizon terminal c τ).DiscreteStep s s' := by
  intro h
  have hlt := H.withHorizon_nonterminal_entry_lt terminal c τ h ht
  rw [hc] at hlt
  exact (lt_irrefl τ) hlt

/-- Appending a discrete tail does not extend the executed time interval. -/
theorem final_tail_preserves_boundaries {Mode Label Var : Type*}
    {H : HybridAutomaton Mode Label Var} {σ : FiniteSignal Var}
    (e : H.Execution σ) (s : H.State)
    (h : Relation.ReflTransGen H.DiscreteStep e.finalState s)
    (hobs : ∀ t : σ.Time, t.val = e.boundary ⟨e.count, by omega⟩ →
      σ.value t = s.val.2) :
    (e.appendFinalSteps s h hobs).boundary = e.boundary := rfl

end HybridAutomataBoundaryChecks

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``HybridAutomataDiagnostics.prefix_congr,
      ``HybridAutomataDiagnostics.no_closed_step_to_strict_horizon,
      ``HybridAutomaton.withHorizon_nonterminal_entry_lt,
      ``HybridAutomaton.withHorizon_terminal_entry_eq,
      ``HybridAutomaton.Execution.reaches_of_finalSteps,
      ``HybridAutomaton.Execution.appendFinalStepsAtHorizon,
      ``HybridAutomataBoundaryChecks.terminal_jump_allowed,
      ``HybridAutomataBoundaryChecks.nonterminal_jump_at_horizon_forbidden,
      ``HybridAutomataBoundaryChecks.final_tail_preserves_boundaries] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
