import STLTableaux.Automata.Recognition.SingletonRecognition

open STLTableau STLTableau.Section4

/-- A singleton frame does not introduce a continuous-evolution assumption. -/
example {Clock Var State : Type*} (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    (s : (T.toAutomaton h τ hτ).State) : T.DwellStep h τ hτ s s 0 :=
  Or.inl ⟨rfl, rfl⟩

/-- Zero dwell preserves the current clock values; the next jump may still
reset them. No sign condition on the real-valued coordinates is needed. -/
example {Clock Var State : Type*} (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {s t : (T.toAutomaton h τ hτ).State}
    (hd : T.DwellStep h τ hτ s t 0) (c : T.clocks) :
    t.val.2 (.inr (.inl c)) = s.val.2 (.inr (.inl c)) := by
  simpa using hd.clock_eq T h τ hτ c

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Tableau.DwellStep.mode_eq, ``Tableau.DwellStep.clock_eq,
      ``Tableau.DwellStep.globalClock_eq, ``Tableau.dwell_entry_globalClock,
      ``Tableau.dwell_entry_nonterminal,
      ``IntervalPartition.singletonCompatible_boundary_lt_last,
      ``Tableau.exists_dwell_schedule,
      ``Finiteness.inputTableau_recognizes_singleton_path_at_horizon,
      ``Finiteness.inputTableau_recognizes_observed_dwells_at_horizon] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
