import STLTableaux.Automata.Recognition.TableauRealClockSchedule

open STLTableau STLTableau.Section4

variable {Clock Var State : Type*} (T : Tableau Clock Var State)

/-- A negative actual coordinate is retained, and flow adds time to it.
There is no implicit clipping into NNReal. -/
theorem negative_coordinate_flows (incoming : ℕ → EdgeLabel Clock)
    (duration : ℕ → NNReal) (v : T.HAVar → ℝ) (c : T.clocks)
    (hv : v (.inr (.inl c)) = -7) (hr : (incoming 0).resets.value c.val = none) :
    T.realClockSchedule incoming duration v 1 c.val = -7 + duration 0 := by
  rw [T.realClockSchedule_succ]
  simp only [Trace.realReset, hr]
  rw [T.realClockSchedule_zero, hv]

/-- Even an undeclared clock is advanced after its initial zero extension.
Extending every frame independently with zero would violate this equation. -/
theorem undeclared_coordinate_flows (incoming : ℕ → EdgeLabel Clock)
    (duration : ℕ → NNReal) (v : T.HAVar → ℝ) (c : Clock)
    (hc : c ∉ T.clocks) (hr : (incoming 0).resets.value c = none) :
    T.realClockSchedule incoming duration v 1 c = duration 0 := by
  classical
  rw [T.realClockSchedule_succ]
  simp only [Trace.realReset, hr]
  change (if h : c ∈ T.clocks then v (.inr (.inl ⟨c, h⟩)) else 0) +
    (duration 0 : ℝ) = _
  rw [dif_neg hc, zero_add]

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Tableau.realClockSchedule_agrees, ``Tableau.realClockSchedule_guards,
      ``Tableau.initial_continuousStep_realClocks,
      ``Tableau.discreteStep_continuousStep_realClocks,
      ``negative_coordinate_flows, ``undeclared_coordinate_flows] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
