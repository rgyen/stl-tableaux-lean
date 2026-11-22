import STLTableaux.Automata.Recognition.SingletonEarlyRecognition

open STLTableau STLTableau.Section4

/-- Early completion preserves every old singleton and flow piece verbatim. -/
example {L R S : ℝ} (P : IntervalPartition (Set.Ico L R))
    (hLR : L ≤ R) (hRS : R < S) (hright : ∀ i, (P.interval i).right ≤ R)
    (i : Fin P.size) (t : ℝ) (hi : P.interval i = ⟨t, t, ●, ●⟩) :
    (P.appendPointSuffix hLR hRS hright).interval
      ⟨i.val, by change i.val < P.size + 2; omega⟩ = ⟨t, t, ●, ●⟩ := by
  rw [IntervalPartition.appendPointSuffix_old, hi]

/-- The unexecuted suffix is geometric coverage, not a new trace frame. -/
example {L R S : ℝ} (P : IntervalPartition (Set.Ico L R))
    (hLR : L ≤ R) (hRS : R < S) (hright : ∀ i, (P.interval i).right ≤ R) :
    ((P.appendPointSuffix hLR hRS hright).interval
      ⟨P.size + 1, by change P.size + 1 < P.size + 2; omega⟩).carrier = Set.Ioo R S := by
  rw [IntervalPartition.appendPointSuffix_suffix]
  exact MarkedInterval.carrier_eq _

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Finiteness.inputTableau_recognizes_observed_dwells_early] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
