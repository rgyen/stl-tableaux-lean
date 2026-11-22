import STLTableaux.ModelChecking.Preprocessing.Normalization
import STLTableaux.Semantics.Robustness.RobustnessShift
import STLTableaux.ModelChecking.Preprocessing.ThresholdPreprocessingMetadata

/-! Timed-until preprocessing commutes with signed threshold shifts.
Consequently its Boolean correctness determines exactly the same quantitative
semantics, by the finite-real cuts of extended-real robustness. -/
namespace STLTableau.Formula
variable {Var : Type*}

theorem eliminateUntil_thresholdShift (I : TimeInterval) (φ ψ : Formula Var) (ε : ℝ) :
    (eliminateUntil I φ ψ).thresholdShift ε =
      eliminateUntil I (φ.thresholdShift ε) (ψ.thresholdShift ε) := by
  classical
  cases I with
  | bounded I =>
    simp only [eliminateUntil]
    split <;> simp [always, eventually, untimedUntil, thresholdShift]
  | unbounded a =>
    simp only [eliminateUntil]
    split <;> simp [always, eventually, untimedUntil, thresholdShift]

theorem eliminateTimedUntil_thresholdShift (φ : Formula Var) (ε : ℝ) :
    (φ.thresholdShift ε).eliminateTimedUntil = φ.eliminateTimedUntil.thresholdShift ε := by
  induction φ generalizing ε with
  | truth => rfl
  | atom a => rfl
  | neg φ ih => simp only [thresholdShift, eliminateTimedUntil, ih]
  | and φ ψ ihφ ihψ => simp only [thresholdShift, eliminateTimedUntil, ihφ, ihψ]
  | «until» I φ ψ ihφ ihψ =>
    cases φ <;> first
      | exact congrArg (eventually I) (ihψ ε)
      | exact (congrArg₂ (eliminateUntil I) (ihφ ε) (ihψ ε)).trans
          (eliminateUntil_thresholdShift I _ _ ε).symm

end STLTableau.Formula

namespace STLTableau.FiniteSignal
variable {Var : Type*}

private theorem ereal_le_of_real_cuts {a b : EReal}
    (cuts : ∀ r : ℝ, (r : EReal) < a → (r : EReal) ≤ b) : a ≤ b := by
  by_contra notLe
  obtain ⟨r, lower, upper⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge notLe)
  exact (not_le_of_gt lower) (cuts r upper)

/-- The already proved Boolean preprocessing is exact quantitatively too.
Its threshold commutation identifies every finite-real robustness cut. -/
theorem robustness_eliminateTimedUntil (σ : FiniteSignal Var) (φ : Formula Var)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) φ → a.relation = .ge)
    (t : σ.Time) : σ.Robustness φ.eliminateTimedUntil t = σ.Robustness φ t := by
  have processed := φ.eliminateTimedUntil_atoms_ge nonStrict
  apply le_antisymm
  · apply ereal_le_of_real_cuts
    intro r lower
    have truth := σ.satisfies_strengthening_of_robustness_gt _ processed r t lower
    rw [← φ.eliminateTimedUntil_thresholdShift r] at truth
    exact σ.robustness_ge_of_satisfies_strengthening φ nonStrict r t
      ((σ.satisfies_eliminateTimedUntil _ t).mp truth)
  · apply ereal_le_of_real_cuts
    intro r lower
    have truth := σ.satisfies_strengthening_of_robustness_gt φ nonStrict r t lower
    have converted := (σ.satisfies_eliminateTimedUntil _ t).mpr truth
    rw [φ.eliminateTimedUntil_thresholdShift r] at converted
    exact σ.robustness_ge_of_satisfies_strengthening _ processed r t converted

run_elab do
  for name in #[``Formula.eliminateUntil_thresholdShift,
      ``Formula.eliminateTimedUntil_thresholdShift, ``robustness_eliminateTimedUntil] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end STLTableau.FiniteSignal
