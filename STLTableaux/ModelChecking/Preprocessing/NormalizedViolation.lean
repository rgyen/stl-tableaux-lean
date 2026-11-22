import STLTableaux.ModelChecking.Preprocessing.NormalizedInput
import STLTableaux.Syntax.InputSyntax

/-! Normalization produces a formula Boolean-equivalent to the original
negation and fixes formulas already in the normalized input grammar. -/
namespace STLTableau.Formula
variable {Var : Type*}

theorem satisfies_normalizeViolation (φ : Formula Var) (σ : FiniteSignal Var)
    (t : σ.Time) :
    σ.Satisfies (Formula.neg φ).normalizeForTableau t ↔ ¬ σ.Satisfies φ t := by
  exact satisfies_normalizeForTableau (.neg φ) σ t

private theorem eliminateTimedUntil_until_zero (φ ψ : Formula Var) :
    (untimedUntil φ ψ).eliminateTimedUntil =
      untimedUntil φ.eliminateTimedUntil ψ.eliminateTimedUntil := by
  cases φ <;> simp [Formula.untimedUntil, Formula.eliminateTimedUntil, Formula.eliminateUntil,
    Formula.eventually]

theorem NormalizedReady.eliminateTimedUntil_eq {φ : Formula Var} (h : φ.NormalizedReady) :
    φ.eliminateTimedUntil = φ := by
  induction h with
  | truth => rfl
  | atom => rfl
  | and _ _ ihφ ihψ => simp only [eliminateTimedUntil, ihφ, ihψ]
  | or _ _ ihφ ihψ => simp only [Formula.or, eliminateTimedUntil, ihφ, ihψ]
  | «until» _ _ ihφ ihψ => rw [eliminateTimedUntil_until_zero, ihφ, ihψ]
  | release _ _ ihφ ihψ =>
    simp [Formula.release, Formula.eliminateTimedUntil, Formula.eliminateUntil,
      Formula.untimedUntil, ihφ, ihψ]
  | eventually I _ ih => simp only [Formula.eventually, Formula.eliminateTimedUntil, ih]
  | always I _ ih =>
    simp only [Formula.always, Formula.eventually, Formula.eliminateTimedUntil, ih]

theorem NormalizedReady.normalizeMixedNegation_eq {φ : Formula Var} (h : φ.NormalizedReady) :
    φ.normalizeMixedNegation false = φ := by
  induction h with
  | truth => rfl
  | atom => rfl
  | and _ _ ihφ ihψ => simp [Formula.normalizeMixedNegation, ihφ, ihψ]
  | or _ _ ihφ ihψ =>
    simp [Formula.or, Formula.normalizeMixedNegation, ihφ, ihψ]
  | «until» _ _ ihφ ihψ =>
    simp [Formula.untimedUntil, Formula.normalizeMixedNegation, ihφ, ihψ]
  | release _ _ ihφ ihψ =>
    simp [Formula.release, Formula.normalizeMixedNegation, ihφ, ihψ]
  | eventually I _ ih =>
    simp [Formula.eventually, Formula.normalizeMixedNegation, ih]
  | always I _ ih =>
    simp [Formula.always, Formula.eventually, Formula.normalizeMixedNegation, ih]

theorem NormalizedReady.normalizeForTableau_eq {φ : Formula Var} (h : φ.NormalizedReady) :
    φ.normalizeForTableau = φ := by
  rw [normalizeForTableau, h.eliminateTimedUntil_eq, h.normalizeMixedNegation_eq]

/-- For a normalized input, normalizing its double negation
requires no new grammar, stability, atom-relation or function assumption. -/
theorem NormalizedReady.normalize_double_neg_eq {φ : Formula Var} (h : φ.NormalizedReady) :
    (Formula.neg (Formula.neg φ)).normalizeForTableau = φ := by
  simp only [normalizeForTableau, eliminateTimedUntil, h.eliminateTimedUntil_eq,
    normalizeMixedNegation, Bool.not_false, Bool.not_true]
  exact h.normalizeMixedNegation_eq

run_elab do
  for name in #[``satisfies_normalizeViolation, ``NormalizedReady.eliminateTimedUntil_eq,
      ``NormalizedReady.normalizeMixedNegation_eq, ``NormalizedReady.normalizeForTableau_eq,
      ``NormalizedReady.normalize_double_neg_eq] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"
end STLTableau.Formula
