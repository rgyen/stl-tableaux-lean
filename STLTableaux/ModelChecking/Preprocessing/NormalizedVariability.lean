import STLTableaux.ModelChecking.Preprocessing.NormalizedInputVariability
import STLTableaux.ModelChecking.Preprocessing.NormalizedAtomVariability

/-! The Boolean normalization in Theorem 5.7 preserves finite variability
under the same checked-input and non-strict-atom conditions as the reduction.
This does not change any numerical threshold. -/
namespace STLTableau.FiniteSignal

variable {Var : Type*}

/-- The fully stable partition of `φ` controls the atomic tests of the
normalized negation. The temporal grammar then yields a
fully stable partition for the whole normalized formula. -/
theorem HasFiniteVariability.normalizeViolation {σ : FiniteSignal Var} {φ : Formula Var}
    (fv : σ.HasFiniteVariability φ)
    (ready : (Formula.neg φ).normalizeForTableau.NormalizedReady)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) (Formula.neg φ).normalizeForTableau →
      a.relation = .ge) :
    σ.HasFiniteVariability (Formula.neg φ).normalizeForTableau :=
  ready.hasFiniteVariability_of_atoms (fun a sub => fv.normalizeViolation_atom sub (nonStrict a sub))

run_elab do
  for ax in ← Lean.collectAxioms ``HasFiniteVariability.normalizeViolation do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "normalizeViolation uses unexpected axiom {ax}"

end STLTableau.FiniteSignal
