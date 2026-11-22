import STLTableaux.ModelChecking.Preprocessing.RobustUntilElimination
import STLTableaux.ModelChecking.Preprocessing.RobustNegationNormalization
import STLTableaux.ModelChecking.Preprocessing.FalsityElimination
import STLTableaux.ModelChecking.Preprocessing.NonStrictPositive

/-! The actual checked input for the robust reduction. Normalization is
Boolean-exact; replacing false is Boolean-exact with a negative quantitative
clamp; closing positive atoms is one-way Boolean and quantitatively exact.
These distinct guarantees are deliberately not conflated. -/
namespace STLTableau
namespace FiniteSignal
variable {Var : Type*} (σ : FiniteSignal Var)

theorem robustness_normalizeForTableau (φ : Formula Var)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) φ → a.relation = .ge)
    (t : σ.Time) : σ.Robustness φ.normalizeForTableau t = σ.Robustness φ t := by
  unfold Formula.normalizeForTableau
  rw [σ.robustness_normalizeMixedNegation _ (φ.eliminateTimedUntil_atoms_ge nonStrict)
    false t]
  exact σ.robustness_eliminateTimedUntil φ nonStrict t

end FiniteSignal
namespace Formula
variable {Var : Type*}

/-- Normalize, replace falsity leaves syntactically, and close atomic margins.
Readiness and non-strictness are derived, not additional admission premises. -/
noncomputable def closedTableauInput (φ : Formula Var) : NormalizedInput Var :=
  let p := eliminateFalsity φ.normalizeForTableau (mixedReady_normalizeForTableau φ)
  ⟨p.val.closeNonStrictAtoms, p.property.closeNonStrictAtoms⟩

theorem closedTableauInput_atoms_ge (φ : Formula Var) (a : AtomicProposition Var)
    (sub : IsSubformula (.atom a) (closedTableauInput φ).val) : a.relation = .ge :=
  closeNonStrictAtoms_all_ge _ a sub

theorem closedTableauInput_functions_continuous (φ : Formula Var)
    (nonStrict : ∀ a, IsSubformula (.atom a) φ → a.relation = .ge)
    (functions : ∀ a, IsSubformula (.atom a) φ → Continuous a.function)
    (a : AtomicProposition Var)
    (sub : IsSubformula (.atom a) (closedTableauInput φ).val) : Continuous a.function := by
  apply closeNonStrictAtoms_functions_continuous _ ?_ a sub
  apply eliminateFalsity_atoms_continuous
  exact normalizeMixedNegation_functions_continuous _
    (φ.eliminateTimedUntil_atoms_ge nonStrict)
    (φ.eliminateTimedUntil_functions_continuous functions) false

/-- Positive atom closure retains every original Boolean witness.
The reverse implication is intentionally not asserted. -/
theorem satisfies_closedTableauInput_of_satisfies (φ : Formula Var)
    (σ : FiniteSignal Var) (t : σ.Time) (truth : σ.Satisfies φ t) :
    σ.Satisfies (closedTableauInput φ).val t := by
  let mixed := mixedReady_normalizeForTableau φ
  let p := eliminateFalsity φ.normalizeForTableau mixed
  apply p.property.satisfies_closeNonStrictAtoms σ t
  apply (satisfies_eliminateFalsity φ.normalizeForTableau mixed σ t).mpr
  exact (satisfies_normalizeForTableau φ σ t).mpr truth

/-- A witness for the actual closed input entails a nonnegative robustness
bound for the original formula, including normalized falsity branches. -/
theorem robustness_nonneg_of_satisfies_closedTableauInput (φ : Formula Var)
    (nonStrict : ∀ a, IsSubformula (.atom a) φ → a.relation = .ge)
    (σ : FiniteSignal Var) (t : σ.Time)
    (truth : σ.Satisfies (closedTableauInput φ).val t) :
    0 ≤ σ.Robustness φ t := by
  have nonneg := σ.robustness_nonneg_of_satisfies _ t truth
  change 0 ≤ σ.Robustness
    ((eliminateFalsity φ.normalizeForTableau
      (mixedReady_normalizeForTableau φ)).val.closeNonStrictAtoms) t at nonneg
  rw [σ.robustness_closeNonStrictAtoms] at nonneg
  have original := robustness_eliminateFalsity_nonneg_reflect φ.normalizeForTableau
    (mixedReady_normalizeForTableau φ) σ t nonneg
  simpa only [σ.robustness_normalizeForTableau φ nonStrict t] using original

/-- The tableau input obtained from the negation of the `ε`-strengthening.
The no-goal direction of the robust reduction uses finite variability
of this input. -/
noncomputable def robustCounterInput (φ : Formula Var) (ε : ℝ) : NormalizedInput Var :=
  closedTableauInput (.neg (φ.thresholdShift ε))

theorem robustCounterInput_functions_continuous (φ : Formula Var) (ε : ℝ)
    (nonStrict : ∀ a, IsSubformula (.atom a) φ → a.relation = .ge)
    (functions : ∀ a, IsSubformula (.atom a) φ → Continuous a.function)
    (a : AtomicProposition Var)
    (sub : IsSubformula (.atom a) (robustCounterInput φ ε).val) : Continuous a.function := by
  apply closedTableauInput_functions_continuous _ ?_ ?_ a sub
  · intro b hb
    cases hb with
    | neg hb => exact φ.thresholdShift_atoms_ge nonStrict ε b hb
  · intro b hb
    cases hb with
    | neg hb => exact φ.thresholdShift_functions_continuous functions ε b hb

theorem satisfies_robustCounterInput_of_violation (φ : Formula Var) (ε : ℝ)
    (σ : FiniteSignal Var) (t : σ.Time) (violation : ¬ σ.Satisfies (φ.thresholdShift ε) t) :
    σ.Satisfies (robustCounterInput φ ε).val t :=
  satisfies_closedTableauInput_of_satisfies _ σ t violation

theorem robustness_le_of_satisfies_robustCounterInput (φ : Formula Var) (ε : ℝ)
    (nonStrict : ∀ a, IsSubformula (.atom a) φ → a.relation = .ge)
    (σ : FiniteSignal Var) (t : σ.Time)
    (truth : σ.Satisfies (robustCounterInput φ ε).val t) :
    σ.Robustness φ t ≤ (ε : EReal) := by
  have ge : ∀ a, IsSubformula (.atom a) (.neg (φ.thresholdShift ε)) → a.relation = .ge := by
    intro a sub
    cases sub with
    | neg sub => exact φ.thresholdShift_atoms_ge nonStrict ε a sub
  have nonneg := robustness_nonneg_of_satisfies_closedTableauInput _ ge σ t truth
  change 0 ≤ -σ.Robustness (φ.thresholdShift ε) t at nonneg
  have upper := EReal.neg_nonneg.mp nonneg
  rw [σ.robustness_thresholdShift φ nonStrict ε t] at upper
  simpa only [zero_add] using
    (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot ε))
      (Or.inl (EReal.coe_ne_top ε))).mp upper

run_elab do
  for name in #[``FiniteSignal.robustness_normalizeForTableau,
      ``closedTableauInput_atoms_ge, ``closedTableauInput_functions_continuous,
      ``satisfies_closedTableauInput_of_satisfies,
      ``robustness_nonneg_of_satisfies_closedTableauInput,
      ``robustCounterInput_functions_continuous, ``satisfies_robustCounterInput_of_violation,
      ``robustness_le_of_satisfies_robustCounterInput] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end Formula
end STLTableau
