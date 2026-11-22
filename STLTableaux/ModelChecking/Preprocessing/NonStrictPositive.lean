import STLTableaux.ModelChecking.Preprocessing.NonStrictAtoms
import STLTableaux.Semantics.Robustness.RobustnessShift

/-! Positive normalized syntax permits one-way Boolean atom closure. Quantitative
margin implications below apply to arbitrary core formulas, but do not assert
Boolean equivalence, finite-variability preservation, or a uniform margin. -/
namespace STLTableau
namespace Formula
variable {Var : Type*}

/-- Positive operators preserve the atomwise implication to closed margins.
The restriction to checked positive syntax is essential under negation. -/
theorem NormalizedReady.satisfies_closeNonStrictAtoms {φ : Formula Var}
    (ready : φ.NormalizedReady) (σ : FiniteSignal Var) (t : σ.Time)
    (truth : σ.Satisfies φ t) : σ.Satisfies φ.closeNonStrictAtoms t := by
  induction ready generalizing t with
  | truth => trivial
  | atom a => exact a.holds_closeNonStrict _ truth
  | and _ _ left right => exact ⟨left t truth.1, right t truth.2⟩
  | @or φ ψ _ _ left right =>
    change σ.Satisfies (Formula.or φ.closeNonStrictAtoms ψ.closeNonStrictAtoms) t
    apply (σ.satisfies_or _ _ _).2
    rcases (σ.satisfies_or _ _ _).1 truth with h | h
    · exact Or.inl (left t h)
    · exact Or.inr (right t h)
  | «until» _ _ left right =>
    obtain ⟨u, inside, goal, earlier⟩ := truth
    exact ⟨u, inside, right u goal, fun s lower upper => left s (earlier s lower upper)⟩
  | @release φ ψ _ _ left right =>
    change ¬ σ.Satisfies (.until (.unbounded 0)
      (.neg φ.closeNonStrictAtoms) (.neg ψ.closeNonStrictAtoms)) t
    intro counter
    apply truth
    obtain ⟨u, inside, goal, earlier⟩ := counter
    refine ⟨u, inside, ?_, ?_⟩
    · exact fun h => goal (right u h)
    · intro s lower upper h
      exact earlier s lower upper (left s h)
  | @eventually I φ _ child =>
    change σ.Satisfies (Formula.eventually I φ.closeNonStrictAtoms) t
    obtain ⟨u, inside, goal⟩ := (σ.satisfies_eventually_iff _ _ _).1 truth
    exact (σ.satisfies_eventually_iff _ _ _).2 ⟨u, inside, child u goal⟩
  | @always I φ _ child =>
    change σ.Satisfies (Formula.always I φ.closeNonStrictAtoms) t
    apply (σ.satisfies_always_iff _ _ _).2
    intro u inside
    exact child u ((σ.satisfies_always_iff _ _ _).1 truth u inside)
end Formula

namespace FiniteSignal
variable {Var : Type*} (σ : FiniteSignal Var)

/-- A strictly positive closed-margin strengthening entails the original
Boolean formula, even for formulas outside positive normalized syntax. -/
theorem satisfies_of_closed_strengthening (φ : Formula Var) (δ : ℝ)
    (positive : 0 < δ) (t : σ.Time)
    (truth : σ.Satisfies (φ.closeNonStrictAtoms.thresholdShift δ) t) :
    σ.Satisfies φ t := by
  have lower := σ.robustness_ge_of_satisfies_strengthening φ.closeNonStrictAtoms
    φ.closeNonStrictAtoms_all_ge δ t truth
  rw [σ.robustness_closeNonStrictAtoms φ t] at lower
  exact σ.satisfies_of_robustness_pos φ t ((EReal.coe_pos.mpr positive).trans_le lower)

/-- A quantitative margin above δ gives the Boolean closed strengthening.
No finite-variability or Boolean-equivalence premise is used. -/
theorem satisfies_closed_strengthening_of_robustness_gt (φ : Formula Var) (δ : ℝ)
    (t : σ.Time) (margin : (δ : EReal) < σ.Robustness φ t) :
    σ.Satisfies (φ.closeNonStrictAtoms.thresholdShift δ) t := by
  apply σ.satisfies_strengthening_of_robustness_gt φ.closeNonStrictAtoms
    φ.closeNonStrictAtoms_all_ge δ t
  simpa only [σ.robustness_closeNonStrictAtoms φ t] using margin
end FiniteSignal

run_elab do
  for name in #[``Formula.NormalizedReady.satisfies_closeNonStrictAtoms,
      ``FiniteSignal.satisfies_of_closed_strengthening,
      ``FiniteSignal.satisfies_closed_strengthening_of_robustness_gt] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end STLTableau
