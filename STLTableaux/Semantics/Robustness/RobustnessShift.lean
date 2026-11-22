import STLTableaux.Semantics.Robustness.Robustness
import STLTableaux.Semantics.Stability.Stability
import STLTableaux.Syntax.InputSyntax

/-! The appendix's signed atomic threshold shift: positive epsilon strengthens
and negative epsilon weakens, with polarity reversed below negation.
The quantitative identity is asserted for the ge atomic syntax.
Finite translations preserve even empty suprema/infima via an order isomorphism. -/
namespace STLTableau.Formula
variable {Var : Type*}

def thresholdShift : Formula Var → ℝ → Formula Var
  | .truth, _ => .truth
  | .atom a, ε => .atom {a with function := fun v => a.function v - ε}
  | .neg φ, ε => .neg (φ.thresholdShift (-ε))
  | .and φ ψ, ε => .and (φ.thresholdShift ε) (ψ.thresholdShift ε)
  | .until I φ ψ, ε => .until I (φ.thresholdShift ε) (ψ.thresholdShift ε)

scoped[STL] notation:max φ "⁺[" ε "]" => STLTableau.Formula.thresholdShift φ ε
scoped[STL] notation:max φ "⁻[" ε "]" => STLTableau.Formula.thresholdShift φ (-ε)

theorem NormalizedReady.thresholdShift {φ : Formula Var} (ready : φ.NormalizedReady) (ε : ℝ) :
    (φ.thresholdShift ε).NormalizedReady := by
  induction ready generalizing ε with
  | truth => exact .truth
  | atom a => exact .atom _
  | and _ _ ihφ ihψ => exact .and (ihφ ε) (ihψ ε)
  | or _ _ ihφ ihψ =>
    simpa only [Formula.or, Formula.thresholdShift, neg_neg] using
      (NormalizedReady.or (ihφ ε) (ihψ ε))
  | «until» _ _ ihφ ihψ => exact .until (ihφ ε) (ihψ ε)
  | release _ _ ihφ ihψ =>
    simpa only [Formula.release, Formula.thresholdShift, neg_neg] using
      (NormalizedReady.release (ihφ ε) (ihψ ε))
  | eventually I _ ih => exact .eventually I (ih ε)
  | always I _ ih =>
    simpa only [Formula.always, Formula.eventually, Formula.thresholdShift, neg_neg] using
      (NormalizedReady.always I (ih ε))
end STLTableau.Formula

namespace STLTableau.FiniteSignal
variable {Var : Type*} (σ : FiniteSignal Var)

private noncomputable def realSubOrderIso (ε : ℝ) : EReal ≃o EReal where
  toFun x := x - (ε : EReal)
  invFun x := x + (ε : EReal)
  left_inv _ := EReal.sub_add_cancel
  right_inv _ := EReal.add_sub_cancel_right
  map_rel_iff' := by
    intro x y
    change x + ((-ε : ℝ) : EReal) ≤ y + ((-ε : ℝ) : EReal) ↔ x ≤ y
    exact (EReal.addLECancellable_coe (-ε)).add_le_add_iff_right

private theorem real_sub_min (x y : EReal) (ε : ℝ) :
    min (x - ε) (y - ε) = min x y - ε :=
  ((realSubOrderIso ε).map_inf x y).symm

private theorem real_sub_iSup {ι : Sort*} (f : ι → EReal) (ε : ℝ) :
    (⨆ i, f i - ε) = (⨆ i, f i) - ε :=
  ((realSubOrderIso ε).map_iSup f).symm

private theorem real_sub_iInf {ι : Sort*} (f : ι → EReal) (ε : ℝ) :
    (⨅ i, f i - ε) = (⨅ i, f i) - ε :=
  ((realSubOrderIso ε).map_iInf f).symm

private theorem neg_sub_neg_real (x : EReal) (ε : ℝ) :
    -(x - ((-ε : ℝ) : EReal)) = -x - (ε : EReal) := by
  cases x with
  | bot => simp
  | top => simp
  | coe x =>
    change ((-(x - -ε) : ℝ) : EReal) = ((-x - ε : ℝ) : EReal)
    congr 1
    ring

/-- Exact epsilon shift, including infinite robustness and absent witnesses. -/
theorem robustness_thresholdShift (φ : Formula Var)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) φ → a.relation = .ge)
    (ε : ℝ) (t : σ.Time) :
    σ.Robustness (φ.thresholdShift ε) t = σ.Robustness φ t - (ε : EReal) := by
  induction φ generalizing ε t with
  | truth => simp [Formula.thresholdShift, Robustness]
  | atom a =>
    have ge := nonStrict a (.refl _)
    simp [Formula.thresholdShift, Robustness, AtomicProposition.robustness, ge, EReal.coe_sub]
  | neg φ ih =>
    rw [Formula.thresholdShift, Robustness,
      ih (fun a ha => nonStrict a (.neg ha)) (-ε) t]
    exact neg_sub_neg_real _ ε
  | and φ ψ ihφ ihψ =>
    rw [Formula.thresholdShift, Robustness,
      ihφ (fun a ha => nonStrict a (.and_left ha)) ε t,
      ihψ (fun a ha => nonStrict a (.and_right ha)) ε t]
    exact real_sub_min _ _ ε
  | «until» I φ ψ ihφ ihψ =>
    simp only [Formula.thresholdShift, Robustness,
      ihφ (fun a ha => nonStrict a (.until_left ha)),
      ihψ (fun a ha => nonStrict a (.until_right ha))]
    simp_rw [real_sub_iInf, real_sub_min, real_sub_iSup]

/-- Boolean satisfaction of the strengthened formula gives the closed
robustness lower bound used in the robust reduction. -/
theorem robustness_ge_of_satisfies_strengthening (φ : Formula Var)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) φ → a.relation = .ge)
    (ε : ℝ) (t : σ.Time) (truth : σ.Satisfies (φ.thresholdShift ε) t) :
    (ε : EReal) ≤ σ.Robustness φ t := by
  have lower := σ.robustness_nonneg_of_satisfies _ t truth
  rw [σ.robustness_thresholdShift φ nonStrict ε t] at lower
  have law := EReal.le_sub_iff_add_le (a := 0) (b := (ε : EReal))
    (c := σ.Robustness φ t) (Or.inl (EReal.coe_ne_bot ε)) (Or.inl (EReal.coe_ne_top ε))
  simpa only [zero_add] using law.mp lower

/-- Strictly exceeding epsilon entails Boolean satisfaction after strengthening. -/
theorem satisfies_strengthening_of_robustness_gt (φ : Formula Var)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) φ → a.relation = .ge)
    (ε : ℝ) (t : σ.Time) (positive : (ε : EReal) < σ.Robustness φ t) :
    σ.Satisfies (φ.thresholdShift ε) t := by
  apply σ.satisfies_of_robustness_pos
  rw [σ.robustness_thresholdShift φ nonStrict ε t]
  have law := EReal.lt_sub_iff_add_lt (c := 0) (b := (ε : EReal))
    (a := σ.Robustness φ t) (Or.inl (EReal.coe_ne_bot ε)) (Or.inl (EReal.coe_ne_top ε))
  exact law.mpr (by simpa only [zero_add] using positive)

/-- The other half of the robust model-checking reduction: a Boolean
counterexample to strengthening cannot have robustness above epsilon. -/
theorem robustness_le_of_not_satisfies_strengthening (φ : Formula Var)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) φ → a.relation = .ge)
    (ε : ℝ) (t : σ.Time) (violation : ¬ σ.Satisfies (φ.thresholdShift ε) t) :
    σ.Robustness φ t ≤ (ε : EReal) := by
  exact le_of_not_gt (fun positive =>
    violation (σ.satisfies_strengthening_of_robustness_gt φ nonStrict ε t positive))

run_elab do
  for name in #[``Formula.thresholdShift, ``robustness_thresholdShift,
      ``Formula.NormalizedReady.thresholdShift, ``robustness_ge_of_satisfies_strengthening,
      ``satisfies_strengthening_of_robustness_gt,
      ``robustness_le_of_not_satisfies_strengthening] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"
end STLTableau.FiniteSignal
