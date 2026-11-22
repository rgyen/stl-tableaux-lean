import STLTableaux.ModelChecking.Preprocessing.NormalizedInput
import STLTableaux.Semantics.Robustness.Robustness

/-! Exact quantitative negation normalization for the original ge atoms.
Complementing such an atom changes its relation to lt, not its function.
No finite-variability or independent semantic-equivalence premise is used. -/
namespace STLTableau
namespace FiniteSignal
variable {Var : Type*} (σ : FiniteSignal Var)

theorem robustness_normalizeMixedNegation (φ : Formula Var)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) φ → a.relation = .ge)
    (negative : Bool) (t : σ.Time) :
    σ.Robustness (φ.normalizeMixedNegation negative) t =
      if negative then -σ.Robustness φ t else σ.Robustness φ t := by
  induction φ generalizing negative t with
  | truth => cases negative <;>
      simp [Formula.normalizeMixedNegation, Formula.falsity, Robustness]
  | atom a =>
    have ge := nonStrict a (.refl _)
    cases negative <;>
      simp [Formula.normalizeMixedNegation, AtomicProposition.complementFormula,
        Robustness, AtomicProposition.robustness, ge, EReal.coe_neg]
  | neg φ ih =>
    cases negative <;> simp [Formula.normalizeMixedNegation, Robustness,
      ih (fun a ha => nonStrict a (.neg ha))]
  | and φ ψ ihφ ihψ =>
    cases negative <;> simp [Formula.normalizeMixedNegation, Formula.or, Robustness,
      ihφ (fun a ha => nonStrict a (.and_left ha)),
      ihψ (fun a ha => nonStrict a (.and_right ha))]
  | «until» I φ ψ ihφ ihψ =>
    have left := ihφ (fun a ha => nonStrict a (.until_left ha))
    have right := ihψ (fun a ha => nonStrict a (.until_right ha))
    cases negative
    · simp [Formula.normalizeMixedNegation, Robustness, left, right]
    · have release :
          σ.Robustness (Formula.release I (φ.normalizeMixedNegation true)
            (ψ.normalizeMixedNegation true)) t = -σ.Robustness (.until I φ ψ) t := by
        simp [Formula.release, Robustness, left, right]
      cases φ <;> exact release
end FiniteSignal

namespace Formula
variable {Var : Type*}

private def atomProperties (P : AtomicProposition Var → Prop) : Formula Var → Prop
  | .truth => True
  | .atom a => P a
  | .neg φ => atomProperties P φ
  | .and φ ψ => atomProperties P φ ∧ atomProperties P ψ
  | .until _ φ ψ => atomProperties P φ ∧ atomProperties P ψ

private theorem atomProperties_iff (P : AtomicProposition Var → Prop) (φ : Formula Var) :
    atomProperties P φ ↔ ∀ a, IsSubformula (.atom a) φ → P a := by
  induction φ with
  | truth => constructor <;> intro h
             · intro a sub; cases sub
             · trivial
  | atom b =>
    constructor
    · intro h a sub; cases sub; exact h
    · intro h; exact h b (.refl _)
  | neg φ ih =>
    constructor
    · intro h a sub; cases sub with | neg sub => exact ih.mp h a sub
    · intro h; exact ih.mpr (fun a sub => h a (.neg sub))
  | and φ ψ ihφ ihψ =>
    constructor
    · intro h a sub
      cases sub with
      | and_left sub => exact ihφ.mp h.1 a sub
      | and_right sub => exact ihψ.mp h.2 a sub
    · intro h
      exact ⟨ihφ.mpr (fun a sub => h a (.and_left sub)),
        ihψ.mpr (fun a sub => h a (.and_right sub))⟩
  | «until» I φ ψ ihφ ihψ =>
    constructor
    · intro h a sub
      cases sub with
      | until_left sub => exact ihφ.mp h.1 a sub
      | until_right sub => exact ihψ.mp h.2 a sub
    · intro h
      exact ⟨ihφ.mpr (fun a sub => h a (.until_left sub)),
        ihψ.mpr (fun a sub => h a (.until_right sub))⟩

private theorem atomProperties_normalizeMixedNegation (P : AtomicProposition Var → Prop)
    (preserve : ∀ a, P a → P { a with relation := .lt }) (φ : Formula Var)
    (nonStrict : ∀ a, IsSubformula (.atom a) φ → a.relation = .ge)
    (all : atomProperties P φ) (negative : Bool) :
    atomProperties P (φ.normalizeMixedNegation negative) := by
  induction φ generalizing negative with
  | truth => cases negative <;> trivial
  | atom a =>
    have ge := nonStrict a (.refl _)
    cases negative
    · exact all
    · simpa only [normalizeMixedNegation, Bool.true_eq, ↓reduceIte,
        AtomicProposition.complementFormula, ge, atomProperties] using preserve a all
  | neg φ ih => exact ih (fun a sub => nonStrict a (.neg sub)) all (!negative)
  | and φ ψ ihφ ihψ =>
    have left := ihφ (fun a sub => nonStrict a (.and_left sub)) all.1
    have right := ihψ (fun a sub => nonStrict a (.and_right sub)) all.2
    cases negative <;>
      exact ⟨left _, right _⟩
  | «until» I φ ψ ihφ ihψ =>
    have left := ihφ (fun a sub => nonStrict a (.until_left sub)) all.1
    have right := ihψ (fun a sub => nonStrict a (.until_right sub)) all.2
    cases negative
    · exact ⟨left _, right _⟩
    · cases φ <;> exact ⟨left true, right true⟩

/-- Every normalized atom keeps an original atomic function unchanged.
In the ge complement branch only the relation is changed to lt. -/
theorem normalizeMixedNegation_functions_continuous (φ : Formula Var)
    (nonStrict : ∀ a, IsSubformula (.atom a) φ → a.relation = .ge)
    (functions : ∀ a, IsSubformula (.atom a) φ → Continuous a.function)
    (negative : Bool) (a : AtomicProposition Var)
    (sub : IsSubformula (.atom a) (φ.normalizeMixedNegation negative)) :
    Continuous a.function := by
  have all := atomProperties_normalizeMixedNegation
    (fun a : AtomicProposition Var => Continuous a.function) (fun _ h => h) φ
    nonStrict ((atomProperties_iff _ φ).mpr functions) negative
  exact (atomProperties_iff _ _).mp all a sub
end Formula

run_elab do
  for name in #[``FiniteSignal.robustness_normalizeMixedNegation,
      ``Formula.normalizeMixedNegation_functions_continuous] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end STLTableau
