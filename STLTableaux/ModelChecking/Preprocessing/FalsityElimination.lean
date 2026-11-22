import STLTableaux.Syntax.InputSyntax
import STLTableaux.Semantics.Robustness.Robustness
import STLTableaux.Semantics.Robustness.RobustnessClip
import STLTableaux.Semantics.Stability.Stability

/-! A syntax-directed positive-grammar translation of falsity leaves.
Derived operators are handled as operators, not by rewriting their internal
negations. Classical choice selects a witness constructed by this grammar;
it neither assumes semantics nor preserves the quantitative value of false. -/
namespace STLTableau.Formula
variable {Var : Type*}

/-- A closed, continuously false atom with no variable arguments. -/
def falseAtom : AtomicProposition Var := ⟨0, Fin.elim0, fun _ => -1, .ge⟩

inductive FalsityElimination : Formula Var → Formula Var → Prop
  | truth : FalsityElimination .truth .truth
  | falsity : FalsityElimination falsity (.atom falseAtom)
  | atom (a : AtomicProposition Var) : FalsityElimination (.atom a) (.atom a)
  | and {φ ψ φ' ψ'} : FalsityElimination φ φ' → FalsityElimination ψ ψ' →
      FalsityElimination (.and φ ψ) (.and φ' ψ')
  | or {φ ψ φ' ψ'} : FalsityElimination φ φ' → FalsityElimination ψ ψ' →
      FalsityElimination (Formula.or φ ψ) (Formula.or φ' ψ')
  | until {φ ψ φ' ψ'} : FalsityElimination φ φ' → FalsityElimination ψ ψ' →
      FalsityElimination (untimedUntil φ ψ) (untimedUntil φ' ψ')
  | release {φ ψ φ' ψ'} : FalsityElimination φ φ' → FalsityElimination ψ ψ' →
      FalsityElimination (Formula.release (.unbounded 0) φ ψ)
        (Formula.release (.unbounded 0) φ' ψ')
  | eventually (I : TimeInterval) {φ φ'} : FalsityElimination φ φ' →
      FalsityElimination (eventually I φ) (eventually I φ')
  | always (I : TimeInterval) {φ φ'} : FalsityElimination φ φ' →
      FalsityElimination (always I φ) (always I φ')

namespace FalsityElimination
variable {φ ψ : Formula Var}

theorem ready (h : FalsityElimination φ ψ) : ψ.NormalizedReady := by
  induction h with
  | truth => exact .truth
  | falsity => exact .atom falseAtom
  | atom a => exact .atom a
  | and _ _ left right => exact .and left right
  | or _ _ left right => exact .or left right
  | «until» _ _ left right => exact .until left right
  | release _ _ left right => exact .release left right
  | eventually I _ child => exact .eventually I child
  | always I _ child => exact .always I child

theorem satisfies_iff (h : FalsityElimination φ ψ)
    (σ : FiniteSignal Var) (t : σ.Time) : σ.Satisfies ψ t ↔ σ.Satisfies φ t := by
  induction h generalizing t with
  | truth => rfl
  | falsity =>
    change ((-1 : ℝ) ≥ 0) ↔ ¬ True
    norm_num
  | atom => rfl
  | and _ _ left right => simp only [FiniteSignal.Satisfies, left, right]
  | or _ _ left right => simp only [FiniteSignal.satisfies_or, left, right]
  | «until» _ _ left right =>
    simp only [untimedUntil, FiniteSignal.Satisfies, left, right]
  | release _ _ left right =>
    simp only [Formula.release, FiniteSignal.Satisfies, left, right]
  | eventually I _ child => simp only [FiniteSignal.satisfies_eventually_iff, child]
  | always I _ child => simp only [FiniteSignal.satisfies_always_iff, child]

/-- Every output atom is unchanged from the input, or is the fixed
zero-argument false atom. No new variable or atomic function is invented. -/
theorem atom_origin (h : FalsityElimination φ ψ) (a : AtomicProposition Var)
    (sub : IsSubformula (.atom a) ψ) : IsSubformula (.atom a) φ ∨ a = falseAtom := by
  induction h with
  | truth => cases sub
  | falsity => cases sub; exact Or.inr rfl
  | atom b => exact Or.inl sub
  | and h₁ h₂ left right =>
    cases sub with
    | and_left hs => exact (left hs).imp IsSubformula.and_left id
    | and_right hs => exact (right hs).imp IsSubformula.and_right id
  | or h₁ h₂ left right =>
    cases sub with
    | neg hs => cases hs with
      | and_left hs => cases hs with
        | neg hs => exact (left hs).imp (fun hs => .neg (.and_left (.neg hs))) id
      | and_right hs => cases hs with
        | neg hs => exact (right hs).imp (fun hs => .neg (.and_right (.neg hs))) id
  | «until» h₁ h₂ left right =>
    cases sub with
    | until_left hs => exact (left hs).imp IsSubformula.until_left id
    | until_right hs => exact (right hs).imp IsSubformula.until_right id
  | release h₁ h₂ left right =>
    cases sub with
    | neg hs => cases hs with
      | until_left hs => cases hs with
        | neg hs => exact (left hs).imp (fun hs => .neg (.until_left (.neg hs))) id
      | until_right hs => cases hs with
        | neg hs => exact (right hs).imp (fun hs => .neg (.until_right (.neg hs))) id
  | eventually I h child =>
    cases sub with
    | until_left hs => cases hs
    | until_right hs => exact (child hs).imp IsSubformula.until_right id
  | always I h child =>
    cases sub with
    | neg hs => cases hs with
      | until_left hs => cases hs
      | until_right hs => cases hs with
        | neg hs => exact (child hs).imp (fun hs => .neg (.until_right (.neg hs))) id

theorem atoms_ge (h : FalsityElimination φ ψ)
    (source : ∀ a, IsSubformula (.atom a) φ → a.relation = .ge)
    (a : AtomicProposition Var) (sub : IsSubformula (.atom a) ψ) : a.relation = .ge := by
  rcases h.atom_origin a sub with original | rfl
  · exact source a original
  · rfl

theorem atoms_continuous (h : FalsityElimination φ ψ)
    (source : ∀ a, IsSubformula (.atom a) φ → Continuous a.function)
    (a : AtomicProposition Var) (sub : IsSubformula (.atom a) ψ) :
    Continuous a.function := by
  rcases h.atom_origin a sub with original | rfl
  · exact source a original
  · exact continuous_const

/-- Falsity's finite surrogate may raise negative robustness, but never
above the fixed negative clamp. No quantitative equality is asserted. -/
theorem robustness_upper (h : FalsityElimination φ ψ)
    (σ : FiniteSignal Var) (t : σ.Time) :
    σ.Robustness ψ t ≤ max (σ.Robustness φ t) (-1 : EReal) := by
  induction h generalizing t with
  | truth => exact le_max_left _ _
  | falsity =>
    change ((-1 : ℝ) : EReal) ≤ max (-(⊤ : EReal)) (-1 : EReal)
    simp
  | atom => exact le_max_left _ _
  | and _ _ left right =>
    exact RobustnessClip.min_upper (left t) (right t)
  | or _ _ left right =>
    simp only [σ.robustness_or]
    exact RobustnessClip.max_upper (left t) (right t)
  | «until» _ _ left right =>
    simp only [untimedUntil, FiniteSignal.Robustness]
    apply RobustnessClip.iSup_upper
    intro u
    apply RobustnessClip.iSup_upper
    intro inside
    apply RobustnessClip.min_upper (right u)
    apply RobustnessClip.iInf_upper
    intro s
    apply RobustnessClip.iInf_upper
    intro lower
    apply RobustnessClip.iInf_upper
    intro upper
    exact left s
  | release _ _ left right =>
    simp only [σ.robustness_release]
    apply RobustnessClip.iInf_upper
    intro u
    apply RobustnessClip.iInf_upper
    intro inside
    apply RobustnessClip.max_upper (right u)
    apply RobustnessClip.iSup_upper
    intro s
    apply RobustnessClip.iSup_upper
    intro lower
    apply RobustnessClip.iSup_upper
    intro upper
    exact left s
  | eventually I _ child =>
    simp only [σ.robustness_eventually]
    exact RobustnessClip.iSup_upper fun u => RobustnessClip.iSup_upper fun _ => child u
  | always I _ child =>
    simp only [σ.robustness_always]
    exact RobustnessClip.iInf_upper fun u => RobustnessClip.iInf_upper fun _ => child u

theorem robustness_nonneg_reflect (h : FalsityElimination φ ψ)
    (σ : FiniteSignal Var) (t : σ.Time) (nonneg : 0 ≤ σ.Robustness ψ t) :
    0 ≤ σ.Robustness φ t := by
  rcases le_max_iff.mp (nonneg.trans (h.robustness_upper σ t)) with good | bad
  · exact good
  · have negative : (-1 : EReal) < 0 := by norm_cast; norm_num
    exact False.elim ((not_le_of_gt negative) bad)

/-- Falsity elimination fixes formulas in the normalized input grammar. -/
theorem eq_of_normalizedReady (h : FalsityElimination φ ψ) (source : φ.NormalizedReady) :
    ψ = φ := by
  induction h with
  | truth => rfl
  | falsity => exact (not_normalizedReady_falsity source).elim
  | atom => rfl
  | and _ _ left right =>
    obtain ⟨hp, hq⟩ := normalizedReady_and.mp source
    rw [left hp, right hq]
  | or _ _ left right =>
    obtain ⟨hp, hq⟩ := normalizedReady_or.mp source
    rw [left hp, right hq]
  | «until» _ _ left right =>
    obtain ⟨hp, hq⟩ := normalizedReady_until.mp source
    rw [left hp, right hq]
  | release _ _ left right =>
    obtain ⟨hp, hq⟩ := normalizedReady_release.mp source
    rw [left hp, right hq]
  | eventually I _ child => rw [child (normalizedReady_eventually.mp source)]
  | always I _ child => rw [child (normalizedReady_always.mp source)]

end FalsityElimination

theorem MixedReady.exists_falsityElimination {φ : Formula Var} (h : φ.MixedReady) :
    ∃ ψ, FalsityElimination φ ψ := by
  induction h with
  | truth => exact ⟨.truth, .truth⟩
  | falsity => exact ⟨.atom falseAtom, .falsity⟩
  | atom a => exact ⟨.atom a, .atom a⟩
  | and _ _ left right =>
    obtain ⟨φ', hp⟩ := left
    obtain ⟨ψ', hq⟩ := right
    exact ⟨_, .and hp hq⟩
  | or _ _ left right =>
    obtain ⟨φ', hp⟩ := left
    obtain ⟨ψ', hq⟩ := right
    exact ⟨_, .or hp hq⟩
  | «until» _ _ left right =>
    obtain ⟨φ', hp⟩ := left
    obtain ⟨ψ', hq⟩ := right
    exact ⟨_, .until hp hq⟩
  | release _ _ left right =>
    obtain ⟨φ', hp⟩ := left
    obtain ⟨ψ', hq⟩ := right
    exact ⟨_, .release hp hq⟩
  | eventually I _ child => obtain ⟨φ', hp⟩ := child; exact ⟨_, .eventually I hp⟩
  | always I _ child => obtain ⟨φ', hp⟩ := child; exact ⟨_, .always I hp⟩

/-- A checked syntactic witness; the only choice is between witnesses of
the explicit positive-grammar transformation above. -/
noncomputable def eliminateFalsity (φ : Formula Var) (h : φ.MixedReady) : NormalizedInput Var :=
  ⟨h.exists_falsityElimination.choose, h.exists_falsityElimination.choose_spec.ready⟩

theorem eliminateFalsity_spec (φ : Formula Var) (h : φ.MixedReady) :
    FalsityElimination φ (eliminateFalsity φ h).val :=
  h.exists_falsityElimination.choose_spec

theorem satisfies_eliminateFalsity (φ : Formula Var) (h : φ.MixedReady)
    (σ : FiniteSignal Var) (t : σ.Time) :
    σ.Satisfies (eliminateFalsity φ h).val t ↔ σ.Satisfies φ t :=
  (eliminateFalsity_spec φ h).satisfies_iff σ t

theorem eliminateFalsity_atoms_ge (φ : Formula Var) (h : φ.MixedReady)
    (source : ∀ a, IsSubformula (.atom a) φ → a.relation = .ge)
    (a : AtomicProposition Var) (sub : IsSubformula (.atom a) (eliminateFalsity φ h).val) :
    a.relation = .ge := (eliminateFalsity_spec φ h).atoms_ge source a sub

theorem eliminateFalsity_atoms_continuous (φ : Formula Var) (h : φ.MixedReady)
    (source : ∀ a, IsSubformula (.atom a) φ → Continuous a.function)
    (a : AtomicProposition Var) (sub : IsSubformula (.atom a) (eliminateFalsity φ h).val) :
    Continuous a.function := (eliminateFalsity_spec φ h).atoms_continuous source a sub

theorem robustness_eliminateFalsity_upper (φ : Formula Var) (h : φ.MixedReady)
    (σ : FiniteSignal Var) (t : σ.Time) :
    σ.Robustness (eliminateFalsity φ h).val t ≤ max (σ.Robustness φ t) (-1 : EReal) :=
  (eliminateFalsity_spec φ h).robustness_upper σ t

theorem robustness_eliminateFalsity_nonneg_reflect (φ : Formula Var) (h : φ.MixedReady)
    (σ : FiniteSignal Var) (t : σ.Time)
    (nonneg : 0 ≤ σ.Robustness (eliminateFalsity φ h).val t) :
    0 ≤ σ.Robustness φ t :=
  (eliminateFalsity_spec φ h).robustness_nonneg_reflect σ t nonneg

theorem eliminateFalsity_eq_of_normalizedReady (φ : Formula Var) (mixed : φ.MixedReady)
    (ready : φ.NormalizedReady) : (eliminateFalsity φ mixed).val = φ :=
  (eliminateFalsity_spec φ mixed).eq_of_normalizedReady ready

run_elab do
  for name in #[``FalsityElimination.ready, ``FalsityElimination.satisfies_iff,
      ``FalsityElimination.atom_origin, ``FalsityElimination.atoms_ge,
      ``FalsityElimination.atoms_continuous, ``MixedReady.exists_falsityElimination,
      ``FalsityElimination.robustness_upper, ``FalsityElimination.robustness_nonneg_reflect,
      ``FalsityElimination.eq_of_normalizedReady,
      ``eliminateFalsity_spec, ``satisfies_eliminateFalsity,
      ``eliminateFalsity_atoms_ge, ``eliminateFalsity_atoms_continuous,
      ``robustness_eliminateFalsity_upper, ``robustness_eliminateFalsity_nonneg_reflect,
      ``eliminateFalsity_eq_of_normalizedReady] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end STLTableau.Formula
