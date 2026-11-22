import STLTableaux.Semantics.Robustness.Robustness
import STLTableaux.Syntax.InputSyntax
import STLTableaux.Semantics.Stability.Stability

/-! Replace each comparison by its closed nonnegative margin. This preserves
quantitative robustness, not Boolean equivalence: a strict boundary becomes
closed. No finite-variability preservation is asserted. -/
namespace STLTableau
namespace AtomicProposition
variable {Var : Type*}

def closeNonStrict (a : AtomicProposition Var) : AtomicProposition Var :=
  {a with relation := .ge, function := fun v =>
    match a.relation with
    | .ge | .gt => a.function v
    | .le | .lt => -a.function v
    | .eq => -|a.function v|}

@[simp] theorem closeNonStrict_relation (a : AtomicProposition Var) :
    a.closeNonStrict.relation = .ge := rfl

@[simp] theorem closeNonStrict_margin (a : AtomicProposition Var) (v : Var → ℝ) :
    a.closeNonStrict.robustness v = a.robustness v := by
  cases a.relation <;> rfl

theorem holds_closeNonStrict (a : AtomicProposition Var) (v : Var → ℝ)
    (truth : a.Holds v) : a.closeNonStrict.Holds v := by
  have margin := a.holds_implies_robustness_nonneg v truth
  cases hr : a.relation <;>
    simpa only [Holds, closeNonStrict, robustness, hr, RealRelation.Holds] using margin

theorem continuous_closeNonStrict (a : AtomicProposition Var)
    (continuous : Continuous a.function) : Continuous a.closeNonStrict.function := by
  change Continuous (fun v : Fin a.arity → ℝ =>
    match a.relation with
    | .ge | .gt => a.function v
    | .le | .lt => -a.function v
    | .eq => -|a.function v|)
  cases hr : a.relation
  · exact continuous
  · exact continuous
  · exact continuous.abs.neg
  · exact continuous.neg
  · exact continuous.neg
end AtomicProposition

namespace Formula
variable {Var : Type*}

def closeNonStrictAtoms : Formula Var → Formula Var
  | .truth => .truth
  | .atom a => .atom a.closeNonStrict
  | .neg φ => .neg φ.closeNonStrictAtoms
  | .and φ ψ => .and φ.closeNonStrictAtoms ψ.closeNonStrictAtoms
  | .until I φ ψ => .until I φ.closeNonStrictAtoms ψ.closeNonStrictAtoms

theorem NormalizedReady.closeNonStrictAtoms {φ : Formula Var} (ready : φ.NormalizedReady) :
    φ.closeNonStrictAtoms.NormalizedReady := by
  induction ready with
  | truth => exact .truth
  | atom a => exact .atom _
  | and _ _ left right => exact .and left right
  | or _ _ left right => exact .or left right
  | «until» _ _ left right => exact .until left right
  | release _ _ left right => exact .release left right
  | eventually I _ child => exact .eventually I child
  | always I _ child => exact .always I child

/-- Every transformed atom comes from a literal original atom. -/
theorem closeNonStrictAtoms_atom_origin (φ : Formula Var) (a : AtomicProposition Var)
    (sub : IsSubformula (.atom a) φ.closeNonStrictAtoms) :
    ∃ b, IsSubformula (.atom b) φ ∧ a = b.closeNonStrict := by
  induction φ generalizing a with
  | truth => cases sub
  | atom b => cases sub; exact ⟨b, .refl _, rfl⟩
  | neg φ ih =>
    cases sub with
    | neg h =>
      obtain ⟨b, hb, equal⟩ := ih a h
      exact ⟨b, .neg hb, equal⟩
  | and φ ψ ihφ ihψ =>
    cases sub with
    | and_left h =>
      obtain ⟨b, hb, equal⟩ := ihφ a h
      exact ⟨b, .and_left hb, equal⟩
    | and_right h =>
      obtain ⟨b, hb, equal⟩ := ihψ a h
      exact ⟨b, .and_right hb, equal⟩
  | «until» I φ ψ ihφ ihψ =>
    cases sub with
    | until_left h =>
      obtain ⟨b, hb, equal⟩ := ihφ a h
      exact ⟨b, .until_left hb, equal⟩
    | until_right h =>
      obtain ⟨b, hb, equal⟩ := ihψ a h
      exact ⟨b, .until_right hb, equal⟩

theorem closeNonStrictAtoms_all_ge (φ : Formula Var) (a : AtomicProposition Var)
    (sub : IsSubformula (.atom a) φ.closeNonStrictAtoms) : a.relation = .ge := by
  obtain ⟨b, _, rfl⟩ := φ.closeNonStrictAtoms_atom_origin a sub
  rfl

theorem closeNonStrictAtoms_functions_continuous (φ : Formula Var)
    (functions : ∀ b, IsSubformula (.atom b) φ → Continuous b.function)
    (a : AtomicProposition Var) (sub : IsSubformula (.atom a) φ.closeNonStrictAtoms) :
    Continuous a.function := by
  obtain ⟨b, hb, rfl⟩ := φ.closeNonStrictAtoms_atom_origin a sub
  exact b.continuous_closeNonStrict (functions b hb)
end Formula

namespace FiniteSignal
variable {Var : Type*} (σ : FiniteSignal Var)

/-- Exact quantitative equality, including empty temporal witness sets. -/
theorem robustness_closeNonStrictAtoms (φ : Formula Var) (t : σ.Time) :
    σ.Robustness φ.closeNonStrictAtoms t = σ.Robustness φ t := by
  induction φ generalizing t with
  | truth => rfl
  | atom a => simp only [Formula.closeNonStrictAtoms, Robustness,
      AtomicProposition.closeNonStrict_margin]
  | neg φ ih => simp only [Formula.closeNonStrictAtoms, Robustness, ih]
  | and φ ψ ihφ ihψ => simp only [Formula.closeNonStrictAtoms, Robustness, ihφ, ihψ]
  | «until» I φ ψ ihφ ihψ =>
    simp only [Formula.closeNonStrictAtoms, Robustness, ihφ, ihψ]
end FiniteSignal

run_elab do
  for name in #[``AtomicProposition.holds_closeNonStrict,
      ``AtomicProposition.continuous_closeNonStrict,
      ``Formula.NormalizedReady.closeNonStrictAtoms,
      ``Formula.closeNonStrictAtoms_atom_origin,
      ``Formula.closeNonStrictAtoms_all_ge,
      ``Formula.closeNonStrictAtoms_functions_continuous,
      ``FiniteSignal.robustness_closeNonStrictAtoms] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"
end STLTableau
