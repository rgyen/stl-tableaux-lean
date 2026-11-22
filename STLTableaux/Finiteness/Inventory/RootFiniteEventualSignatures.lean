import STLTableaux.Semantics.Stability.Stability
import Mathlib.Data.Finset.Lattice.Basic

/-! A finite syntactic inventory of signatures of `◇[I] φ` with bounded `I` in a
root formula. This does not assert rule/closure signature confinement. -/
namespace STLTableau.Section4.Finiteness
open scoped STL
variable {Var : Type*}

/-- The signature of a formula which is of the form `◇[I] φ` with bounded `I`. -/
noncomputable def finiteEventualAtRoot : Formula Var → Finset (BoundedTimeInterval × Formula Var)
  | .until (.bounded I) .truth φ => {⟨I,φ⟩}
  | _ => ∅

/-- All occurrences of `◇[I] φ` with bounded `I`, deduplicated by interval and operand. -/
noncomputable def rootFiniteEventualSignatures : Formula Var →
    Finset (BoundedTimeInterval × Formula Var)
  | .truth | .atom _ => ∅
  | .neg φ => rootFiniteEventualSignatures φ
  | .and φ ψ => by
      classical
      exact rootFiniteEventualSignatures φ ∪ rootFiniteEventualSignatures ψ
  | .until I φ ψ => by
      classical
      exact (rootFiniteEventualSignatures φ ∪ rootFiniteEventualSignatures ψ) ∪
        finiteEventualAtRoot (.until I φ ψ)

theorem finiteEventualAtRoot_formula_eq
    (root : Formula Var) (I : BoundedTimeInterval) (φ : Formula Var)
    (hm : (I,φ) ∈ finiteEventualAtRoot root) : root = Formula.eventually (.bounded I) φ := by
  cases root with
  | truth | atom | neg | and => simp [finiteEventualAtRoot] at hm
  | «until» J ψ χ =>
    cases J with
    | unbounded => cases ψ <;> simp [finiteEventualAtRoot] at hm
    | bounded J =>
      cases ψ <;> simp [finiteEventualAtRoot] at hm
      obtain ⟨rfl,rfl⟩ := hm
      rfl

theorem mem_rootFiniteEventualSignatures_formula_subformula
    (root : Formula Var) (I : BoundedTimeInterval) (φ : Formula Var)
    (hm : (I,φ) ∈ rootFiniteEventualSignatures root) :
    Formula.eventually (.bounded I) φ ≼ root := by
  classical
  induction root with
  | truth | atom => simp [rootFiniteEventualSignatures] at hm
  | neg ψ ih => exact .neg (ih hm)
  | and ψ χ ihψ ihχ =>
    rcases Finset.mem_union.mp hm with h | h
    · exact .and_left (ihψ h)
    · exact .and_right (ihχ h)
  | «until» J ψ χ ihψ ihχ =>
    rcases Finset.mem_union.mp hm with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact .until_left (ihψ h)
      · exact .until_right (ihχ h)
    · rw [finiteEventualAtRoot_formula_eq _ I φ h]
      exact .refl _

theorem rootFiniteEventualSignatures_mono {ψ root : Formula Var}
    (h : ψ ≼ root) : rootFiniteEventualSignatures ψ ⊆ rootFiniteEventualSignatures root := by
  classical
  induction h with
  | refl => exact Finset.Subset.refl _
  | neg _ ih => exact ih
  | and_left _ ih => exact ih.trans Finset.subset_union_left
  | and_right _ ih => exact ih.trans Finset.subset_union_right
  | until_left _ ih =>
    exact ih.trans (Finset.subset_union_left.trans Finset.subset_union_left)
  | until_right _ ih =>
    exact ih.trans (Finset.subset_union_right.trans Finset.subset_union_left)

theorem mem_rootFiniteEventualSignatures_iff
    (root : Formula Var) (I : BoundedTimeInterval) (φ : Formula Var) :
    (I,φ) ∈ rootFiniteEventualSignatures root ↔ Formula.eventually (.bounded I) φ ≼ root := by
  classical
  refine ⟨mem_rootFiniteEventualSignatures_formula_subformula root I φ,?_⟩
  intro h
  apply rootFiniteEventualSignatures_mono h
  simp [Formula.eventually,rootFiniteEventualSignatures,finiteEventualAtRoot]

theorem mem_rootFiniteEventualSignatures_operand_subformula
    (root : Formula Var) (I : BoundedTimeInterval) (φ : Formula Var)
    (hm : (I,φ) ∈ rootFiniteEventualSignatures root) : φ ≼ root :=
  (Formula.IsSubformula.until_right (.refl φ)).trans
    (mem_rootFiniteEventualSignatures_formula_subformula root I φ hm)

/-- The root's fully stable partition supplies every inventory operand's stability. -/
theorem rootFiniteEventualSignatures_operand_stable
    (root : Formula Var) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (hst : σ.StablePartition root P) :
    ∀ s ∈ rootFiniteEventualSignatures root, ∀ j, σ.Stable (P.interval j) s.2 := by
  rintro ⟨I,φ⟩ hm j
  exact hst j φ (mem_rootFiniteEventualSignatures_operand_subformula root I φ hm)

/-- Full subformula stability is inherited as well as operand truth stability. -/
theorem rootFiniteEventualSignatures_operand_stablePartition
    (root : Formula Var) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (hst : σ.StablePartition root P) (I : BoundedTimeInterval) (φ : Formula Var)
    (hm : (I,φ) ∈ rootFiniteEventualSignatures root) : σ.StablePartition φ P := by
  intro j ψ hψ
  exact hst j ψ (hψ.trans
    (mem_rootFiniteEventualSignatures_operand_subformula root I φ hm))

end STLTableau.Section4.Finiteness
