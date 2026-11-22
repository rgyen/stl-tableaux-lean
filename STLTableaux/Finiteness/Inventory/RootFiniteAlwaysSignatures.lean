import STLTableaux.Semantics.Stability.Stability
import Mathlib.Data.Finset.Lattice.Basic

/-! A finite inventory of subformulas `□[I] φ` with bounded `I`.
This inventory alone does not assert actual rule or closure confinement. -/
namespace STLTableau.Section4.Finiteness
open scoped STL
variable {Var : Type*}

/-- The exact encoding is neg(until bounded-I truth (neg operand)). -/
noncomputable def finiteAlwaysAtRoot : Formula Var → Finset (BoundedTimeInterval × Formula Var)
  | .neg (.until (.bounded I) .truth (.neg φ)) => {⟨I,φ⟩}
  | _ => ∅

noncomputable def rootFiniteAlwaysSignatures : Formula Var →
    Finset (BoundedTimeInterval × Formula Var)
  | .truth | .atom _ => ∅
  | .neg φ => by
      classical
      exact rootFiniteAlwaysSignatures φ ∪ finiteAlwaysAtRoot (.neg φ)
  | .and φ ψ => by
      classical
      exact rootFiniteAlwaysSignatures φ ∪ rootFiniteAlwaysSignatures ψ
  | .until _ φ ψ => by
      classical
      exact rootFiniteAlwaysSignatures φ ∪ rootFiniteAlwaysSignatures ψ

theorem finiteAlwaysAtRoot_formula_eq
    (root : Formula Var) (I : BoundedTimeInterval) (φ : Formula Var)
    (hm : (I,φ) ∈ finiteAlwaysAtRoot root) : root = Formula.always (.bounded I) φ := by
  cases root with
  | truth | atom | and | «until» => simp [finiteAlwaysAtRoot] at hm
  | neg ψ =>
    cases ψ with
    | truth | atom | neg | and => simp [finiteAlwaysAtRoot] at hm
    | «until» J χ ξ =>
      cases J <;> cases χ <;> cases ξ <;> simp_all [finiteAlwaysAtRoot,Formula.always,Formula.eventually]

theorem mem_rootFiniteAlwaysSignatures_formula_subformula
    (root : Formula Var) (I : BoundedTimeInterval) (φ : Formula Var)
    (hm : (I,φ) ∈ rootFiniteAlwaysSignatures root) :
    Formula.always (.bounded I) φ ≼ root := by
  classical
  induction root with
  | truth | atom => simp [rootFiniteAlwaysSignatures] at hm
  | neg ψ ih =>
    rcases Finset.mem_union.mp hm with h | h
    · exact .neg (ih h)
    · rw [finiteAlwaysAtRoot_formula_eq _ I φ h]
      exact .refl _
  | and ψ χ ihψ ihχ =>
    rcases Finset.mem_union.mp hm with h | h
    · exact .and_left (ihψ h)
    · exact .and_right (ihχ h)
  | «until» J ψ χ ihψ ihχ =>
    rcases Finset.mem_union.mp hm with h | h
    · exact .until_left (ihψ h)
    · exact .until_right (ihχ h)

theorem rootFiniteAlwaysSignatures_mono {ψ root : Formula Var}
    (h : ψ ≼ root) : rootFiniteAlwaysSignatures ψ ⊆ rootFiniteAlwaysSignatures root := by
  classical
  induction h with
  | refl => exact Finset.Subset.refl _
  | neg _ ih => exact ih.trans Finset.subset_union_left
  | and_left _ ih => exact ih.trans Finset.subset_union_left
  | and_right _ ih => exact ih.trans Finset.subset_union_right
  | until_left _ ih => exact ih.trans Finset.subset_union_left
  | until_right _ ih => exact ih.trans Finset.subset_union_right

theorem mem_rootFiniteAlwaysSignatures_iff
    (root : Formula Var) (I : BoundedTimeInterval) (φ : Formula Var) :
    (I,φ) ∈ rootFiniteAlwaysSignatures root ↔ Formula.always (.bounded I) φ ≼ root := by
  classical
  refine ⟨mem_rootFiniteAlwaysSignatures_formula_subformula root I φ,?_⟩
  intro h
  apply rootFiniteAlwaysSignatures_mono h
  simp [Formula.always,Formula.eventually,rootFiniteAlwaysSignatures,finiteAlwaysAtRoot]

theorem mem_rootFiniteAlwaysSignatures_operand_subformula
    (root : Formula Var) (I : BoundedTimeInterval) (φ : Formula Var)
    (hm : (I,φ) ∈ rootFiniteAlwaysSignatures root) : φ ≼ root :=
  (Formula.IsSubformula.neg (.until_right (.neg (.refl φ)))).trans
    (mem_rootFiniteAlwaysSignatures_formula_subformula root I φ hm)

theorem rootFiniteAlwaysSignatures_operand_stable
    (root : Formula Var) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (hst : σ.StablePartition root P) :
    ∀ s ∈ rootFiniteAlwaysSignatures root, ∀ j, σ.Stable (P.interval j) s.2 := by
  rintro ⟨I,φ⟩ hm j
  exact hst j φ (mem_rootFiniteAlwaysSignatures_operand_subformula root I φ hm)

theorem rootFiniteAlwaysSignatures_operand_stablePartition
    (root : Formula Var) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (hst : σ.StablePartition root P) (I : BoundedTimeInterval) (φ : Formula Var)
    (hm : (I,φ) ∈ rootFiniteAlwaysSignatures root) : σ.StablePartition φ P := by
  intro j ψ hψ
  exact hst j ψ (hψ.trans (mem_rootFiniteAlwaysSignatures_operand_subformula root I φ hm))

end STLTableau.Section4.Finiteness
