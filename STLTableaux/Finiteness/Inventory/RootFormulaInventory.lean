import STLTableaux.Tableau.Stability.GeneratorStability
import Mathlib.Data.Finset.Lattice.Basic

/-! The finite set of syntactic subformulas of the root formula. -/
namespace STLTableau.Section4.Finiteness
open scoped STL
variable {Var : Type*}

/-- All literal syntactic subformulas, including Boolean and untimed nodes. -/
noncomputable def rootPlainFormulas : Formula Var → Finset (Formula Var)
  | .truth => {.truth}
  | .atom p => {.atom p}
  | .neg φ => by
      classical
      exact insert (.neg φ) (rootPlainFormulas φ)
  | .and φ ψ => by
      classical
      exact insert (.and φ ψ) (rootPlainFormulas φ ∪ rootPlainFormulas ψ)
  | .until I φ ψ => by
      classical
      exact insert (.until I φ ψ) (rootPlainFormulas φ ∪ rootPlainFormulas ψ)

theorem root_mem_rootPlainFormulas (root : Formula Var) : root ∈ rootPlainFormulas root := by
  classical
  cases root <;> simp [rootPlainFormulas]

theorem subformula_mem_rootPlainFormulas {φ root : Formula Var} (h : φ ≼ root) :
    φ ∈ rootPlainFormulas root := by
  classical
  induction h with
  | refl => exact root_mem_rootPlainFormulas _
  | neg h ih => exact Finset.mem_insert_of_mem ih
  | and_left h ih => exact Finset.mem_insert_of_mem (Finset.mem_union_left _ ih)
  | and_right h ih => exact Finset.mem_insert_of_mem (Finset.mem_union_right _ ih)
  | until_left h ih => exact Finset.mem_insert_of_mem (Finset.mem_union_left _ ih)
  | until_right h ih => exact Finset.mem_insert_of_mem (Finset.mem_union_right _ ih)

/-- A formula in the literal inventory is a syntactic subformula. -/
theorem subformula_of_mem_rootPlainFormulas {φ root : Formula Var}
    (hm : φ ∈ rootPlainFormulas root) : Formula.IsSubformula φ root := by
  classical
  induction root with
  | truth | atom =>
    simp only [rootPlainFormulas, Finset.mem_singleton] at hm
    exact hm ▸ .refl _
  | neg φ ih =>
    simp only [rootPlainFormulas, Finset.mem_insert] at hm
    rcases hm with rfl | hm
    · exact .refl _
    · exact .neg (ih hm)
  | and φ ψ ih ik =>
    simp only [rootPlainFormulas, Finset.mem_insert, Finset.mem_union] at hm
    rcases hm with rfl | hm | hm
    · exact .refl _
    · exact .and_left (ih hm)
    · exact .and_right (ik hm)
  | «until» I φ ψ ih ik =>
    simp only [rootPlainFormulas, Finset.mem_insert, Finset.mem_union] at hm
    rcases hm with rfl | hm | hm
    · exact .refl _
    · exact .until_left (ih hm)
    · exact .until_right (ik hm)

end STLTableau.Section4.Finiteness

namespace STLTableau.Section4.Finiteness
variable {Var : Type*}

/-- Exactly the variables occurring as arguments of literal root atoms. -/
noncomputable def rootVariables (root : Formula Var) : Finset Var := by
  classical
  exact (Finiteness.rootPlainFormulas root).biUnion fun φ => match φ with
    | .atom a => Finset.univ.image a.arguments
    | _ => ∅

theorem atom_arguments_mem_rootVariables (root : Formula Var) (a : AtomicProposition Var)
    (ha : Formula.atom a ∈ Finiteness.rootPlainFormulas root) (i : Fin a.arity) :
    a.arguments i ∈ rootVariables root := by
  classical
  exact Finset.mem_biUnion.mpr ⟨.atom a, ha, Finset.mem_image.mpr ⟨i, by simp, rfl⟩⟩

end STLTableau.Section4.Finiteness
