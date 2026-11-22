import STLTableaux.Tableau.Stability.GeneratorStability
import Mathlib.Data.Finset.Lattice.Basic

/-! The finite set of signatures of syntactic eventuality and always
subformulas, for bounded and unbounded timing. -/
namespace STLTableau.Section4.Finiteness
open scoped STL
variable {Var : Type*}
namespace RootTemporalInventory
/-- The signature of a formula which is literally an eventuality. -/
noncomputable def literalEventualAtRoot : Formula Var → Finset (TimeInterval × Formula Var)
  | .until I .truth φ => {⟨I,φ⟩}
  | _ => ∅

/-- All eventuality occurrences, deduplicated by interval and operand. -/
noncomputable def rootEventualSignatures : Formula Var →
    Finset (TimeInterval × Formula Var)
  | .truth | .atom _ => ∅
  | .neg φ => rootEventualSignatures φ
  | .and φ ψ => by
      classical
      exact rootEventualSignatures φ ∪ rootEventualSignatures ψ
  | .until I φ ψ => by
      classical
      exact (rootEventualSignatures φ ∪ rootEventualSignatures ψ) ∪
        literalEventualAtRoot (.until I φ ψ)

theorem literalEventualAtRoot_formula_eq
    (root : Formula Var) (I : TimeInterval) (φ : Formula Var)
    (hm : (I,φ) ∈ literalEventualAtRoot root) : root = Formula.eventually I φ := by
  cases root with
  | truth | atom | neg | and => simp [literalEventualAtRoot] at hm
  | «until» J ψ χ =>
    cases ψ <;> simp [literalEventualAtRoot] at hm
    obtain ⟨rfl,rfl⟩ := hm
    rfl

theorem mem_rootEventualSignatures_formula_subformula
    (root : Formula Var) (I : TimeInterval) (φ : Formula Var)
    (hm : (I,φ) ∈ rootEventualSignatures root) :
    Formula.eventually I φ ≼ root := by
  classical
  induction root with
  | truth | atom => simp [rootEventualSignatures] at hm
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
    · rw [literalEventualAtRoot_formula_eq _ I φ h]
      exact .refl _

theorem rootEventualSignatures_mono {ψ root : Formula Var}
    (h : ψ ≼ root) : rootEventualSignatures ψ ⊆ rootEventualSignatures root := by
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

theorem mem_rootEventualSignatures_iff
    (root : Formula Var) (I : TimeInterval) (φ : Formula Var) :
    (I,φ) ∈ rootEventualSignatures root ↔ Formula.eventually I φ ≼ root := by
  classical
  refine ⟨mem_rootEventualSignatures_formula_subformula root I φ,?_⟩
  intro h
  apply rootEventualSignatures_mono h
  simp [Formula.eventually,rootEventualSignatures,literalEventualAtRoot]


/-- The exact encoding is neg(until I truth (neg operand)). -/
noncomputable def literalAlwaysAtRoot : Formula Var → Finset (TimeInterval × Formula Var)
  | .neg (.until I .truth (.neg φ)) => {⟨I,φ⟩}
  | _ => ∅

noncomputable def rootAlwaysSignatures : Formula Var →
    Finset (TimeInterval × Formula Var)
  | .truth | .atom _ => ∅
  | .neg φ => by
      classical
      exact rootAlwaysSignatures φ ∪ literalAlwaysAtRoot (.neg φ)
  | .and φ ψ => by
      classical
      exact rootAlwaysSignatures φ ∪ rootAlwaysSignatures ψ
  | .until _ φ ψ => by
      classical
      exact rootAlwaysSignatures φ ∪ rootAlwaysSignatures ψ

theorem literalAlwaysAtRoot_formula_eq
    (root : Formula Var) (I : TimeInterval) (φ : Formula Var)
    (hm : (I,φ) ∈ literalAlwaysAtRoot root) : root = Formula.always I φ := by
  cases root with
  | truth | atom | and | «until» => simp [literalAlwaysAtRoot] at hm
  | neg ψ =>
    cases ψ with
    | truth | atom | neg | and => simp [literalAlwaysAtRoot] at hm
    | «until» J χ ξ =>
      cases χ <;> cases ξ <;> simp_all [literalAlwaysAtRoot,Formula.always,Formula.eventually]

theorem mem_rootAlwaysSignatures_formula_subformula
    (root : Formula Var) (I : TimeInterval) (φ : Formula Var)
    (hm : (I,φ) ∈ rootAlwaysSignatures root) :
    Formula.always I φ ≼ root := by
  classical
  induction root with
  | truth | atom => simp [rootAlwaysSignatures] at hm
  | neg ψ ih =>
    rcases Finset.mem_union.mp hm with h | h
    · exact .neg (ih h)
    · rw [literalAlwaysAtRoot_formula_eq _ I φ h]
      exact .refl _
  | and ψ χ ihψ ihχ =>
    rcases Finset.mem_union.mp hm with h | h
    · exact .and_left (ihψ h)
    · exact .and_right (ihχ h)
  | «until» J ψ χ ihψ ihχ =>
    rcases Finset.mem_union.mp hm with h | h
    · exact .until_left (ihψ h)
    · exact .until_right (ihχ h)

theorem rootAlwaysSignatures_mono {ψ root : Formula Var}
    (h : ψ ≼ root) : rootAlwaysSignatures ψ ⊆ rootAlwaysSignatures root := by
  classical
  induction h with
  | refl => exact Finset.Subset.refl _
  | neg _ ih => exact ih.trans Finset.subset_union_left
  | and_left _ ih => exact ih.trans Finset.subset_union_left
  | and_right _ ih => exact ih.trans Finset.subset_union_right
  | until_left _ ih => exact ih.trans Finset.subset_union_left
  | until_right _ ih => exact ih.trans Finset.subset_union_right

theorem mem_rootAlwaysSignatures_iff
    (root : Formula Var) (I : TimeInterval) (φ : Formula Var) :
    (I,φ) ∈ rootAlwaysSignatures root ↔ Formula.always I φ ≼ root := by
  classical
  refine ⟨mem_rootAlwaysSignatures_formula_subformula root I φ,?_⟩
  intro h
  apply rootAlwaysSignatures_mono h
  simp [Formula.always,Formula.eventually,rootAlwaysSignatures,literalAlwaysAtRoot]


end RootTemporalInventory

noncomputable def rootTemporalSignatures (root : Formula Var) :
    Finset (TemporalKind × TimeInterval × Formula Var) := by
  classical
  exact (RootTemporalInventory.rootEventualSignatures root).image
      (fun s => (TemporalKind.eventually,s.1,s.2)) ∪
    (RootTemporalInventory.rootAlwaysSignatures root).image
      (fun s => (TemporalKind.always,s.1,s.2))

def temporalSignatureFormula (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    Formula Var :=
  match kind with
  | .eventually => Formula.eventually I φ
  | .always => Formula.always I φ

theorem mem_rootTemporalSignatures_iff (root : Formula Var)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    (kind,I,φ) ∈ rootTemporalSignatures root ↔ temporalSignatureFormula kind I φ ≼ root := by
  classical
  cases kind <;>
    simp [rootTemporalSignatures,temporalSignatureFormula,
      RootTemporalInventory.mem_rootEventualSignatures_iff,
      RootTemporalInventory.mem_rootAlwaysSignatures_iff]

theorem mem_rootTemporalSignatures_operand_subformula
    (root : Formula Var) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hm : (kind,I,φ) ∈ rootTemporalSignatures root) : φ ≼ root := by
  have ht := (mem_rootTemporalSignatures_iff root kind I φ).mp hm
  apply Formula.IsSubformula.trans (φ := temporalSignatureFormula kind I φ) _ ht
  cases kind with
  | eventually => exact .until_right (.refl φ)
  | always => exact .neg (.until_right (.neg (.refl φ)))

theorem rootTemporalSignatures_operand_stablePartition
    (root : Formula Var) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (hst : σ.StablePartition root P) (kind : TemporalKind) (I : TimeInterval)
    (φ : Formula Var) (hm : (kind,I,φ) ∈ rootTemporalSignatures root) :
    σ.StablePartition φ P := by
  intro j ψ hψ
  exact hst j ψ (hψ.trans (mem_rootTemporalSignatures_operand_subformula root kind I φ hm))

theorem upper_signature_mem_of_formula_subformula {Clock : Type*}
    (root : Formula Var) (c : Clock) (b : Marker) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var)
    (h : (Section3.Predicate.upper c b kind I φ).formula ≼ root) :
    (kind,I,φ) ∈ rootTemporalSignatures root := by
  apply (mem_rootTemporalSignatures_iff root kind I φ).mpr
  cases kind <;> exact h

theorem bounded_signature_mem_of_formula_subformula {Clock : Type*}
    (root : Formula Var) (c d : Clock) (b q : Marker) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var)
    (h : (Section3.Predicate.bounded c d b q kind I φ).formula ≼ root) :
    (kind,I,φ) ∈ rootTemporalSignatures root := by
  apply (mem_rootTemporalSignatures_iff root kind I φ).mpr
  cases kind <;> exact h

end STLTableau.Section4.Finiteness
