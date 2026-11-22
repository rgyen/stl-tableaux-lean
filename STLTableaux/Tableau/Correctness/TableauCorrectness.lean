import STLTableaux.Tableau.Correctness.TableauSoundness

/-! Soundness and completeness of the tableau of Definition 4.28. -/
namespace STLTableau.Section4.Generated
open Section3
variable {Clock Var : Type*}

/-- Theorems 4.32 and 4.34 (tableau soundness and completeness). On a fully
stable partition, recognition is equivalent to satisfaction at time zero
for a formula in the normalized input grammar. -/
theorem recognizes_iff_formula [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (Xc : Set Clock) (φ : Formula Var) (hφ : φ.MixedReady)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (hst : σ.StablePartition φ P) :
    (closureTableau ConcreteContextual.catalogue X Xc
      (Section3.StateForm.ofLocal (.predicate (.plain φ)))).recognizes labels_finite σ P ↔
      σ.Satisfies φ ⟨0,le_rfl,σ.horizon_pos⟩ :=
  ⟨formula_of_recognizes X Xc φ hφ σ P,
    recognizes_of_formula X Xc φ σ P hst⟩

end STLTableau.Section4.Generated
