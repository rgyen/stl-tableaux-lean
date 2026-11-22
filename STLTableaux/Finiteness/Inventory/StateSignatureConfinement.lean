import STLTableaux.Finiteness.Inventory.ClosureFormulaConfinement
import STLTableaux.Finiteness.Inventory.RootTemporalSignatures

/-! State-level formula and temporal signature confinement, without paths. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

def StateSignaturesConfined (root : Formula Var) (S : Section3.StateForm Clock Var) : Prop :=
  (∀ c b kind I φ, Local.predicate (.upper c b kind I φ) ∈ S.locals →
    (kind, I, φ) ∈ rootTemporalSignatures root) ∧
  (∀ c d b q kind I φ, Local.predicate (.bounded c d b q kind I φ) ∈ S.locals →
    (kind, I, φ) ∈ rootTemporalSignatures root)

theorem state_signatures_confined_of_formulas_below
    (root : Formula Var) (S : Section3.StateForm Clock Var) (hS : StateFormulasBelow root S) :
    StateSignaturesConfined root S := by
  constructor
  · intro c b kind I φ hp
    exact upper_signature_mem_of_formula_subformula root c b kind I φ (hS _ hp)
  · intro c d b q kind I φ hp
    exact bounded_signature_mem_of_formula_subformula root c d b q kind I φ (hS _ hp)

end STLTableau.Section4.Finiteness
