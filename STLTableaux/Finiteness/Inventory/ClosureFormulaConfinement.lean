import STLTableaux.Finiteness.Inventory.BranchFormulaConfinement
import STLTableaux.Finiteness.Inventory.CurrentBoundedProvenance

/-! Literal minimality confines every actual closure predicate to the
subformula envelope of the original input. No expansion history is assumed. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*}

def LocalFormulaBelow (root : Formula Var) : Local Clock Var → Prop
  | .predicate p => p.formula ≼ root
  | _ => True

def StateFormulasBelow (root : Formula Var) (S : Section3.StateForm Clock Var) : Prop :=
  ∀ l ∈ S.locals, LocalFormulaBelow root l

def FormFormulasBelow (root : Formula Var) (F : Section3.TransitionForm Clock Var) : Prop :=
  StateFormulasBelow root F.current ∧
    ∀ N, F.nextPart = some N → StateFormulasBelow root N

theorem closure_formulas_below [DecidableEq Clock]
    (root : Formula Var) {S : Section3.StateForm Clock Var} {U : Section3.TransitionForm Clock Var}
    (hc : ConcreteContextual.catalogue.IsClosure (.ofState S) U)
    (hS : StateFormulasBelow root S) : FormFormulasBelow root U := by
  let Q : Local Clock Var → Prop := LocalFormulaBelow root
  let H := U.restrictLocals Q Q
  have hSH : Section3.SyntacticallySubsumed (Section3.TransitionForm.ofState S) H :=
    hc.extension.restrictLocalsTarget Q Q (fun _ hl => hS _ hl) (by intros N _ hN; cases hN)
  have hclosed : ConcreteContextual.catalogue.IsClosed H := by
    intro p hp
    have hpU : Local.predicate p ∈ U.current.locals := hp.1
    have hpRoot : p.formula ≼ root := hp.2
    rcases hc.closed p hpU with hn | ⟨B, hb, hBU⟩
    · exact Or.inl hn
    · refine Or.inr ⟨B, hb, ?_⟩
      apply hBU.restrictLocalsTarget Q Q
      · intro l hl
        cases l with
        | terminal | marker => trivial
        | predicate q => exact (branch_current_formula_subformula hb hl).trans hpRoot
      · intro N _ hN _ l hl
        cases l with
        | terminal | marker => trivial
        | predicate q => exact (branch_next_formula_subformula hb hN hl).trans hpRoot
  have hUH := hc.minimal H hSH hclosed (U.restrictLocals_subsumed Q Q)
  refine ⟨fun l hl => (hUH.current.locals hl).2, ?_⟩
  intro N hN l hl
  obtain ⟨M, hM, hNM, _⟩ := hUH.next N hN
  have he : M = N.restrictLocals Q := by
    simpa only [H, TransitionForm.restrictLocals, hN, Option.map_some,
      Option.some.injEq] using hM.symm
  subst M
  exact (hNM.locals hl).2

theorem plain_formulas_below (root : Formula Var) :
    StateFormulasBelow root (Section3.StateForm.ofLocal (.predicate (.plain root)) :
      Section3.StateForm Clock Var) := by
  intro l hl
  have he : l = .predicate (.plain root) := hl
  subst l
  exact Formula.IsSubformula.refl root

end STLTableau.Section4.Finiteness
