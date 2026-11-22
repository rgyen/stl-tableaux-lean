import STLTableaux.Automata.Recognition.TraceClockSchedule
import STLTableaux.Finiteness.Inventory.Subgraph

/-! Properties of actual tableau labels transfer to indexed trace frames.
No alternate labeling or path is introduced. -/
namespace STLTableau.Section4.Path
variable {Clock Var State : Type*}

theorem frameAt_locals_of_allStates (T : Tableau Clock Var State)
    (hf : ∀ s, (T.label s).Finite) (p : Path Clock State) (A : Set State)
    (hp : Finiteness.Subgraph.AllStates A p)
    (Q : Section3.Local Clock Var → Prop)
    (hQ : ∀ s ∈ A, ∀ l ∈ T.label s, Q l)
    (i : Fin (p.trace T.label hf).length) (l : Section3.Local Clock Var)
    (hl : l ∈ ((p.trace T.label hf).frameAt i).locals) : Q l := by
  induction p with
  | last incoming s =>
      exact hQ s hp l hl
  | step incoming s tail ih =>
      cases i using Fin.cases with
      | zero => exact hQ s hp.1 l hl
      | succ j => exact ih hp.2 j hl

theorem frameAt_locals_property (T : Tableau Clock Var State)
    (hf : ∀ s, (T.label s).Finite) (p : Path Clock State) (hp : p.valid T)
    (Q : Section3.Local Clock Var → Prop)
    (hQ : ∀ s ∈ T.states, ∀ l ∈ T.label s, Q l)
    (i : Fin (p.trace T.label hf).length)
    (l : Section3.Local Clock Var)
    (hl : l ∈ ((p.trace T.label hf).frameAt i).locals) : Q l := by
  induction p with
  | last incoming s =>
      have hi : i.val = 0 := by have := i.isLt; change i.val < 1 at this; omega
      have he : i = ⟨0, by simp [trace, Trace.length]⟩ := Fin.ext hi
      subst i
      exact hQ s hp l hl
  | step incoming s tail ih =>
      cases i using Fin.cases with
      | zero => exact hQ s hp.1 l hl
      | succ j => exact ih hp.2.1 j hl

theorem frameAt_locals_keepAtomic (T : Tableau Clock Var State)
    (hf : ∀ s, (T.label s).Finite) (p : Path Clock State)
    (i : Fin (p.trace T.label hf).length)
    (l : Section3.Local Clock Var)
    (hl : l ∈ ((p.trace T.label hf).frameAt i).locals) :
    Section3.TransitionForm.KeepAtomic l := by
  induction p with
  | last incoming s =>
      have hi : i.val = 0 := by have := i.isLt; change i.val < 1 at this; omega
      have he : i = ⟨0, by simp [trace, Trace.length]⟩ := Fin.ext hi
      subst i
      exact T.label_atomic s l hl
  | step incoming s tail ih =>
      cases i using Fin.cases with
      | zero => exact T.label_atomic s l hl
      | succ j => exact ih j hl

end STLTableau.Section4.Path
