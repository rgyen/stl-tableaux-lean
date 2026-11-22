import STLTableaux.Closure.Subsumption.FaithfulClosureOrder

open STLTableau.Section3

/-- If the current part is already rule-closed, a closure of a state form
has no next component (Definition 4.8). -/
example {Clock Var : Type*} (E : ClosureCatalogue Clock Var)
    (N : StateForm Clock Var) (F : TransitionForm Clock Var)
    (hcurrent : E.IsClosed (.ofState F.current)) (hn : F.nextPart ≠ none) :
    ¬ E.IsClosure (.ofState N) F := by
  intro hc
  exact hn (hc.nextPart_eq_none_of_current_closed hcurrent)

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for ax in ← Lean.collectAxioms
      ``ClosureCatalogue.IsClosure.nextPart_eq_none_of_current_closed do
    unless allowed.contains ax do
      throwError "Minimal-closure check uses unapproved axiom {ax}"
