import STLTableaux.Finiteness.Derivation.Pending.PendingSelectedExposure

open STLTableau.Section4.Finiteness
#check owned_selected_exposure
#check residual_guard_empty
#print axioms owned_selected_exposure
#print axioms residual_guard_empty

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``owned_selected_exposure, ``residual_guard_empty] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
