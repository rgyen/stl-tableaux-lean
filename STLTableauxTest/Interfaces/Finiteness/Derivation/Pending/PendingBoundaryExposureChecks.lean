import STLTableaux.Finiteness.Derivation.Pending.PendingBoundaryExposure
open STLTableau.Section4.Finiteness
#print axioms owned_optional_boundary_exposure
#print axioms owned_required_boundary_exposure
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``owned_optional_boundary_exposure, ``owned_required_boundary_exposure] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
