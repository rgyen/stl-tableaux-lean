import STLTableaux.Finiteness.ClockAllocation.SelectedAlphaStep
open STLTableau.Section4.Finiteness
#print axioms SelectedTree.allocationSupport_card
#print axioms SelectedTree.output_support_allocation
#print axioms transition_holds_rename
#print axioms resolved_rename_holds
#print axioms renamed_successor_agreement
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SelectedTree.allocationSupport_card, ``SelectedTree.output_support_allocation, ``transition_holds_rename, ``resolved_rename_holds, ``renamed_successor_agreement] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "unapproved axiom: {ax}"
