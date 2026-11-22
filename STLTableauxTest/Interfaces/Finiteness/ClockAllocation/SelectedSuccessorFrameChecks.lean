import STLTableaux.Finiteness.ClockAllocation.SelectedSuccessorFrame
open STLTableau.Section4.Finiteness
#print axioms SlotFrame.StateTyped.congr_on_support
#print axioms SelectedTree.successorRoleAllocation
#print axioms selectedNextRole_on_support
#print axioms SelectedTree.successorSlotFrame
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SlotFrame.StateTyped.congr_on_support, ``SelectedTree.successorRoleAllocation, ``selectedNextRole_on_support, ``SelectedTree.successorSlotFrame] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "unapproved axiom: {ax}"
