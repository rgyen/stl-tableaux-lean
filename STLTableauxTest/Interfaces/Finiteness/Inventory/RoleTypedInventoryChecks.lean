import STLTableaux.Finiteness.Inventory.RoleTypedInventory
open STLTableau.Section4.Finiteness
#print axioms SlotFrame.stateTyped
#print axioms SlotFrame.predicate_rename_mem
#print axioms SlotFrame.StateTyped.rename_within
#print axioms SlotFrame.TransitionTyped.rename_within
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SlotFrame.stateTyped, ``SlotFrame.predicate_rename_mem, ``SlotFrame.StateTyped.rename_within, ``SlotFrame.TransitionTyped.rename_within] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "unapproved axiom: {ax}"
