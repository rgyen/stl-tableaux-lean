import STLTableaux.Finiteness.ClockAllocation.InitialSlotFrame
open STLTableau.Section4.Finiteness
#print axioms plain_initial_slot_frame
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``plain_initial_slot_frame] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "unapproved axiom: {ax}"
