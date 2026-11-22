import STLTableaux.Finiteness.ClockAllocation.OpeningSlotAssignment
open STLTableau.Section4.Finiteness
#check SlotFrame.exists_opening_slots
#check rootPalette_exists_opening_slots
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SlotFrame.exists_opening_slots, ``rootPalette_exists_opening_slots] do
    let axs ← Lean.collectAxioms name
    Lean.logInfo m!"{name}: {axs}"
    for axiomName in axs do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom: {axiomName}"
