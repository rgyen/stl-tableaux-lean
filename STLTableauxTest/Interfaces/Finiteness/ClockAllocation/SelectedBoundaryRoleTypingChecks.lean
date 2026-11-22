import STLTableaux.Finiteness.ClockAllocation.SelectedBoundaryRoleTyping
open STLTableau.Section4.Finiteness
#check InputOrigins.strict_clock_role
#check InputOrigins.strict_guard_typed
#check SlotFrame.GuardTyped.mono
#check InputOrigins.strict_guard_typed_extended
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``InputOrigins.strict_clock_role, ``InputOrigins.strict_guard_typed, ``SlotFrame.GuardTyped.mono, ``InputOrigins.strict_guard_typed_extended] do
    let axs ← Lean.collectAxioms name
    Lean.logInfo m!"{name}: {axs}"
    for axiomName in axs do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom: {axiomName}"
