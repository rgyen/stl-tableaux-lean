import STLTableaux.Finiteness.ClockAllocation.SelectedEventClassification
open STLTableau.Section4.Finiteness
#check UsedNameEvent.not_bounded
#check UsedNameEvent.plain_opening
#check UsedNameEvent.same_entry_name
#check UsedNameEvent.opening_or_upper
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``UsedNameEvent.not_bounded, ``UsedNameEvent.plain_opening, ``UsedNameEvent.same_entry_name, ``UsedNameEvent.opening_or_upper] do
    let axs ← Lean.collectAxioms name
    Lean.logInfo m!"{name}: {axs}"
    for axiomName in axs do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom: {axiomName}"
