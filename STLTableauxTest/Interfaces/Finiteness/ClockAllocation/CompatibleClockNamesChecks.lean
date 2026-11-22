import STLTableaux.Finiteness.ClockAllocation.CompatibleClockNames

open STLTableau.Section4.Finiteness

#check extend_clock_names
#check compatible_clock_names
#check finite_compatible_clock_names
#print axioms extend_clock_names
#print axioms compatible_clock_names
#print axioms finite_compatible_clock_names

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``extend_clock_names, ``compatible_clock_names,
      ``finite_compatible_clock_names] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
