import STLTableaux.Finiteness.ClockAllocation.TypedSelectedPath
open STLTableau.Section4.Finiteness
#print axioms typed_path_of_local_extensions
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for ax in ← Lean.collectAxioms ``typed_path_of_local_extensions do
    unless allowed.contains ax do
      throwError "unapproved axiom: {ax}"
