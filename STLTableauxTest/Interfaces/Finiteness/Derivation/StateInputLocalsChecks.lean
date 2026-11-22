import STLTableaux.Finiteness.Derivation.StateInputLocals
open STLTableau.Section4.Finiteness
#check OwnedPending.locals_eq_of_safe
#check OwnedPending.local_mem_of_safe
#print axioms OwnedPending.local_mem_of_safe
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``ACIdem.currentLocalSet_eq, ``canonical_currentLocalSet,
    ``OwnedPending.locals_eq_of_safe, ``OwnedPending.local_mem_of_safe] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
