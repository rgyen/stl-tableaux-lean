import STLTableaux.Finiteness.Derivation.Pending.PendingChildShape

open STLTableau.Section4.Finiteness
#check assemble_child_canonical
#print axioms assemble_child_canonical

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in ← Lean.collectAxioms ``assemble_child_canonical do
    unless allowed.contains axiomName do
      throwError "assemble_child_canonical depends on an unapproved axiom: {axiomName}"
