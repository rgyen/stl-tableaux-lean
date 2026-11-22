import STLTableaux.Finiteness.Derivation.Pending.PendingOrdinarySolo

open STLTableau.Section4.Finiteness
#check exists_ordinary_child_solo
#print axioms exists_ordinary_child_solo

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in ← Lean.collectAxioms ``exists_ordinary_child_solo do
    unless allowed.contains axiomName do
      throwError "exists_ordinary_child_solo depends on an unapproved axiom: {axiomName}"
