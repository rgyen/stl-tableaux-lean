import STLTableaux.Finiteness.Derivation.Pending.PendingFold

open STLTableau.Section4.Finiteness
#check foldCurrent_perm
#check foldCurrent_perm_weight
#check foldCurrent_append
#check foldCurrent_append_weight
#print axioms foldCurrent_perm
#print axioms foldCurrent_perm_weight
#print axioms foldCurrent_append
#print axioms foldCurrent_append_weight

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``foldCurrent_perm, ``foldCurrent_perm_weight,
      ``foldCurrent_append, ``foldCurrent_append_weight] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
