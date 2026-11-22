import STLTableaux.Finiteness.Bounds.TruthOriginBoundary
open STLTableau.Section4.Finiteness.TruthPartitionIntervals
#print axioms blockOf_last_of_false_successor
#print axioms reset_endpoint_of_false_successor
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``blockOf_last_of_false_successor, ``reset_endpoint_of_false_successor] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
