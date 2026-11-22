import STLTableaux.Finiteness.ClockAllocation.SelectedNameEvents
open STLTableau.Section4.Finiteness
#check SelectedTree.usedNameEvents_names
#print axioms SelectedTree.usedNameEvents_names
#check SelectedTree.usedNameEvents_name_injective
#print axioms SelectedTree.usedNameEvents_name_injective
#check SelectedTree.usedNameEvents_ledger
#print axioms SelectedTree.usedNameEvents_ledger
#check SelectedTree.opening_name_producer
#print axioms SelectedTree.opening_name_producer
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SelectedTree.usedNameEvents_names, ``SelectedTree.usedNameEvents_name_injective, ``SelectedTree.usedNameEvents_ledger, ``SelectedTree.opening_name_producer] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
