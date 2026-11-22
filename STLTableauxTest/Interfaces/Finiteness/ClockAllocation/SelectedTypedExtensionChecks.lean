import STLTableaux.Finiteness.ClockAllocation.SelectedTypedExtension
open STLTableau.Section4.Finiteness
#check SelectedTree.exists_typed_slot_extension
#check SelectedTree.exists_root_typed_extension
#print axioms SelectedTree.exists_typed_slot_extension
#print axioms SelectedTree.exists_root_typed_extension
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SelectedTree.exists_typed_slot_extension, ``SelectedTree.exists_root_typed_extension] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
