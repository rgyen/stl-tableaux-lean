import STLTableaux.Finiteness.Bounds.SelectedSuccessorSlotCount
open STLTableau.Section4.Finiteness
#print axioms SelectedTree.upperFamilyEvents_card_le_one
#print axioms SelectedTree.boundedFamilyEvents_card_le
#print axioms SelectedTree.successor_occupiedFamily_card_le
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SelectedTree.upperFamilyEvents_card_le_one, ``SelectedTree.boundedFamilyEvents_card_le, ``SelectedTree.successor_occupiedFamily_card_le] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "unapproved axiom: {ax}"
