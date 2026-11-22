import STLTableaux.Finiteness.ClockAllocation.RoleAllocationPermutation
open STLTableau.Section4.Finiteness
#print axioms RoleAllocation.exists_permutation
#print axioms RoleAllocation.exists_permutation_agree
#print axioms SlotFrame.exists_vacant_family_slot
#print axioms SlotFrame.exists_vacant_family_slot_of_bound
#print axioms SlotFrame.exists_vacant_family_slot_fourfold
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``RoleAllocation.exists_permutation, ``RoleAllocation.exists_permutation_agree, ``SlotFrame.exists_vacant_family_slot, ``SlotFrame.exists_vacant_family_slot_of_bound, ``SlotFrame.exists_vacant_family_slot_fourfold] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "unapproved axiom: {ax}"
