import STLTableaux.Finiteness.Derivation.Pending.PendingResetAgreement
open STLTableau.Section4.Finiteness
#check remaining_active_subset_budget
#check ordinary_child_common_reset_agrees
#print axioms remaining_active_subset_budget
#print axioms ordinary_child_common_reset_agrees
#print axioms ordinary_child_inherited_reset_agrees
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``remaining_active_subset_budget, ``ordinary_child_common_reset_agrees,
      ``ordinary_child_inherited_reset_agrees] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
