import STLTableaux.Finiteness.Derivation.Pending.PendingFixedGuardSupport
open STLTableau.Section4.Finiteness
#print axioms canonical_reset_subset_fresh
#print axioms ordinary_child_reset_avoids_fixed_set
#print axioms RawBranch.bounded_current_iff_residual
#print axioms RawBranch.no_bounded_current_under_reset
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``canonical_reset_subset_fresh, ``ordinary_child_reset_avoids_fixed_set,
      ``RawBranch.bounded_current_iff_residual, ``RawBranch.no_bounded_current_under_reset] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
