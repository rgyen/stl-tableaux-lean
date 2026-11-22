import STLTableaux.Semantics.Partitions.PartitionDurationAlignment

open STLTableau.IntervalPartition

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``right_le_domain_right, ``last_right_eq_domain_right, ``residenceBoundary_eq_left,
      ``residenceBoundary_eq_horizon, ``interval_subset_residenceBounds] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
