import STLTableaux.Tableau.Traces.TracePrefixTransport

open STLTableau.Section4

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``local_holds_of_same_interval,
      ``Trace.holdsWith_prefix_congr, ``Trace.holds_prefix_congr] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
