import STLTableaux.Automata.Recognition.NormalizedInputLabelSemantics

open STLTableau.Section4.Finiteness

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``normalizedReady_atomic_cases, ``normalizedReady_labels_hold_iff,
      ``markedFlow_labels_hold_iff, ``inputTableau_execution_flow_normalizedReady,
      ``inputTableau_flow_labels_iff_markers] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
