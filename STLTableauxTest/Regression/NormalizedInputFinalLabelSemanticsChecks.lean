import STLTableaux.Automata.Recognition.NormalizedInputFinalLabelSemantics

open STLTableau.Section4.Finiteness

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``inputTableau_final_singleton_labels_iff,
      ``inputTableau_final_singleton_frame,
      ``inputTableau_exists_final_singleton_partition,
      ``inputTableau_exists_flow_and_final_partition] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
