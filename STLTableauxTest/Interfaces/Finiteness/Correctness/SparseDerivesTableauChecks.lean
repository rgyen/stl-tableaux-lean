import STLTableaux.Finiteness.Correctness.SparseDerivesTableau
open STLTableau.Section4.Finiteness
#check sparseDerivesTableau_states_finite
#check sparseDerivesTableau_state_card_le
#check sparseDerivesTableau_sound
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``sparseDerivesTableau_states_finite, ``sparseDerivesTableau_state_card_le, ``sparseDerivesTableau_sound] do
    let axs ← Lean.collectAxioms name
    Lean.logInfo m!"{name}: {axs}"
    for axiomName in axs do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom: {axiomName}"
