import STLTableaux.Finiteness.Correctness.FiniteRootTableau

/-! Checks state and clock bounds and recognition soundness for the finite
restriction of the auxiliary derivation tableau. -/
open STLTableau.Section4.Finiteness
#print axioms finiteRootTableau_states_finite
#print axioms finiteRootTableau_state_card_le
#print axioms finiteRootTableau_clocks_finite
#print axioms finiteRootTableau_clock_card_le
#print axioms finiteRootTableau_state_clock_support
#print axioms finiteRootTableau_state_clock_card_le
#print axioms finiteRootTableau_sound
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``finiteRootTableau_states_finite, ``finiteRootTableau_state_card_le, ``finiteRootTableau_clocks_finite, ``finiteRootTableau_clock_card_le, ``finiteRootTableau_state_clock_support, ``finiteRootTableau_state_clock_card_le, ``finiteRootTableau_sound] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "unapproved axiom: {ax}"
