import STLTableaux.Finiteness.Derivation.Selection.SelectedClockSupport
open STLTableau.Section4.Finiteness
#check SelectedTree.syntax_clock_support
#check SafeNormalization.allClocks_eq_syntax
#check SelectedTree.normalized_clock_card
#check SelectedTree.normalized_clock_card_of_input
#print axioms SelectedTree.syntax_clock_support
#print axioms SafeNormalization.allClocks_eq_syntax
#print axioms SelectedTree.normalized_clock_card_of_input
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``OwnedPending.canonical_clock_support, ``SelectedTree.freshClocks_length,
    ``SelectedTree.syntax_clock_support, ``SafeNormalization.allClocks_eq_syntax,
    ``OwnedPending.local_clock_support, ``OwnedPending.outside_clock_support,
    ``BoundaryChoice.input_clock_support, ``OrdinaryChoice.input_clock_support_branch,
    ``SelectedTree.normalized_clock_card, ``SelectedTree.normalized_clock_card_of_input] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
