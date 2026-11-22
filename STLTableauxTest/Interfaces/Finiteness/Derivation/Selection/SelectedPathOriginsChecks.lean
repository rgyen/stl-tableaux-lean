import STLTableaux.Finiteness.Derivation.Selection.SelectedPathOrigins
open STLTableau.Section4.Finiteness
#print axioms InputOrigins.no_bounded_at_terminal
#print axioms InputOrigins.eligible_unique_formula
#print axioms InputOrigins.eligibility
#print axioms InputOrigins.selected_output
#print axioms InputOrigins.next_cause_exists
#print axioms InputOrigins.next_cause_injective
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``InputOrigins.no_bounded_at_terminal, ``InputOrigins.eligible_unique_formula,
      ``InputOrigins.eligibility, ``InputOrigins.selected_output,
      ``InputOrigins.next_cause_exists, ``InputOrigins.next_cause_injective] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
