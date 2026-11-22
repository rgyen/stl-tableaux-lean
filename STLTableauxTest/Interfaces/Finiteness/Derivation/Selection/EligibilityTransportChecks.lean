import STLTableaux.Finiteness.Derivation.Selection.EligibilityTransport
open STLTableau.Section4.Finiteness
#check Eligibility.ordinary
#check Eligibility.boundary
#print axioms Eligibility.ordinary
#print axioms Eligibility.boundary
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Eligibility.ordinary, ``Eligibility.boundary] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
