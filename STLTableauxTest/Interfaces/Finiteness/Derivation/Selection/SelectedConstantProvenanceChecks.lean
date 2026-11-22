import STLTableaux.Finiteness.Derivation.Selection.SelectedConstantProvenance
open STLTableau.Section4.Finiteness
#check RawBranch.raw_constants
#print axioms RawBranch.raw_constants
#check RawBranch.normalized_constants
#print axioms RawBranch.normalized_constants
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``RawBranch.raw_constants, ``RawBranch.normalized_constants] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
