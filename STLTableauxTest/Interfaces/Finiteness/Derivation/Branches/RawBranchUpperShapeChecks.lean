import STLTableaux.Finiteness.Derivation.Branches.RawBranchUpperShape
open STLTableau.Section4.Finiteness
#print axioms RawBranch.current_upper_opening
#print axioms RawBranch.current_upper_unique
#print axioms RawBranch.normalized_next_no_upper
#print axioms RawBranch.literal_next_no_upper
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``RawBranch.current_upper_opening, ``RawBranch.current_upper_unique,
      ``RawBranch.normalized_next_no_upper, ``RawBranch.literal_next_no_upper] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
