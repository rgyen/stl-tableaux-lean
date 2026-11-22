import STLTableaux.Finiteness.Derivation.Branches.RawBranchUpperEntry
open STLTableau.Section4.Finiteness
#print axioms RawBranch.normalized_upper_entry
#print axioms RawBranch.normalized_upper_entry_certificate
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``RawBranch.normalized_upper_entry, ``RawBranch.normalized_upper_entry_certificate] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
