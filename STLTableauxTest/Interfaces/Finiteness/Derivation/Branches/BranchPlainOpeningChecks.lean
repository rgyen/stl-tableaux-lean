import STLTableaux.Finiteness.Derivation.Branches.BranchPlainOpening
open STLTableau.Section4.Finiteness
#check RawBranch.plain_opening_or_empty
#print axioms RawBranch.plain_opening_or_empty
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``RawBranch.plain_opening_or_empty] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
