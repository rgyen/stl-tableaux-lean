import STLTableaux.Finiteness.Derivation.Branches.RawBranchCanonical

open STLTableau.Section4.Finiteness
#check RawBranch.canonical
#print axioms RawBranch.canonical
#check RawBranch.canonical_with_reset_support
#print axioms RawBranch.canonical_with_reset_support

#check RawBranch.canonical_with_exact_reset_map
#print axioms RawBranch.canonical_with_exact_reset_map
#check canonical_reset_map_without_guards
#print axioms canonical_reset_map_without_guards

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``RawBranch.canonical, ``RawBranch.canonical_with_reset_support, ``RawBranch.canonical_with_exact_reset_map,
    ``canonical_reset_map_without_guards] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
