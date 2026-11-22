import STLTableaux.Finiteness.Derivation.Branches.BranchTripleAnnotations
open STLTableau.Section4.Finiteness
#check RawGuardAt.clock_support
#print axioms RawGuardAt.clock_support
#check RawResetAt.clock_support
#print axioms RawResetAt.clock_support
#check RawBranch.guard_triple_indices
#print axioms RawBranch.guard_triple_indices
#check RawBranch.reset_triple_indices
#print axioms RawBranch.reset_triple_indices
#check OrdinaryChoice.guard_triple_indices
#print axioms OrdinaryChoice.guard_triple_indices
#check OrdinaryChoice.reset_triple_indices
#print axioms OrdinaryChoice.reset_triple_indices
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``RawGuardAt.clock_support, ``RawResetAt.clock_support, ``RawBranch.guard_triple_indices, ``RawBranch.reset_triple_indices, ``OrdinaryChoice.guard_triple_indices, ``OrdinaryChoice.reset_triple_indices] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
