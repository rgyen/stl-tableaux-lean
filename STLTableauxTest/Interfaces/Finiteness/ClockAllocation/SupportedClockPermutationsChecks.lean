import STLTableaux.Finiteness.ClockAllocation.SupportedClockPermutations

open STLTableau.Section4.Finiteness

#check supported_clock_permutation
#check compatible_clock_permutations
#check state_rename_congr
#check shared_state_rename
#check transition_rename_congr
#print axioms supported_clock_permutation
#print axioms compatible_clock_permutations
#print axioms state_rename_congr
#print axioms shared_state_rename
#print axioms transition_rename_congr

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``supported_clock_permutation, ``compatible_clock_permutations,
      ``state_rename_congr, ``shared_state_rename, ``transition_rename_congr] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
