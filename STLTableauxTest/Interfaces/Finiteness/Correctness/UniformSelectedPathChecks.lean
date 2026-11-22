import STLTableaux.Finiteness.Correctness.UniformSelectedPath
open STLTableau.Section4.Finiteness
#print axioms uniform_path_of_local_counts
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in ← Lean.collectAxioms ``uniform_path_of_local_counts do
    unless allowed.contains axiomName do
      throwError "unapproved axiom: {axiomName}"
