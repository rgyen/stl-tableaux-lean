import STLTableaux.Finiteness.Correctness.OriginalPathInclusion

open STLTableau.Section4.Finiteness
#check original_valid_forward
#check original_run_forward
#check original_accepting_run_forward
#check original_recognizes_forward
#print axioms original_valid_forward
#print axioms original_run_forward
#print axioms original_accepting_run_forward
#print axioms original_recognizes_forward

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``original_valid_forward, ``original_run_forward,
      ``original_accepting_run_forward, ``original_recognizes_forward] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
