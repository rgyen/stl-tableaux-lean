import STLTableaux.Finiteness.Correctness.SelectedOriginPath
open STLTableau.Section4.Finiteness
#print axioms origin_certified_accepting_path
#print axioms origin_certified_path_of_formula
#print axioms origin_certified_path_of_satisfied_run
#print axioms origin_certified_path_of_original_run
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``origin_certified_accepting_path, ``origin_certified_path_of_formula,
      ``origin_certified_path_of_satisfied_run, ``origin_certified_path_of_original_run] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
