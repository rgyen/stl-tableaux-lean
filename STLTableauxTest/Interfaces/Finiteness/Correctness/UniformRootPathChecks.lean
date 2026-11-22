import STLTableaux.Finiteness.Correctness.UniformRootPath
open STLTableau.Section4.Finiteness
#print axioms uniform_root_accepting_path
#print axioms uniform_root_path_of_formula
#print axioms uniform_root_path_of_satisfied_run
#print axioms uniform_root_path_of_original_run
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``uniform_root_accepting_path, ``uniform_root_path_of_formula, ``uniform_root_path_of_satisfied_run, ``uniform_root_path_of_original_run] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "unapproved axiom: {ax}"
