import STLTableaux.Finiteness.ClockAllocation.AllocatedRootPath
open STLTableau.Section4.Finiteness
#print axioms allocated_root_accepting_path
#print axioms freeDerives_valid_derives
#print axioms freeDerives_run_derives
#print axioms freeDerives_accepting_derives
#print axioms allocated_root_path_of_formula
#print axioms allocated_root_path_of_satisfied_run
#print axioms allocated_root_path_of_original_run
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``allocated_root_accepting_path, ``freeDerives_valid_derives, ``freeDerives_run_derives, ``freeDerives_accepting_derives, ``allocated_root_path_of_formula, ``allocated_root_path_of_satisfied_run, ``allocated_root_path_of_original_run] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "unapproved axiom: {ax}"
