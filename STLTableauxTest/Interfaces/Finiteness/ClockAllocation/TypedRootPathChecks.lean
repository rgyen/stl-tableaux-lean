import STLTableaux.Finiteness.ClockAllocation.TypedRootPath
open STLTableau.Section4.Finiteness
#print axioms typed_root_accepting_path
#print axioms finiteRootTableau_accepting_path_of_formula
#print axioms finiteRootTableau_accepting_path_of_revised_run
#print axioms finiteRootTableau_accepting_path_of_original_run
#print axioms finiteRootTableau_complete
#print axioms finiteRootTableau_recognizes_iff
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``typed_root_accepting_path, ``finiteRootTableau_accepting_path_of_formula, ``finiteRootTableau_accepting_path_of_revised_run, ``finiteRootTableau_accepting_path_of_original_run, ``finiteRootTableau_complete, ``finiteRootTableau_recognizes_iff] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "unapproved axiom: {ax}"
