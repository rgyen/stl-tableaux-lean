import STLTableaux.Finiteness.Correctness.SelectedAcceptingPath
open STLTableau.Section4.Finiteness
#check initial_accepting_path_of_relation_steps
#check initial_accepting_path_of_invariant_steps
#check initial_accepting_path_of_nonempty_steps
#print axioms initial_accepting_path_of_relation_steps
#print axioms initial_accepting_path_of_invariant_steps
#print axioms initial_accepting_path_of_nonempty_steps
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``initial_accepting_path_of_relation_steps, ``initial_accepting_path_of_invariant_steps, ``initial_accepting_path_of_nonempty_steps] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
