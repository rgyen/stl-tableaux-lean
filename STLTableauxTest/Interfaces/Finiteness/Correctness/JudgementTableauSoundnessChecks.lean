import STLTableaux.Finiteness.Correctness.JudgementTableauSoundness

open STLTableau.Section4.Finiteness.JudgementTableau

#check LocalLaws
#check nonPredicate_of_atomic_trace
#check fullTrace_and_input_of_atomic_trace
#check fullTrace_and_root_of_accepting_run
#check formula_of_recognizes
#print axioms nonPredicate_of_atomic_trace
#print axioms fullTrace_and_input_of_atomic_trace
#print axioms fullTrace_and_root_of_accepting_run
#print axioms formula_of_recognizes

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``nonPredicate_of_atomic_trace, ``fullTrace_and_input_of_atomic_trace,
      ``fullTrace_and_root_of_accepting_run, ``formula_of_recognizes] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
