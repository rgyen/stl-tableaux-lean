import STLTableaux.Finiteness.Correctness.JudgementTraceFreeSupport
open STLTableau.Section4.Finiteness
#check JudgementTableau.fullTrace_free_subset_input
#check JudgementTableau.fullTrace_closed_of_run
#check JudgementTableau.fullTrace_holds_all_valuations
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``JudgementTableau.fullTrace_free_subset_input,
    ``JudgementTableau.fullTrace_closed_of_run, ``JudgementTableau.fullTrace_holds_all_valuations] do
    let axs ← Lean.collectAxioms name
    Lean.logInfo m!"{name}: {axs}"
    for axiomName in axs do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom: {axiomName}"
