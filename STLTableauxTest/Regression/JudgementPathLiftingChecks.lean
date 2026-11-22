import STLTableaux.Finiteness.Correctness.JudgementPathLifting

open STLTableau.Section4.Finiteness.JudgementTableau

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``exists_generator_lift_valid, ``exists_generator_lift_accepting_run,
      ``recognizes_iff_generator_pairs] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
