import STLTableaux.Automata.Translation.InitialClockSupport

open STLTableau.Section4.Finiteness

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``closed_initial_guards_empty, ``closed_initial_body_reset,
      ``closed_initial_guardsHold, ``closed_initial_body_clock_agreement,
      ``closed_initial_body_nonnegative, ``freeDerives_closed_initial,
      ``derives_closed_input_guards_empty, ``finiteRootTableau_initial_guards_empty,
      ``STLTableau.Section3.ClosureCatalogue.IsClosure.current_guards_eq,
      ``STLTableau.Section3.ConcreteContextual.branch_current_guards_empty,
      ``STLTableau.Section3.ConcreteContextual.closure_current_guards_eq] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
