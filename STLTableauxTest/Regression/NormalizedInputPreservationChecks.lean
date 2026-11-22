import STLTableaux.Automata.Translation.NormalizedInputReachability

open STLTableau
open STLTableau.Section4.Finiteness

-- No accepting-path or signal-satisfaction premise may be inserted here.
example {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (p : Section4.Path Clock (Section3.TransitionForm Clock Var))
    (hr : p.run (inputTableau X root)) :
    Subgraph.AllStates
      {F | Section3.Local.predicate (.plain Formula.falsity) ∉
        (inputTableau X root).label F} p :=
  inputTableau_run_no_false X root p hr

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Section3.TransitionForm.normalize_normalizedReady,
      ``Section3.TransitionForm.AlphaEquivalent.normalizedReady,
      ``Section3.ConcreteMixed.branch_normalizedReady,
      ``Section3.ConcreteContextual.branch_normalizedReady,
      ``Section3.ConcreteContextual.closure_normalizedReady,
      ``SafeNormalization.normalizedReady, ``derives_normalizedReady,
      ``inputTableau_initial_normalizedReady, ``inputTableau_edge_normalizedReady,
      ``inputTableau_valid_normalizedReady, ``inputTableau_run_normalizedReady,
      ``inputTableau_modeSteps_normalizedReady, ``normalizedReady_current_not_false,
      ``inputTableau_run_no_false, ``inputTableau_reachable_no_false,
      ``inputAutomaton_final_no_false] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
