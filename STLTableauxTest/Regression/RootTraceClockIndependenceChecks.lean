import STLTableaux.Finiteness.Correctness.RootTraceClockIndependence

open STLTableau.Section3 STLTableau.Section4.Finiteness

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``StateForm.restrictFree_freeClocks_subset,
      ``StateForm.restrictFree_components, ``TransitionForm.restrictFree_freeClocks_subset,
      ``TransitionForm.restrictFree_subsumed, ``ComponentsIncluded.restrictFree_target,
      ``SyntacticallySubsumed.restrictFree_target,
      ``ConcreteContextual.branch_free_subset, ``ConcreteContextual.closure_freeClocks_subset,
      ``derives_freeClocks_subset, ``derives_iff_freeDerives,
      ``ordinaryTrace_free_subset_fullTrace, ``finiteRootTableau_initial_freeClocks_empty,
      ``finiteRootTableau_fullTrace_closed, ``finiteRootTableau_trace_closed,
      ``finiteRootTableau_recognizes_of_one_trace,
      ``finiteRootTableau_recognizes_of_clock_schedule,
      ``finiteRootTableau_recognizes_of_realGuards] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
