import STLTableaux.Finiteness.Correctness.FiniteRootTableauEdges
open STLTableau.Section4.Finiteness
#check Subgraph.judgement_restriction_edges_finite
#check Subgraph.judgement_restriction_initial_finite
#check Subgraph.judgement_restriction_final_finite
#check finiteRootTableau_edges_finite
#check finiteRootTableau_initial_finite
#check finiteRootTableau_final_finite
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Subgraph.judgement_restriction_edges_finite, ``Subgraph.judgement_restriction_initial_finite, ``Subgraph.judgement_restriction_final_finite, ``finiteRootTableau_edges_finite, ``finiteRootTableau_initial_finite, ``finiteRootTableau_final_finite] do
    let axs ← Lean.collectAxioms name
    Lean.logInfo m!"{name}: {axs}"
    for axiomName in axs do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom: {axiomName}"
