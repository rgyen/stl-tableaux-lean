import STLTableaux.Automata.Recognition.PrunedExecutionEndpoint

open STLTableau STLTableau.Section4

/-- A single actual flow leaves exactly one tableau frame, regardless of its
duration. Its continuous witness remains attached to that same frame. -/
theorem flow_keeps_one_frame {Clock Var State : Type*}
    (T : Tableau Clock Var State) (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    (s t : (T.toAutomaton h τ hτ).State) (incoming : EdgeLabel Clock)
    (r : NNReal) (γ : Set.Icc (0 : ℝ) r → T.HAVar → ℝ)
    (hc : (T.toAutomaton h τ hτ).ContinuousStep s t r γ) :
    T.ExecutionPathWitness h τ hτ s t (.last incoming t.val.1.val) :=
  .flow r γ hc (.stop t incoming)

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Tableau.ExecutionPathWitness.valid, ``Tableau.executionSteps_path,
      ``Tableau.execution_steps, ``Tableau.execution_accepting_path_witness,
      ``Finiteness.pruned_execution_original_accepting_run_with_witness,
      ``Finiteness.pruned_execution_original_accepting_run, ``flow_keeps_one_frame] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
