import STLTableaux.Automata.Recognition.ExecutionBoundaryObservations

open STLTableau STLTableau.Section4

#check Tableau.execution_initial_boundary_observation
#check Tableau.execution_intermediate_boundary_observation
#check Tableau.execution_final_boundary_observation

-- Singleton atoms follow from the observation; no marker/partition premise.
example {Clock Var State : Type*} (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {σ : FiniteSignal T.HAVar} (e : (T.toAutomaton h τ hτ).Execution σ)
    {ρ : FiniteSignal Var} (hp : T.ProjectsTo σ ρ)
    (a : AtomicProposition Var)
    (ha : STLTableau.Section3.Local.predicate (.plain (.atom a)) ∈
      T.label e.initialState.val.1.val)
    (u : ρ.Time) (hu : u.val = 0) : a.Holds (ρ.value u) := by
  exact (T.execution_initial_boundary_observation h τ hτ e).2.closed_atom
    T h τ hτ e hp a ha u (by rw [hu]; exact ⟨le_rfl, le_rfl⟩)

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Tableau.execution_initial_boundary_observation,
      ``Tableau.execution_intermediate_boundary_observation,
      ``Tableau.execution_final_boundary_observation] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
