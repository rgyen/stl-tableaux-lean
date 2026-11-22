import STLTableaux.Automata.Recognition.ExecutionObservedPath

open STLTableau STLTableau.Section4

#check Tableau.ObservedPath.frame_count
#check Tableau.ObservedPath.prepend_zero_jump
#check Tableau.ObservedPath.prepend_flow
#check Tableau.ObservedPath.prepend_flow_with_witness

-- The exceptional endpoint has no local-label satisfaction premise/conclusion.
example {Clock Var State : Type*} (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {σ : FiniteSignal T.HAVar} (e : (T.toAutomaton h τ hτ).Execution σ)
    (incoming : EdgeLabel Clock) (s : State)
    (ht : STLTableau.Section3.Local.terminal ∈ T.label s) :
    T.ObservedPath h τ hτ e (.last incoming s) σ.horizon σ.horizon [0] := by
  exact .last (Or.inr ⟨rfl, rfl, ht⟩) (by simp)

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Tableau.ObservedPath.prepend_zero_jump_with_witness,
      ``Tableau.ObservedPath.frame_count,
      ``Tableau.ObservedPath.prepend_zero_jump,
      ``Tableau.ObservedPath.prepend_flow,
      ``Tableau.ObservedPath.prepend_flow_with_witness] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
