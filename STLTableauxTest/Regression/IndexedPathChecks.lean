import STLTableaux.Automata.Recognition.IndexedPath

open STLTableau STLTableau.Section4

variable {Clock Var State : Type*}

/-- Two flow frames followed by a goal: no incoming label is shifted or lost. -/
theorem indexed_three_frames (incoming : Fin 3 → EdgeLabel Clock) (states : Fin 3 → State) :
    Path.ofIndexed 2 incoming states =
      .step (incoming 0) (states 0)
        (.step (incoming 1) (states 1) (.last (incoming 2) (states 2))) := rfl

theorem indexed_run_and_goal (T : Tableau Clock Var State) (n : ℕ)
    (incoming : Fin (n + 1) → EdgeLabel Clock) (states : Fin (n + 1) → State)
    (hs : ∀ i, states i ∈ T.states)
    (he : ∀ i : Fin n, (states i.castSucc, incoming i.succ, states i.succ) ∈ T.edges)
    (hi : (incoming 0, states 0) ∈ T.initial)
    (hf : states (Fin.last n) ∈ T.final) :
    ∃ p : Path Clock State, p.run T ∧ p.accepting T ∧
      p.firstIncoming = incoming 0 ∧ p.lastState = states (Fin.last n) := by
  exact ⟨Path.ofIndexed n incoming states,
    Path.ofIndexed_run T n incoming states hs he hi,
    Path.ofIndexed_accepting T n incoming states hs he hf,
    Path.ofIndexed_firstIncoming _ _ _, Path.ofIndexed_lastState _ _ _⟩

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Path.ofIndexed_valid, ``Path.ofIndexed_run,
      ``Path.ofIndexed_accepting, ``Path.ofIndexed_trace_length,
      ``Path.ofIndexed_trace_frameAt, ``indexed_three_frames, ``indexed_run_and_goal] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
