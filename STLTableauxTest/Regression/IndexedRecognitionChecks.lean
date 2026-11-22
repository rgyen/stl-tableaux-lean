import STLTableaux.Automata.Recognition.IndexedRecognition

open STLTableau STLTableau.Section4
open STLTableau.Section4.Finiteness

/-- Two durations and three incoming labels. Both recurrences must refer to
the source frame's reset, not the destination frame's reset. -/
theorem three_frame_recognition {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (root : Formula Var)
    (incoming : Fin 3 → EdgeLabel Clock)
    (states : Fin 3 → Section3.TransitionForm Clock Var)
    (hs : ∀ i, states i ∈ (finiteRootTableau X root).states)
    (he : ∀ i : Fin 2,
      (states i.castSucc, incoming i.succ, states i.succ) ∈ (finiteRootTableau X root).edges)
    (hi : (incoming 0, states 0) ∈ (finiteRootTableau X root).initial)
    (hf : states 2 ∈ (finiteRootTableau X root).final)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (hlen : 2 ≤ P.size)
    (ν : ℕ → Clock → ℝ)
    (hg : ∀ i : Fin 3, ∀ g ∈ (incoming i).guards,
      Tableau.realComparison g.relation (ν i.val g.clock) g.bound)
    (h₀ : ν 1 = fun c => Trace.realReset (incoming 0).resets (ν 0) c +
      Judgement.duration P ⟨0, by omega⟩)
    (h₁ : ν 2 = fun c => Trace.realReset (incoming 1).resets (ν 1) c +
      Judgement.duration P ⟨1, by omega⟩)
    (hl : ∀ (i : Fin 3) (β : ClockValuation Clock),
      ∀ l ∈ JudgementTableau.labels (states i),
        l.holds σ P β ⟨i.val, by have := i.isLt; omega⟩) :
    (finiteRootTableau (Clock := Clock) X root).recognizes JudgementTableau.labels_finite σ P := by
  apply finiteRootTableau_recognizes_of_indexed_schedule X root 2 incoming states
    hs he hi hf σ P hlen ν hg ?_ hl
  intro i
  fin_cases i
  · exact h₀
  · exact h₁

/-- A zero-width middle piece retains its state, edge and reset in the exact trace. -/
theorem three_frame_singleton_same_trace {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (root : Formula Var)
    (incoming : Fin 3 → EdgeLabel Clock)
    (states : Fin 3 → Section3.TransitionForm Clock Var)
    (hs : ∀ i, states i ∈ (finiteRootTableau X root).states)
    (he : ∀ i : Fin 2,
      (states i.castSucc, incoming i.succ, states i.succ) ∈ (finiteRootTableau X root).edges)
    (hi : (incoming 0, states 0) ∈ (finiteRootTableau X root).initial)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (hlen : 2 ≤ P.size)
    (ν : ℕ → Clock → ℝ)
    (hg : ∀ i : Fin 3, ∀ g ∈ (incoming i).guards,
      Tableau.realComparison g.relation (ν i.val g.clock) g.bound)
    (h₀ : ν 1 = fun c => Trace.realReset (incoming 0).resets (ν 0) c +
      Judgement.duration P ⟨0, by omega⟩)
    (hzero : Judgement.duration P ⟨1, by omega⟩ = 0)
    (h₁ : ν 2 = Trace.realReset (incoming 1).resets (ν 1))
    (hl : ∀ (i : Fin 3) (β : ClockValuation Clock),
      ∀ l ∈ JudgementTableau.labels (states i),
        l.holds σ P β ⟨i.val, by have := i.isLt; omega⟩) :
    ∀ α, ((Path.ofIndexed 2 incoming states).trace JudgementTableau.labels
      JudgementTableau.labels_finite).holds σ P α ⟨0, by omega⟩ := by
  apply finiteRootTableau_indexed_trace_holds X root 2 incoming states
    hs he hi σ P hlen ν hg ?_ hl
  intro i
  fin_cases i
  · exact h₀
  · change ν 2 = fun c => Trace.realReset (incoming 1).resets (ν 1) c +
      (Judgement.duration P ⟨1, by omega⟩ : ℝ)
    rw [hzero]
    simpa using h₁

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``finiteRootTableau_given_trace_holds_of_realGuards,
      ``finiteRootTableau_indexed_trace_holds,
      ``finiteRootTableau_given_trace_holds_of_real_coordinates,
      ``finiteRootTableau_recognizes_of_indexed_schedule,
      ``finiteRootTableau_recognizes_of_real_coordinates,
      ``three_frame_recognition, ``three_frame_singleton_same_trace] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
