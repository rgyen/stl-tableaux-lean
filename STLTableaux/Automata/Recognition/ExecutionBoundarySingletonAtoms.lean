import STLTableaux.Automata.Recognition.ExecutionInducedPartitionReview
import STLTableaux.Automata.Recognition.ExecutionObservedPiece

/-! All atomic obligations in a zero-time block are observed on one boundary
singleton. This does not collapse the block's guards, resets, or tableau edges. -/
namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {σ : FiniteSignal T.HAVar} (e : (T.toAutomaton h τ hτ).Execution σ)

theorem reviewInducedPartition_beforeFlow_atoms
    {ρ : FiniteSignal Var} (hp : T.ProjectsTo σ ρ) (i : Fin e.count) :
    ∃ j : Fin e.reviewInducedPartition.size, j.val = 2 * i.val ∧
      (e.reviewInducedPartition.interval j).carrier =
        {e.boundary ⟨i.val, by omega⟩} ∧
      ∀ s : (T.toAutomaton h τ hτ).State,
        Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep s (e.start i) →
        ∀ a : AtomicProposition Var,
          Section3.Local.predicate (.plain (.atom a)) ∈ T.label s.val.1.val →
          ∀ u : ρ.Time, u.val ∈ (e.reviewInducedPartition.interval j).carrier →
            a.Holds (ρ.value u) := by
  obtain ⟨j, hj, heq⟩ := e.reviewInducedPartition_old_piece
    ⟨2 * i.val, by have := i.isLt; omega⟩
  have hpoint : (e.reviewInducedPartition.interval j).carrier =
      {e.boundary ⟨i.val, by omega⟩} := by
    rw [heq]
    change (IntervalPartition.pointOpenPiece e.boundary _).carrier = _
    rw [IntervalPartition.pointOpenPiece_carrier]
    simp
  refine ⟨j, hj, hpoint, ?_⟩
  intro s hs a ha u hu
  have obs : T.ExecutionObservedPiece h τ hτ e s.val.1.val
      (e.boundary ⟨i.val, by omega⟩) (e.boundary ⟨i.val, by omega⟩) :=
    .beforeFlow i s hs
  apply obs.atom T h τ hτ e hp a ha u
  simpa [hpoint] using hu

theorem reviewInducedPartition_earlyFinal_atoms
    {ρ : FiniteSignal Var} (hp : T.ProjectsTo σ ρ)
    (he : e.boundary ⟨e.count, by omega⟩ < σ.horizon) :
    ∃ j : Fin e.reviewInducedPartition.size, j.val = 2 * e.count ∧
      (e.reviewInducedPartition.interval j).carrier =
        {e.boundary ⟨e.count, by omega⟩} ∧
      ∀ s : (T.toAutomaton h τ hτ).State,
        Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep s e.finalState →
        ∀ a : AtomicProposition Var,
          Section3.Local.predicate (.plain (.atom a)) ∈ T.label s.val.1.val →
          ∀ u : ρ.Time, u.val ∈ (e.reviewInducedPartition.interval j).carrier →
            a.Holds (ρ.value u) := by
  rw [e.reviewInducedPartition_of_early he]
  refine ⟨⟨2 * e.count, by change 2 * e.count < 2 * (e.count + 1); omega⟩,
    rfl, e.completedPointOpenFlowPartition_stop_carrier he, ?_⟩
  intro s hs a ha u hu
  have obs : T.ExecutionObservedPiece h τ hτ e s.val.1.val
      (e.boundary ⟨e.count, by omega⟩) (e.boundary ⟨e.count, by omega⟩) :=
    .atFinal s hs he
  apply obs.atom T h τ hτ e hp a ha u
  simpa [e.completedPointOpenFlowPartition_stop_carrier he] using hu

end STLTableau.Section4.Tableau
