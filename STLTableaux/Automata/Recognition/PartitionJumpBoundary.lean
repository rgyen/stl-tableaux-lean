import STLTableaux.Automata.Recognition.ForwardVisits

namespace STLTableau.Section4.Tableau
open Section3
variable {Clock Var State : Type*}

/-- Adjacent partition ownership gives exactly the two jump-marker tests. -/
theorem partition_adjacent_jump_markers (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (i j : Fin P.size) (adj : i.val + 1 = j.val) :
    ((P.interval j).leftBoundary = ○ → (P.interval i).rightBoundary = ●) ∧
    ((STLTableau.Judgement.duration P i : ℝ) = 0 →
      (P.interval i).leftBoundary = ● ∧ (P.interval j).leftBoundary = ○) := by
  have hi : i.val + 1 < P.size := adj ▸ j.isLt
  have ij : (⟨i.val + 1, hi⟩ : Fin P.size) = j := Fin.ext adj
  have boundary := P.adjacent_rightBoundary_eq_complement_leftBoundary i hi
  rw [ij] at boundary
  constructor
  · intro hopen
    simp [boundary, hopen]
  · intro zero
    obtain ⟨left, right⟩ := partition_singleton_markers σ P i zero
    refine ⟨left, ?_⟩
    cases hm : (P.interval j).leftBoundary <;> simp_all

/-- The source owns an open successor's boundary, so its atoms are checked
at the actual post-boundary signal value without any continuity premise. -/
theorem partition_source_atoms_at_open_successor (T : Tableau Clock Var State)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (i j : Fin P.size) (adj : i.val + 1 = j.val)
    (q : T.states) (β : ClockValuation Clock)
    (labels : ∀ l ∈ T.label q.val, l.holds σ P β ⟨i.val, by omega⟩)
    (hopen : (P.interval j).leftBoundary = ○) :
    ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      a.Holds (σ.value (pieceEntry σ P j)) := by
  intro a ha
  have hold := labels (.predicate (.plain (.atom a))) ha
  simp only [Local.holds, Local.toJudgement, Section3.Judgement.holds, dif_pos i.isLt,
    Predicate.holds, predicateSatisfies, FiniteSignal.Satisfies] at hold
  apply hold
  have hi : i.val + 1 < P.size := adj ▸ j.isLt
  have ij : (⟨i.val + 1, hi⟩ : Fin P.size) = j := Fin.ext adj
  have joint := P.adjacent_right_eq_left i hi
  rw [ij] at joint
  change (P.interval j).left ∈ P.interval i
  rw [← joint]
  apply (P.interval i).right_mem (P.nonempty i)
  rw [(partition_adjacent_jump_markers σ P i j adj).1 hopen]
  trivial

run_elab do
  for name in #[``partition_singleton_markers, ``partition_adjacent_jump_markers,
      ``partition_source_atoms_at_open_successor] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end STLTableau.Section4.Tableau
