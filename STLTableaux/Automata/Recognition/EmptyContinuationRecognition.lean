import STLTableaux.Automata.Translation.EmptyContinuationSupport

/-! The unfiltered empty-continuation convention preserves recognition.
Only an optional final empty tableau frame is removed for this language
comparison. No execution jump or locally contradictory closure is discarded. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
variable (X : Set Var) (root : Formula.NormalizedInput Var)
local notation "T" => inputTableau (Clock := Clock) X root
local notation "U" => withEmptyContinuation (Clock := Clock) X root
local notation "Tr" => Section3.TransitionForm Clock Var
local notation "labs" => (JudgementTableau.labels (Clock := Clock) (Var := Var))
local notation "hfin" => (JudgementTableau.labels_finite (Clock := Clock) (Var := Var))

private theorem trimEmpty (p : Path Clock Tr) (valid : p.valid U)
    (first : p.firstState ∈ (T).states) (final : p.lastState ∈ (U).final) :
    ∃ q : Path Clock Tr, q.accepting T ∧ q.firstIncoming = p.firstIncoming ∧
      q.firstState = p.firstState ∧ ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
        (α : ClockValuation Clock) k,
        (p.trace labs hfin).holds σ P α k → (q.trace labs hfin).holds σ P α k := by
  induction p with
  | last l s =>
    have goal : s ∈ (T).final := by
      rcases final with empty | old
      · exact ⟨show s.nextPart = none by rw [show s = emptyMode from empty]; rfl, first⟩
      · exact old
    exact ⟨.last l s, ⟨first, goal⟩, rfl, rfl, fun _ _ _ _ => id⟩
  | step l s p ih =>
    rcases valid.2.2 with old | added
    · obtain ⟨q, goal, incoming, state, trace⟩ := ih valid.2.1 old.2.2 final
      refine ⟨.step l s q, ⟨⟨first, goal.1, ?_⟩, goal.2⟩, rfl, rfl, ?_⟩
      · simpa only [incoming, state] using old
      · intro σ P α k sat
        refine ⟨sat.1, ?_⟩
        have tail := sat.2
        by_cases hk : k.val < P.size
        · simp only [dif_pos hk] at tail ⊢
          exact trace _ _ _ _ tail
        · simp only [dif_neg hk] at tail
    · obtain ⟨goal, _, incoming, state⟩ := added
      cases p with
      | step l' s' p' =>
        change s' = emptyMode at state
        subst s'
        exact (emptyContinuation_edge_empty_absurd X root valid.2.1.2.2).elim
      | last l' s' =>
        exact ⟨.last l s, ⟨first, goal⟩, rfl, rfl, fun _ _ _ _ sat => sat.1⟩

theorem recognizes_original_of_emptyContinuation (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (recognized : (U).recognizes hfin σ P) :
    (T).recognizes hfin σ P := by
  obtain ⟨p, run, accepting, trace⟩ := recognized
  have first : (p.firstIncoming, p.firstState) ∈ (T).initial := run.2
  obtain ⟨q, goal, incoming, state, preserve⟩ :=
    trimEmpty X root p run.1 first.2 accepting.2
  exact ⟨q, ⟨goal.1, by rw [incoming, state]; exact first⟩, goal,
    fun α => preserve _ _ _ _ (trace α)⟩

private theorem liftValid (p : Path Clock Tr) (valid : p.valid T) : p.valid U := by
  induction p with
  | last l s => exact Or.inr valid
  | step l s p ih => exact ⟨Or.inr valid.1, ih valid.2.1, Or.inl valid.2.2⟩

theorem emptyContinuation_recognizes_iff (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) :
    (U).recognizes hfin σ P ↔ (T).recognizes hfin σ P := by
  refine ⟨recognizes_original_of_emptyContinuation X root σ P, ?_⟩
  rintro ⟨p, run, goal, trace⟩
  exact ⟨p, ⟨liftValid X root p run.1, run.2⟩,
    ⟨liftValid X root p goal.1, Or.inr goal.2⟩, trace⟩

/-- Soundness on an arbitrary partition, with no finite-variability or stable
partition premise. Completeness needs stability, but this direction does not. -/
theorem formula_of_emptyContinuation_recognizes (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (recognized : (U).recognizes hfin σ P) :
    σ.Satisfies root.val ⟨0, le_rfl, σ.horizon_pos⟩ :=
  finiteRootTableau_sound X root.val σ P
    (recognizes_original_of_emptyContinuation X root σ P recognized)

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``recognizes_original_of_emptyContinuation,
      ``emptyContinuation_recognizes_iff, ``formula_of_emptyContinuation_recognizes] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do throwError "{name} uses unexpected axiom {ax}"

end STLTableau.Section4.Finiteness
