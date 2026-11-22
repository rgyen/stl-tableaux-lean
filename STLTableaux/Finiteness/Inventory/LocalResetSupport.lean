import STLTableaux.Closure.Subsumption.InvariantTransport

/-! A state-local reset support representative. This does not claim that
all guard clocks occur in the same state's labels, nor that trimming outer
resets of a transition form may ignore its next part. -/
namespace STLTableau.Section4.Finiteness.LocalResetSupport
open Section3
variable {Clock Var : Type*}

noncomputable def restrictResets (Λ : ClockResetSet Clock) (A : Set Clock) :
    ClockResetSet Clock := by
  classical
  exact ⟨fun c => if c ∈ A then Λ.value c else none, by
    apply Λ.finite_domain.subset
    rintro c ⟨a, ha⟩
    by_cases hc : c ∈ A
    · exact ⟨a, by simpa only [if_pos hc] using ha⟩
    · simp only [if_neg hc] at ha
      cases ha⟩

theorem restrictResets_clocks (Λ : ClockResetSet Clock) (A : Set Clock) :
    (restrictResets Λ A).clocks = Λ.clocks ∩ A := by
  classical
  ext c
  change (∃ a, (if c ∈ A then Λ.value c else (Option.none : Option NNReal)) = some a) ↔
    (∃ a, Λ.value c = some a) ∧ c ∈ A
  by_cases hc : c ∈ A
  · rw [if_pos hc]
    exact ⟨fun h => ⟨h, hc⟩, fun h => h.1⟩
  · rw [if_neg hc]
    constructor
    · rintro ⟨a, ha⟩
      cases ha
    · intro h
      exact (hc h.2).elim

theorem restrictResets_apply (Λ : ClockResetSet Clock) (A : Set Clock)
    (α : ClockValuation Clock) (c : Clock) (hc : c ∈ A) :
    (restrictResets Λ A).apply α c = Λ.apply α c := by
  classical
  simp [ClockResetSet.apply, restrictResets, hc]

noncomputable def state (S : Section3.StateForm Clock Var) : Section3.StateForm Clock Var :=
  { S with resets := restrictResets S.resets S.localClocks }

theorem resets_supported (S : Section3.StateForm Clock Var) :
    (state S).resets.clocks ⊆ S.localClocks := by
  change (restrictResets S.resets S.localClocks).clocks ⊆ _
  rw [restrictResets_clocks]
  exact Set.inter_subset_right

theorem holds_iff (S : Section3.StateForm Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (state S).holds σ P α k ↔ S.holds σ P α k := by
  have he : ∀ l ∈ S.locals, (l.holds σ P ((state S).resets.apply α) k ↔
      l.holds σ P (S.resets.apply α) k) := by
    intro l hl
    apply l.holds_congr_of_agree
    intro c hc
    exact restrictResets_apply S.resets S.localClocks α c ⟨l, hl, hc⟩
  constructor
  · rintro ⟨hg, hl⟩
    exact ⟨hg, fun l h => (he l h).mp (hl l h)⟩
  · rintro ⟨hg, hl⟩
    exact ⟨hg, fun l h => (he l h).mpr (hl l h)⟩

theorem invariant_iff (S : Section3.StateForm Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (state S).EvaluatedInvariant σ P α k ↔ S.EvaluatedInvariant σ P α k := by
  have he : ∀ l ∈ S.locals,
      l.EvaluatedInvariant σ P ((state S).resets.apply α) k ↔
      l.EvaluatedInvariant σ P (S.resets.apply α) k := by
    intro l hl
    apply l.evaluatedInvariant_congr_of_agree
    intro c hc
    exact restrictResets_apply S.resets S.localClocks α c ⟨l, hl, hc⟩
  constructor
  · intro hi l hl
    exact (he l hl).mp (hi l hl)
  · intro hi l hl
    exact (he l hl).mpr (hi l hl)

end STLTableau.Section4.Finiteness.LocalResetSupport
