import STLTableaux.Rules.Finite.Transitions
namespace STLTableau
open scoped STL
open STLTableau.Judgement
open STLTableau.IntervalPredicate
variable {Clock Var : Type*}

private theorem predicate_eventually_zero
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hc : (α c : ℝ) = 0) (hb : b = J.leftBoundary) (hJ : J.carrier ⊆ σ.domain) :
    predicateSatisfies σ J α (.plain (◇[(I : TimeInterval)] φ)) ↔
      predicateSatisfies σ J α (.upper c b .eventually I φ) := by
  subst b
  exact plain_eventually_iff_upper_zero σ J α c I φ hc hJ

private theorem predicate_always_zero
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hc : (α c : ℝ) = 0) (hb : b = J.leftBoundary)
    (hne : J.carrier.Nonempty) (hJ : J.carrier ⊆ σ.domain) :
    predicateSatisfies σ J α (.plain (□[(I : TimeInterval)] φ)) ↔
      predicateSatisfies σ J α (.upper c b .always I φ) := by
  subst b
  exact plain_always_iff_upper_zero σ J α c I φ hc hne hJ

private theorem predicate_always_of_upper_zero
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hc : (α c : ℝ) = 0) (hb : b = J.leftBoundary)
    (h : predicateSatisfies σ J α (.upper c b .always I φ)) :
    predicateSatisfies σ J α (.plain (□[(I : TimeInterval)] φ)) := by
  exact IntervalPredicate.satisfies_plain_always_of_upper_of_zero σ J α c b I φ hc hb
    (fun t ht _ => h t ht)

/-- Fixed-marker form used internally to prove the satisfaction-driven form
of Proposition 3.10 (1). -/
theorem satisfies_plain_eventually_iff_reset_upper_of_marker
    [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Position P) (hk : k.1 < P.size) (c : Clock) (b : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hb : b = (P.interval ⟨k.1, hk⟩).leftBoundary) :
    ((σ, P, α, k) ⊨ₚ
      ((IntervalPredicate.plain (◇[(I : TimeInterval)] φ) :
        IntervalPredicate Clock Var) : Judgement Clock Var)) ↔
    ((σ, P, α, k) ⊨ₚ
      (⟦c ↦ᶜ 0⟧ ·ⱼ
        ((↑[c, b] ◇[I] φ : IntervalPredicate Clock Var) ∧ⱼ lty[b]))) := by
  let i : Fin P.size := ⟨k.1, hk⟩
  have hJ : (P.interval i).carrier ⊆ σ.domain := by
    intro t ht
    rw [← P.covers]
    exact Set.mem_iUnion.2 ⟨i, ht⟩
  have hpred := predicate_eventually_zero
    σ (P.interval i) (⟦c ↦ᶜ 0⟧.apply α) c b I φ
    (by simp) hb hJ
  change
    (if h : k.1 < P.size then
      (σ, P.interval ⟨k.1, h⟩, α) ⊨ₚᵢ
        IntervalPredicate.plain (◇[(I : TimeInterval)] φ)
    else False) ↔
      ((if h : k.1 < P.size then
        (σ, P.interval ⟨k.1, h⟩, ⟦c ↦ᶜ 0⟧.apply α) ⊨ₚᵢ
          (↑[c, b] ◇[I] φ)
      else False) ∧
        (if h : k.1 < P.size then
          (P.interval ⟨k.1, h⟩).leftBoundary = b
        else b = ●))
  simp only [dif_pos hk]
  dsimp [i] at hpred
  change
    ((σ, P.interval ⟨k.1, hk⟩, α) ⊨ₚᵢ
      IntervalPredicate.plain (◇[(I : TimeInterval)] φ)) ↔ _ at hpred
  rw [hpred]
  simp [hb]

/-- Eventuality instance of Proposition 3.10 (1). The marker is selected
inside satisfaction: `lty[b]` ensures that the witness `b` is precisely the
left marker of the current partition interval. -/
private theorem satisfies_plain_eventually_iff_reset_upper_of_valid_position
    [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Position P) (hk : k.1 < P.size) (c : Clock)
    (I : BoundedTimeInterval) (φ : Formula Var) :
    ((σ, P, α, k) ⊨ₚ
      ((IntervalPredicate.plain (◇[(I : TimeInterval)] φ) :
        IntervalPredicate Clock Var) : Judgement Clock Var)) ↔
    ∃ b : Marker,
      ((σ, P, α, k) ⊨ₚ
        (⟦c ↦ᶜ 0⟧ ·ⱼ
          ((↑[c, b] ◇[I] φ : IntervalPredicate Clock Var) ∧ⱼ lty[b]))) := by
  constructor
  · intro h
    let b := (P.interval ⟨k.1, hk⟩).leftBoundary
    refine ⟨b, ?_⟩
    exact (satisfies_plain_eventually_iff_reset_upper_of_marker
      σ P α k hk c b I φ rfl).1 h
  · rintro ⟨b, h⟩
    have hb : b = (P.interval ⟨k.1, hk⟩).leftBoundary := by
      have hmarker : (P.interval ⟨k.1, hk⟩).leftBoundary = b := by
        change
          (if hp : k.1 < P.size then
            (σ, P.interval ⟨k.1, hp⟩, ⟦c ↦ᶜ 0⟧.apply α) ⊨ₚᵢ
              (↑[c, b] ◇[I] φ)
          else False) ∧
            (if hp : k.1 < P.size then
              (P.interval ⟨k.1, hp⟩).leftBoundary = b
            else b = ●) at h
        exact (by simpa only [dif_pos hk] using h.2)
      exact hmarker.symm
    exact (satisfies_plain_eventually_iff_reset_upper_of_marker
      σ P α k hk c b I φ hb).2 h

/-- Eventuality instance of Proposition 3.10 (1), including the terminal
position. The marker is bound existentially and checked solely by `lty[b]`. -/
theorem satisfies_plain_eventually_iff_reset_upper
    [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Position P) (c : Clock) (I : BoundedTimeInterval) (φ : Formula Var) :
    ((σ, P, α, k) ⊨ₚ
      ((IntervalPredicate.plain (◇[(I : TimeInterval)] φ) :
        IntervalPredicate Clock Var) : Judgement Clock Var)) ↔
    ∃ b : Marker,
      ((σ, P, α, k) ⊨ₚ
        (⟦c ↦ᶜ 0⟧ ·ⱼ
          ((↑[c, b] ◇[I] φ : IntervalPredicate Clock Var) ∧ⱼ lty[b]))) := by
  by_cases hk : k.1 < P.size
  · exact satisfies_plain_eventually_iff_reset_upper_of_valid_position
      σ P α k hk c I φ
  · simp [satisfies, hk]

/-- Proven direction of the always instance of Proposition 3.10 (1).
Marker selection remains internal to judgement satisfaction. -/
theorem reset_upper_always_implies_plain
    [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Position P) (c : Clock) (I : BoundedTimeInterval) (φ : Formula Var) :
    (∃ b : Marker,
      ((σ, P, α, k) ⊨ₚ
        (⟦c ↦ᶜ 0⟧ ·ⱼ
          ((↑[c, b] □[I] φ : IntervalPredicate Clock Var) ∧ⱼ lty[b])))) →
    ((σ, P, α, k) ⊨ₚ
      ((IntervalPredicate.plain (□[(I : TimeInterval)] φ) :
        IntervalPredicate Clock Var) : Judgement Clock Var)) := by
  by_cases hk : k.1 < P.size
  · rintro ⟨b, h⟩
    change
      (if hp : k.1 < P.size then
        (σ, P.interval ⟨k.1, hp⟩, ⟦c ↦ᶜ 0⟧.apply α) ⊨ₚᵢ
          (↑[c, b] □[I] φ)
      else False) ∧
        (if hp : k.1 < P.size then
          (P.interval ⟨k.1, hp⟩).leftBoundary = b
        else b = ●) at h
    simp only [dif_pos hk] at h
    change
      (if hp : k.1 < P.size then
        (σ, P.interval ⟨k.1, hp⟩, α) ⊨ₚᵢ
          IntervalPredicate.plain (□[(I : TimeInterval)] φ)
      else False)
    rw [dif_pos hk]
    exact predicate_always_of_upper_zero
      σ (P.interval ⟨k.1, hk⟩) (⟦c ↦ᶜ 0⟧.apply α) c b I φ
      (by simp) h.2.symm h.1
  · simp [satisfies, hk]

/-- Complete satisfaction-level always characterization corresponding to
Proposition 3.10 (1). -/
theorem satisfies_plain_always_iff_reset_upper
    [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Position P) (c : Clock) (I : BoundedTimeInterval) (φ : Formula Var) :
    ((σ, P, α, k) ⊨ₚ
      ((IntervalPredicate.plain (□[(I : TimeInterval)] φ) :
        IntervalPredicate Clock Var) : Judgement Clock Var)) ↔
    ∃ b : Marker,
      ((σ, P, α, k) ⊨ₚ
        (⟦c ↦ᶜ 0⟧ ·ⱼ
          ((↑[c, b] □[I] φ : IntervalPredicate Clock Var) ∧ⱼ lty[b]))) := by
  constructor
  · intro h
    by_cases hk : k.1 < P.size
    · let i : Fin P.size := ⟨k.1, hk⟩
      let b := (P.interval i).leftBoundary
      have hplain : (σ, P.interval i, ⟦c ↦ᶜ 0⟧.apply α) ⊨ₚᵢ
          IntervalPredicate.plain (□[(I : TimeInterval)] φ) := by
        have h' : (σ, P.interval ⟨k.1, hk⟩, α) ⊨ₚᵢ
            IntervalPredicate.plain (□[(I : TimeInterval)] φ) := by
          change (if hp : k.1 < P.size then
            (σ, P.interval ⟨k.1, hp⟩, α) ⊨ₚᵢ
              IntervalPredicate.plain (□[(I : TimeInterval)] φ)
            else False) at h
          simpa only [dif_pos hk] using h
        simpa [i, predicateSatisfies] using h'
      have hJ : (P.interval i).carrier ⊆ σ.domain := by
        intro t ht
        rw [← P.covers]
        exact Set.mem_iUnion.2 ⟨i, ht⟩
      have hupper := (predicate_always_zero
        σ (P.interval i) (⟦c ↦ᶜ 0⟧.apply α) c b I φ
        (by simp) rfl (P.nonempty i) hJ).1 hplain
      refine ⟨b, ?_⟩
      change
        (if hp : k.1 < P.size then
          (σ, P.interval ⟨k.1, hp⟩, ⟦c ↦ᶜ 0⟧.apply α) ⊨ₚᵢ
            (↑[c, b] □[I] φ)
        else False) ∧
          (if hp : k.1 < P.size then
            (P.interval ⟨k.1, hp⟩).leftBoundary = b
          else b = ●)
      simp only [dif_pos hk]
      exact ⟨hupper, rfl⟩
    · simp [satisfies, hk] at h
  · exact reset_upper_always_implies_plain σ P α k c I φ

/-- Part (1), with the marker fixed before the semantic context. -/
theorem satisfies_plain_always_iff_reset_upper_of_marker
    [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Position P) (hk : k.1 < P.size) (c : Clock) (m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hm : m = (P.interval ⟨k.1, hk⟩).leftBoundary) :
    ((σ, P, α, k) ⊨ₚ (Judgement.predicate (.plain (□[(I : TimeInterval)] φ)))) ↔
    ((σ, P, α, k) ⊨ₚ (⟦c ↦ᶜ 0⟧ ·ⱼ
      ((↑[c, m]□[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[m]))) := by
  rw [satisfies_plain_always_iff_reset_upper]
  constructor
  · rintro ⟨b, hb⟩
    have heq : (P.interval ⟨k.1, hk⟩).leftBoundary = b := by
      simpa only [satisfies, dif_pos hk] using hb.2
    simpa only [hm.trans heq] using hb
  · intro h
    exact ⟨m, h⟩

/-- Fixed-marker judgement equivalence. The same marker test is included
on the left, so this is an unrestricted `Equivalent`, not an existential
choice of a marker after the context has been selected. -/
theorem plain_eventually_fixed_marker_equiv [DecidableEq Clock]
    (c : Clock) (m : Marker) (I : BoundedTimeInterval) (φ : Formula Var) :
    (Judgement.predicate (.plain (◇[(I : TimeInterval)] φ)) ∧ⱼ lty[m]) ≡ₚ
      (⟦c ↦ᶜ 0⟧ ·ⱼ ((↑[c, m]◇[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[m])) := by
  intro σ P α k
  by_cases hk : k.1 < P.size
  · by_cases hm : m = (P.interval ⟨k.1, hk⟩).leftBoundary
    · have h := satisfies_plain_eventually_iff_reset_upper_of_marker
        σ P α k hk c m I φ hm
      simpa only [satisfies, dif_pos hk, hm, and_true] using h
    · simp [satisfies, hk, Ne.symm hm]
  · simp [satisfies, hk]

theorem plain_always_fixed_marker_equiv [DecidableEq Clock]
    (c : Clock) (m : Marker) (I : BoundedTimeInterval) (φ : Formula Var) :
    (Judgement.predicate (.plain (□[(I : TimeInterval)] φ)) ∧ⱼ lty[m]) ≡ₚ
      (⟦c ↦ᶜ 0⟧ ·ⱼ ((↑[c, m]□[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[m])) := by
  intro σ P α k
  by_cases hk : k.1 < P.size
  · by_cases hm : m = (P.interval ⟨k.1, hk⟩).leftBoundary
    · have h := satisfies_plain_always_iff_reset_upper_of_marker
        σ P α k hk c m I φ hm
      simpa only [satisfies, dif_pos hk, hm, and_true] using h
    · simp [satisfies, hk, Ne.symm hm]
  · simp [satisfies, hk]


/-- The decomposition of the `↑` predicate into `↑↓` and unclocked predicates needs endpoint
compatibility when the source clock is zero. No source marker is silently
changed to make this theorem true. -/
theorem upper_decomposition_zero (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c d : Clock) (b : Marker) (kind : TemporalKind)
    (I : BoundedTimeInterval) (φ : Formula Var) (hd : (α d : ℝ) = 0)
    (hne : J.carrier.Nonempty) (hD : J.carrier ⊆ σ.domain)
    (hmarker : (α c : ℝ) = 0 → J.leftBoundary.Includes → b.Includes) :
    predicateSatisfies σ J α (.upper c b kind I φ) ↔
      predicateSatisfies σ J α (.bounded c d b (¬ₘ J.leftBoundary) kind I φ) ∧
        predicateSatisfies σ J α (.plain (IntervalPredicate.upper c b kind I φ).formula) := by
  have hplain : predicateSatisfies σ J α (.plain (IntervalPredicate.upper c b kind I φ).formula) ↔
      temporalSatisfies σ kind I φ (Scope.ofMarkedInterval J) := by
    cases kind with
    | eventually =>
        exact (plain_eventually_iff_upper_zero σ J α d I φ hd hD).trans
          (by simp [scope, Scope.ofMarkedInterval, hd])
    | always =>
        exact (plain_always_iff_upper_zero σ J α d I φ hd hne hD).trans
          (by simp [scope, Scope.ofMarkedInterval, hd])
  rw [upper_temporal, bounded_temporal, hplain]
  apply (temporal_union σ kind I φ ?_ ?_).symm
  · cases kind <;> simpa only [scope, hd, sub_zero] using
      carrier_union_split_upperScope J α c b hne hmarker
  · cases kind <;> simpa only [scope, hd, sub_zero] using
      carrier_union_split_upperAlwaysRegion J α c b I hne hmarker

/-- Corrected reset-and-marker form of Proposition 3.10 (2).
The actual partition marker and the zero-clock endpoint compatibility are
explicit; the terminal position is included. -/
theorem satisfies_upper_iff_reset_bounded_and_plain [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P)
    (c d : Clock) (b m : Marker) (kind : TemporalKind)
    (I : BoundedTimeInterval) (φ : Formula Var) (hcd : c ≠ d)
    (hm : ∀ hk : k.1 < P.size, m = (P.interval ⟨k.1, hk⟩).leftBoundary)
    (hmarker : (α c : ℝ) = 0 → m.Includes → b.Includes) :
    satisfies σ P α k (.predicate (.upper c b kind I φ)) ↔
      satisfies σ P α k
        ((⟦d ↦ᶜ 0⟧ ·ⱼ
          (.predicate (.bounded c d b (¬ₘ m) kind I φ) ∧ⱼ lty[m])) ∧ⱼ
          .predicate (.plain (IntervalPredicate.upper c b kind I φ).formula)) := by
  by_cases hk : k.1 < P.size
  · let J := P.interval ⟨k.1, hk⟩
    let β := (⟦d ↦ᶜ 0⟧).apply α
    have hmJ : m = J.leftBoundary := hm hk
    have hβc : β c = α c := ClockResetSet.apply_singleton_of_ne 0 α hcd
    have hβd : β d = 0 := ClockResetSet.apply_singleton_self d 0 α
    have hJ : J.carrier ⊆ σ.domain := by
      intro t ht
      rw [← P.covers]
      exact Set.mem_iUnion.2 ⟨⟨k.1, hk⟩, ht⟩
    have hs := upper_decomposition_zero σ J β c d b kind I φ
      (by simp only [hβd, NNReal.coe_zero]) (P.nonempty _) hJ
      (by rw [hβc, ← hmJ]; exact hmarker)
    have hupper : predicateSatisfies σ J β (.upper c b kind I φ) ↔
        predicateSatisfies σ J α (.upper c b kind I φ) := by
      cases kind <;> simp only [predicateSatisfies, scope, hβc]
    have hplain : predicateSatisfies σ J β
        (.plain (IntervalPredicate.upper c b kind I φ).formula) ↔
        predicateSatisfies σ J α
          (.plain (IntervalPredicate.upper c b kind I φ).formula) := Iff.rfl
    rw [hupper, hplain] at hs
    rw [← hmJ] at hs
    simpa only [satisfies, dif_pos hk, ← hm hk, and_true, J, β] using hs
  · simp [satisfies, hk]

/-- Current printed part (2), with the unclocked predicate inside the
fresh reset, exactly as in the updated statement. -/
theorem satisfies_upper_iff_reset_split [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P)
    (c d : Clock) (b m : Marker) (kind : TemporalKind)
    (I : BoundedTimeInterval) (φ : Formula Var) (hcd : c ≠ d)
    (hm : ∀ hk : k.1 < P.size, m = (P.interval ⟨k.1, hk⟩).leftBoundary)
    (hmarker : (α c : ℝ) = 0 → m.Includes → b.Includes) :
    satisfies σ P α k (.predicate (.upper c b kind I φ)) ↔
      satisfies σ P α k
        (⟦d ↦ᶜ 0⟧ ·ⱼ
          ((.predicate (.bounded c d b (¬ₘ m) kind I φ) ∧ⱼ lty[m]) ∧ⱼ
            .predicate (.plain (IntervalPredicate.upper c b kind I φ).formula))) := by
  have h := satisfies_upper_iff_reset_bounded_and_plain
    σ P α k c d b m kind I φ hcd hm hmarker
  simpa only [satisfies, predicateSatisfies] using h

/-- Proposition (2) under its intended current-interval containment convention.
At the terminal position the containment premise is vacuous. -/
theorem satisfies_upper_iff_reset_split_of_contains [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P)
    (c d : Clock) (b m : Marker) (kind : TemporalKind)
    (I : BoundedTimeInterval) (φ : Formula Var) (hcd : c ≠ d)
    (hm : ∀ hk : k.1 < P.size, m = (P.interval ⟨k.1, hk⟩).leftBoundary)
    (hcontains : ∀ hk : k.1 < P.size,
      (P.interval ⟨k.1, hk⟩).carrier ⊆
        (scope (P.interval ⟨k.1, hk⟩) α (.upper c b kind I φ)).carrier) :
    satisfies σ P α k (.predicate (.upper c b kind I φ)) ↔
      satisfies σ P α k
        (⟦d ↦ᶜ 0⟧ ·ⱼ
          ((.predicate (.bounded c d b (¬ₘ m) kind I φ) ∧ⱼ lty[m]) ∧ⱼ
            .predicate (.plain (IntervalPredicate.upper c b kind I φ).formula))) := by
  by_cases hk : k.1 < P.size
  · apply satisfies_upper_iff_reset_split σ P α k c d b m kind I φ hcd hm
    rw [hm hk]
    exact (current_subset_upperScope_iff _ α c b (P.nonempty _)).1 (hcontains hk)
  · simp [satisfies, hk]

end STLTableau
