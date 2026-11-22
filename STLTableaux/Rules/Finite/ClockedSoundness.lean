import STLTableaux.Rules.Finite.Bridge
import STLTableaux.Rules.Finite.Equivalences
import STLTableaux.Semantics.Intervals.IntervalLemmas

namespace STLTableau
open scoped STL
open STLTableau.ExpansionRule
variable {Clock Var : Type*}

@[simp] theorem satisfies_markedLT (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (c : Clock) (m : Marker) (a : NNReal) :
    satisfies σ P α k (Judgement.markedLT c m a) ↔ (α c : ℝ) <[m] (a : ℝ) := by
  cases m <;> simp [Judgement.markedLT, satisfies, ClockRelation.Holds]

@[simp] theorem satisfies_markedGT (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (c : Clock) (m : Marker) (a : NNReal) :
    satisfies σ P α k (Judgement.markedGT c m a) ↔ (a : ℝ) <[m] (α c : ℝ) := by
  cases m <;> simp [Judgement.markedGT, satisfies, ClockRelation.Holds]

private theorem current_witness
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hne : J.carrier.Nonempty) (hD : J.carrier ⊆ σ.domain)
    (hr : (α c : ℝ) <[Marker.imp b J.leftBoundary] I.upper)
    (hφ : predicateSatisfies σ J α (.plain φ)) (t : ℝ)
    (ht : J.left - (α c : ℝ) <[b] t)
    (hcut : t + I.lower <[J.rightBoundary] J.right) :
    ∃ u : σ.Time, u.val ∈ (I : TimeInterval).translate t ∧ (σ, u)⊨φ := by
  have hcover : t ∈ timingDifference J.carrier (.bounded I) :=
    IntervalPredicate.exists_current_point_of_marked_bounds J α c b I hne hr t ht hcut
  exact eventually_witness_of_timingDifference σ J.carrier (.bounded I) φ hD hφ t hcover

private theorem bounded_current_witness
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hne : J.carrier.Nonempty) (hD : J.carrier ⊆ σ.domain)
    (hi : IntervalPredicate.Invariant J α (.bounded c d b q .eventually I φ))
    (hφ : predicateSatisfies σ J α (.plain φ)) (t : ℝ)
    (ht : t ∈ IntervalPredicate.scope J α (.bounded c d b q .eventually I φ))
    (hcut : t + I.lower <[J.rightBoundary] J.right) :
    ∃ u : σ.Time, u.val ∈ (I : TimeInterval).translate t ∧ (σ, u)⊨φ :=
  current_witness σ J α c b I φ hne hD hi.1 hφ t ht.1 hcut

private theorem bounded_plain_finish
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hne : J.carrier.Nonempty) (hD : J.carrier ⊆ σ.domain)
    (hi : IntervalPredicate.Invariant J α (.bounded c d b q .eventually I φ))
    (hg : I.lower <[Marker.imp q J.rightBoundary]
      ((α d : ℝ) + (J.right - J.left)))
    (hφ : predicateSatisfies σ J α (.plain φ)) :
    predicateSatisfies σ J α (.bounded c d b q .eventually I φ) := by
  intro t ht
  exact bounded_current_witness σ J α c d b q I φ hne hD hi hφ t ht
    (IntervalPredicate.eventually_finish_cut J α d q I.lower ht.2 hg)

private theorem upper_plain_zero
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hne : J.carrier.Nonempty) (hD : J.carrier ⊆ σ.domain) (hz : I.lower = 0)
    (hi : IntervalPredicate.Invariant J α (.upper c b .eventually I φ))
    (hφ : predicateSatisfies σ J α (.plain φ)) :
    predicateSatisfies σ J α (.upper c b .eventually I φ) := by
  intro t ht
  apply current_witness σ J α c b I φ hne hD hi.1 hφ t ht.1
  rw [hz, add_zero]
  exact ht.2

private theorem exists_marker_iff (p : Marker → Prop) : (∃ m, p m) ↔ p ○ ∨ p ● := by
  constructor
  · rintro ⟨m, h⟩; cases m; exact Or.inl h; exact Or.inr h
  · rintro (h | h); exact ⟨○, h⟩; exact ⟨●, h⟩

theorem openEventually_correct_at [DecidableEq Clock] (c : Clock)
    (I : BoundedTimeInterval) (φ : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) :
    ((σ, P, α, k)⊨ₚ((openEventually c I φ).source : Judgement Clock Var)) ↔
      branchSatisfied (openEventually c I φ) σ P α k := by
  change ((σ, P, α, k)⊨ₚ
    ((IntervalPredicate.plain (◇[(I : TimeInterval)] φ) :
      IntervalPredicate Clock Var) : Judgement Clock Var)) ↔ _
  rw [satisfies_plain_eventually_iff_reset_upper σ P α k c I φ]
  rw [exists_marker_iff]
  simp [branchSatisfied, openEventually]


theorem openAlways_correct_at [DecidableEq Clock] (c : Clock)
    (I : BoundedTimeInterval) (φ : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) :
    ((σ, P, α, k)⊨ₚ((openAlways c I φ).source : Judgement Clock Var)) ↔
      branchSatisfied (openAlways c I φ) σ P α k := by
  change ((σ, P, α, k)⊨ₚ
    ((IntervalPredicate.plain (□[(I : TimeInterval)] φ) :
      IntervalPredicate Clock Var) : Judgement Clock Var)) ↔ _
  rw [satisfies_plain_always_iff_reset_upper σ P α k c I φ]
  rw [exists_marker_iff]
  simp [branchSatisfied, openAlways]


theorem boundedEventually_defer_sound (c d : Clock) (b q m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) :
    boundedEventually_defer c d b q m I φ ⇒ₚ
      ((↑↓[c, d, b, q]◇[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  intro σ P α k h
  apply next_bounded_implies_bounded c d b q .eventually I φ σ P α k
  by_cases hk : k.1 < P.size
  · simp only [boundedEventually_defer, satisfies, dif_pos hk] at h ⊢
    exact h.2.2
  · simp [boundedEventually_defer, satisfies, hk] at h

/-- Finish soundness at consecutive intervals, using the predicate invariant
to obtain witnesses in the current piece. No stability or freshness is needed. -/
theorem boundedEventually_finish_sound_at_next
    (c d : Clock) (b q m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size)
    (hinv : IntervalPredicate.Invariant (P.interval ⟨k.1, by omega⟩) α (↑↓[c, d, b, q]◇[I]φ))
    (h : (σ, P, α, k)⊨ₚ(boundedEventually_finish d q m I φ)) :
    (σ, P, α, k)⊨ₚ((↑↓[c, d, b, q]◇[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let j : Fin P.size := ⟨k.1 + 1, hn⟩
  let γ := ClockResetSet.elapse α (Judgement.duration P i)
  simp only [boundedEventually_finish, satisfies, dif_pos hk, dif_pos hn] at h ⊢
  have hmarker : (P.interval j).leftBoundary = m := h.2.2
  have hm : (P.interval i).rightBoundary = ¬ₘ m :=
    (P.adjacent_rightBoundary_eq_complement_leftBoundary i hn).trans
      (congrArg Marker.complement hmarker)
  have hg : I.lower <[Marker.notConj q m] (γ d : ℝ) :=
    (satisfies_markedGT σ P γ ⟨k.1 + 1, by omega⟩ d
      (Marker.notConj q m) ⟨I.lower, I.lower_nonnegative⟩).1 h.2.1
  have hguard : I.lower <[Marker.imp q (P.interval i).rightBoundary]
      ((α d : ℝ) + ((P.interval i).right - (P.interval i).left)) := by
    rw [hm]
    have heq : Marker.imp q (¬ₘ m) = Marker.notConj q m := by
      cases q <;> cases m <;> rfl
    rw [heq]
    exact hg
  have hDomain : (P.interval i).carrier ⊆ σ.domain := by
    intro t ht
    rw [← P.covers]
    exact Set.mem_iUnion.2 ⟨i, ht⟩
  exact bounded_plain_finish
    σ (P.interval i) α c d b q I φ (P.nonempty i) hDomain hinv hguard h.1

/-- At the last interval the next marker is closed, and the current right
marker is open; the same witness-intersection argument still applies. -/
theorem boundedEventually_finish_sound_at_last
    (c d : Clock) (b q m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hlast : k.1 + 1 = P.size)
    (hinv : IntervalPredicate.Invariant (P.interval ⟨k.1, by omega⟩) α (↑↓[c, d, b, q]◇[I]φ))
    (h : (σ, P, α, k)⊨ₚ(boundedEventually_finish d q m I φ)) :
    (σ, P, α, k)⊨ₚ((↑↓[c, d, b, q]◇[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  have hk : k.1 < P.size := by omega
  have hn : ¬k.1 + 1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let γ := ClockResetSet.elapse α (Judgement.duration P i)
  simp only [boundedEventually_finish, satisfies, dif_pos hk, dif_neg hn] at h ⊢
  have hmarker : m = ● := h.2.2
  have hg : I.lower <[Marker.notConj q m] (γ d : ℝ) :=
    (satisfies_markedGT σ P γ ⟨k.1 + 1, by omega⟩ d
      (Marker.notConj q m) ⟨I.lower, I.lower_nonnegative⟩).1 h.2.1
  have hguard : I.lower <[Marker.imp q (P.interval i).rightBoundary]
      ((α d : ℝ) + ((P.interval i).right - (P.interval i).left)) := by
    rw [P.rightBoundary_last i hlast]
    rw [hmarker] at hg
    cases q <;> exact hg
  have hDomain : (P.interval i).carrier ⊆ σ.domain := by
    intro t ht
    rw [← P.covers]
    exact Set.mem_iUnion.2 ⟨i, ht⟩
  exact bounded_plain_finish
    σ (P.interval i) α c d b q I φ (P.nonempty i) hDomain hinv hguard h.1

/-- Finish soundness at every position under the eventuality invariant.
No stability or clock-distinctness assumption is required. -/
theorem boundedEventually_finish_sound_at
    (c d : Clock) (b q m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hinv : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α (↑↓[c, d, b, q]◇[I]φ))
    (h : (σ, P, α, k)⊨ₚ(boundedEventually_finish d q m I φ)) :
    (σ, P, α, k)⊨ₚ((↑↓[c, d, b, q]◇[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · exact boundedEventually_finish_sound_at_next c d b q m I φ σ P α k hn (hinv hk) h
    · exact boundedEventually_finish_sound_at_last c d b q m I φ σ P α k (by omega) (hinv hk) h
  · simp [boundedEventually_finish, satisfies, hk] at h

/-- Check/reset soundness splits the scope into current-witness points and
points retained by the reset predicate. The invariant supplies current
witnesses; clock freshness preserves the remaining scope's right endpoint. -/
theorem boundedEventually_check_sound_at [DecidableEq Clock]
    (c d : Clock) (b q m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hinv : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α (↑↓[c, d, b, q]◇[I]φ))
    (h : (σ, P, α, k)⊨ₚ(boundedEventually_check c d b q m I φ)) :
    (σ, P, α, k)⊨ₚ((↑↓[c, d, b, q]◇[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · let i : Fin P.size := ⟨k.1, hk⟩
      let j : Fin P.size := ⟨k.1 + 1, hn⟩
      let a : NNReal := ⟨I.lower, I.lower_nonnegative⟩
      let γ := ClockResetSet.elapse α (Judgement.duration P i)
      let β := (⟦c ↦ᶜ a⟧).apply γ
      have hβc : β c = a := ClockResetSet.apply_singleton_self c a γ
      have hβd : β d = γ d := ClockResetSet.apply_singleton_of_ne a γ hcd.symm
      have hd : (P.interval i).left - (α d : ℝ) =
          (P.interval j).left - (β d : ℝ) := by
        rw [hβd]
        exact (Judgement.next_left_sub_elapse_eq P α i hn d).symm
      have hadj : (P.interval i).right = (P.interval j).left := P.adjacent_right_eq_left i hn
      simp only [boundedEventually_check, satisfies, dif_pos hk, dif_pos hn] at h ⊢
      have hmarker : (P.interval j).leftBoundary = m := h.2.2.2.2
      have hm : (P.interval i).rightBoundary = ¬ₘ m :=
        (P.adjacent_rightBoundary_eq_complement_leftBoundary i hn).trans
          (congrArg Marker.complement hmarker)
      have hnext : (σ, P.interval j, β)⊨ₚᵢ(↑↓[c, d, m, q]◇[I]φ) := h.2.2.2.1
      have hDomain : (P.interval i).carrier ⊆ σ.domain := by
        intro t ht
        rw [← P.covers]
        exact Set.mem_iUnion.2 ⟨i, ht⟩
      intro t ht
      by_cases hcut : t + I.lower <[(P.interval i).rightBoundary] (P.interval i).right
      · exact bounded_current_witness
          σ (P.interval i) α c d b q I φ (P.nonempty i) hDomain (hinv hk) h.1 t ht hcut
      · have htNext : t ∈ IntervalPredicate.scope (P.interval j) β (↑↓[c, d, m, q]◇[I]φ) := by
          constructor
          · change ((P.interval j).left - (β c : ℝ)) <[m] t
            rw [hβc, ← hadj]
            apply (Judgement.not_markedLT_add_complement_iff t I.lower _ m).1
            simpa only [hm] using hcut
          · change t < (P.interval j).left - (β d : ℝ) ∨
              (t = (P.interval j).left - (β d : ℝ) ∧ q.Includes)
            rw [← hd]
            exact ht.2
        obtain ⟨u, hu, hφ⟩ := hnext t htNext
        exact ⟨u, hu, hφ⟩
    · simp [boundedEventually_check, satisfies, hk, hn] at h
  · simp [boundedEventually_check, satisfies, hk] at h

/-- Soundness of all three `↑↓` `◇` schemas (six concrete
branches), under the source invariant and reset-clock freshness. -/
theorem boundedEventually_sound_at [DecidableEq Clock]
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hinv : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α (↑↓[c, d, b, q]◇[I]φ))
    (h : branchSatisfied (boundedEventually c d b q I φ) σ P α k) :
    (σ, P, α, k)⊨ₚ((boundedEventually c d b q I φ).source : Judgement Clock Var) := by
  obtain ⟨B, hB, h⟩ := h
  simp only [boundedEventually, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl
  · exact boundedEventually_defer_sound c d b q ○ I φ σ P α k h
  · exact boundedEventually_defer_sound c d b q ● I φ σ P α k h
  · exact boundedEventually_finish_sound_at c d b q ○ I φ σ P α k hinv h
  · exact boundedEventually_finish_sound_at c d b q ● I φ σ P α k hinv h
  · exact boundedEventually_check_sound_at c d b q ○ I φ hcd σ P α k hinv h
  · exact boundedEventually_check_sound_at c d b q ● I φ hcd σ P α k hinv h


theorem upperEventually_defer_sound [DecidableEq Clock]
    (c d : Clock) (b m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) : upperEventually_defer c d b m I φ ⇒ₚ
      ((↑[c, b]◇[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  intro σ P α k h
  apply next_reset_bounded_implies_upper c d b m .eventually I φ hcd σ P α k
  by_cases hk : k.1 < P.size
  · simp only [upperEventually_defer, satisfies, dif_pos hk] at h ⊢
    exact h.2
  · simp [upperEventually_defer, satisfies, hk] at h

/-- Soundness of the zero-lower-bound branch `[φ]` under the source
invariant, without stability or distinct-clock assumptions. -/
theorem upperEventually_plain_sound_at
    (c : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hzero : I.lower = 0) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hinv : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α (↑[c, b]◇[I]φ))
    (h : (σ, P, α, k)⊨ₚ(Judgement.predicate (.plain φ))) :
    (σ, P, α, k)⊨ₚ((↑[c, b]◇[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  by_cases hk : k.1 < P.size
  · let i : Fin P.size := ⟨k.1, hk⟩
    have hDomain : (P.interval i).carrier ⊆ σ.domain := by
      intro t ht
      rw [← P.covers]
      exact Set.mem_iUnion.2 ⟨i, ht⟩
    simp only [satisfies, dif_pos hk] at h ⊢
    exact upper_plain_zero
      σ (P.interval i) α c b I φ (P.nonempty i) hDomain hzero (hinv hk) h
  · simp [satisfies, hk] at h

/-- `↑` `◇` check/reset soundness. The current-witness argument
and the reset continuation cover complementary parts of the source scope. -/
theorem upperEventually_check_sound_at [DecidableEq Clock]
    (c d : Clock) (b m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hinv : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α (↑[c, b]◇[I]φ))
    (h : (σ, P, α, k)⊨ₚ(upperEventually_check c d b m I φ)) :
    (σ, P, α, k)⊨ₚ((↑[c, b]◇[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · let i : Fin P.size := ⟨k.1, hk⟩
      let j : Fin P.size := ⟨k.1 + 1, hn⟩
      let a : NNReal := ⟨I.lower, I.lower_nonnegative⟩
      let γ := ClockResetSet.elapse α (Judgement.duration P i)
      let β := ((⟦c ↦ᶜ a⟧).union ⟦d ↦ᶜ 0⟧).apply γ
      have hβc : β c = a := by
        simp [β, ClockResetSet.apply, ClockResetSet.union, ClockResetSet.singleton]
      have hβd : β d = 0 := by
        change ((⟦c ↦ᶜ a⟧).union ⟦d ↦ᶜ 0⟧).apply γ d = 0
        rw [ClockResetSet.apply_union_eq_right_of_not_mem _ _ γ (by simp [Ne.symm hcd])]
        exact ClockResetSet.apply_singleton_self d 0 γ
      have hadj : (P.interval i).right = (P.interval j).left := P.adjacent_right_eq_left i hn
      simp only [upperEventually_check, satisfies, dif_pos hk, dif_pos hn] at h ⊢
      have hmarker : (P.interval j).leftBoundary = m := h.2.2.2
      have hm : (P.interval i).rightBoundary = ¬ₘ m :=
        (P.adjacent_rightBoundary_eq_complement_leftBoundary i hn).trans
          (congrArg Marker.complement hmarker)
      have hnext : (σ, P.interval j, β)⊨ₚᵢ(↑↓[c, d, m, ¬ₘ m]◇[I]φ) := h.2.2.1
      have hDomain : (P.interval i).carrier ⊆ σ.domain := by
        intro t ht
        rw [← P.covers]
        exact Set.mem_iUnion.2 ⟨i, ht⟩
      intro t ht
      by_cases hcut : t + I.lower <[(P.interval i).rightBoundary] (P.interval i).right
      · exact current_witness
          σ (P.interval i) α c b I φ (P.nonempty i) hDomain (hinv hk).1 h.1 t ht.1 hcut
      · have htNext : t ∈ IntervalPredicate.scope (P.interval j) β (↑↓[c, d, m, ¬ₘ m]◇[I]φ) := by
          constructor
          · change ((P.interval j).left - (β c : ℝ)) <[m] t
            rw [hβc, ← hadj]
            apply (Judgement.not_markedLT_add_complement_iff t I.lower _ m).1
            simpa only [hm] using hcut
          · change t < (P.interval j).left - (β d : ℝ) ∨
              (t = (P.interval j).left - (β d : ℝ) ∧ (¬ₘ m).Includes)
            rw [hβd, NNReal.coe_zero, sub_zero, ← hadj, ← hm]
            exact ht.2
        obtain ⟨u, hu, hφ⟩ := hnext t htNext
        exact ⟨u, hu, hφ⟩
    · simp [upperEventually_check, satisfies, hk, hn] at h
  · simp [upperEventually_check, satisfies, hk] at h

/-- Soundness of every `↑` `◇` branch, with numerical side
conditions enforced by the branch list. Stability is unnecessary. -/
theorem upperEventually_sound_at [DecidableEq Clock]
    (c d : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hinv : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α (↑[c, b]◇[I]φ))
    (h : branchSatisfied (upperEventually c d b I φ) σ P α k) :
    (σ, P, α, k)⊨ₚ((upperEventually c d b I φ).source : Judgement Clock Var) := by
  classical
  obtain ⟨B, hB, h⟩ := h
  by_cases hz : I.lower = 0
  · simp only [upperEventually, if_pos hz, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hB
    rcases hB with rfl | rfl | rfl
    · exact upperEventually_defer_sound c d b ○ I φ hcd σ P α k h
    · exact upperEventually_defer_sound c d b ● I φ hcd σ P α k h
    · exact upperEventually_plain_sound_at c b I φ hz σ P α k hinv h
  · simp only [upperEventually, if_neg hz, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hB
    rcases hB with rfl | rfl | rfl | rfl
    · exact upperEventually_defer_sound c d b ○ I φ hcd σ P α k h
    · exact upperEventually_defer_sound c d b ● I φ hcd σ P α k h
    · exact upperEventually_check_sound_at c d b ○ I φ hcd σ P α k hinv h
    · exact upperEventually_check_sound_at c d b ● I φ hcd σ P α k hinv h


end STLTableau
