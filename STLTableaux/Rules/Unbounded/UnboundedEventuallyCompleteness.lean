import STLTableaux.Rules.Unbounded.UnboundedClockedRules

namespace STLTableau.UnboundedClocked
open scoped STL
variable {Clock Var : Type*}

/-- At the last piece the original invariant excludes past witnesses.
Operand stability therefore yields the literal finish branch. -/
theorem boundedEventually_complete_last
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c d : Clock) (b q : Marker) (a : NNReal) (φ : Formula Var)
    (hlast : k.1 + 1 = P.size)
    (hi : Invariant σ P α k (by omega) (.bounded c d b q .eventually a φ))
    (hst : ∀ j, σ.Stable (P.interval j) φ)
    (hs : Node.holds σ P α k (.predicate (.bounded c d b q .eventually a φ))) :
    Node.holds σ P α k (boundedEventuallyFinish d q ● a φ) := by
  have hk : k.1 < P.size := by omega
  have hn : ¬ k.1 + 1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let J := P.interval i
  let S := (scope J α (.bounded c d b q .eventually a φ)).toMarkedInterval
  let γ := ClockResetSet.elapse α (Judgement.duration P i)
  have hSne : S.carrier.Nonempty := by
    apply (MarkedInterval.nonempty_iff S).2
    rcases hi.1 with h | ⟨h, hm⟩
    · left; dsimp [S, scope, Scope.toMarkedInterval]; linarith
    · right
      exact ⟨by dsimp [S, scope, Scope.toMarkedInterval]; linarith, hm⟩
  have hU : ∀ t : ℝ, t ∈ S →
      ∃ u : σ.Time, (a : ℝ) ≤ u.1 - t ∧ (σ,u)⊨φ := by
    simpa [Node.holds, hk, satisfies, temporalSatisfies, S, J, i] using hs
  have hcover := STLTableau.eventually_stable_scope_cover σ P S.carrier (.unbounded a) φ hst hU
  obtain ⟨t, ht⟩ := hSne
  obtain ⟨j, u, huPiece, hu, htrue⟩ := hcover t ht
  have huSuffix := witness_in_suffix σ P α k hk c b a φ hst hi.2 t ht.1 u hu (htrue u huPiece)
  have huJ := P.mem_last_of_left_condition i hlast u.2 huSuffix
  have he : j = i := P.eq_of_shared_point huPiece huJ
  have hφ : ∀ v : σ.Time, v.1 ∈ J → (σ,v)⊨φ := by
    simpa only [he] using htrue
  let K : MarkedInterval := ⟨S.left, J.right - (a : ℝ), b, ○⟩
  have hsub : S.carrier ⊆ K.carrier := by
    intro t ht
    obtain ⟨j, u, huPiece, hu, htrue⟩ := hcover t ht
    change (a : ℝ) ≤ u.1 - t at hu
    have huSuffix := witness_in_suffix σ P α k hk c b a φ hst hi.2 t ht.1 u hu (htrue u huPiece)
    have hur := P.lt_right_of_mem_last i hlast
      (P.mem_last_of_left_condition i hlast u.2 huSuffix)
    exact ⟨ht.1, Or.inl (by change t < J.right - (a : ℝ); linarith)⟩
  have hr := ((MarkedInterval.subset_iff (show S.carrier.Nonempty from
    ⟨t, ht⟩)).1 hsub).2
  have hg : (a : ℝ) <[Marker.notConj q ●] (γ d : ℝ) := by
    change J.left - (α d : ℝ) <[Marker.imp q ○] (J.right - (a : ℝ)) at hr
    change (a : ℝ) <[Marker.notConj q ●] ((α d : ℝ) + (J.right - J.left))
    have hm : Marker.imp q ○ = Marker.notConj q ● := by cases q <;> rfl
    rw [hm] at hr
    rcases hr with h | ⟨h, hm⟩
    · left; linarith
    · right; exact ⟨by linarith, hm⟩
  simp only [boundedEventuallyFinish, Node.holds, dif_pos hk, dif_neg hn]
  exact ⟨hφ, (Node.holds_gt σ P γ _ d _ a).2 hg, trivial⟩

/-- Literal unbounded `↑↓` `◇` completeness. At nonterminal
successors the exact frozen scope already supplies a defer branch. -/
theorem boundedEventually_complete [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c d : Clock) (b q : Marker) (a : NNReal) (φ : Formula Var)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk (.bounded c d b q .eventually a φ))
    (hst : ∀ j, σ.Stable (P.interval j) φ)
    (hs : Node.holds σ P α k (.predicate (.bounded c d b q .eventually a φ))) :
    ∃ B ∈ boundedEventuallyBranches c d b q a φ, Node.holds σ P α k B := by
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · let m := (P.interval ⟨k.1 + 1, hn⟩).leftBoundary
      refine ⟨boundedEventuallyDefer c d b q m a φ, ?_, ?_⟩
      · cases m <;> simp [boundedEventuallyBranches]
      · simp only [boundedEventuallyDefer, Node.holds, dif_pos hk, dif_pos hn]
        refine ⟨rfl, ?_⟩
        apply (bounded_transport σ _ _ α _ c d b q .eventually a φ
          (Judgement.next_left_sub_elapse_eq P α ⟨k.1, hk⟩ hn c).symm
          (Judgement.next_left_sub_elapse_eq P α ⟨k.1, hk⟩ hn d).symm).1
        simpa only [Node.holds, dif_pos hk] using hs
    · refine ⟨boundedEventuallyFinish d q ● a φ, by simp [boundedEventuallyBranches], ?_⟩
      exact boundedEventually_complete_last σ P α k c d b q a φ (by omega) (hi hk) hst hs
  · simp [Node.holds, hk] at hs

/-- A last-piece `↑` `◇` can only have zero lower delay: its
scope approaches the signal horizon. Every witness is then current. -/
theorem upperEventually_complete_last
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c : Clock) (b : Marker) (a : NNReal) (φ : Formula Var)
    (hlast : k.1 + 1 = P.size)
    (hi : Invariant σ P α k (by omega) (.upper c b .eventually a φ))
    (hst : ∀ j, σ.Stable (P.interval j) φ)
    (hs : Node.holds σ P α k (.predicate (.upper c b .eventually a φ))) :
    a = 0 ∧ Node.holds σ P α k (.plain φ) := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let J := P.interval i
  let S := (scope J α (.upper c b .eventually a φ)).toMarkedInterval
  have hSne : S.carrier.Nonempty := by
    apply (MarkedInterval.nonempty_iff S).2
    rcases hi.1 with h | ⟨h, hm⟩
    · left; dsimp [S, scope, Scope.toMarkedInterval]; linarith
    · right
      exact ⟨by dsimp [S, scope, Scope.toMarkedInterval]; linarith, hm⟩
  have hU : ∀ t : ℝ, t ∈ S →
      ∃ u : σ.Time, (a : ℝ) ≤ u.1 - t ∧ (σ,u)⊨φ := by
    simpa [Node.holds, hk, satisfies, temporalSatisfies, S, J, i] using hs
  have hcover := STLTableau.eventually_stable_scope_cover σ P S.carrier (.unbounded a) φ hst hU
  obtain ⟨t, ht⟩ := hSne
  obtain ⟨j, u, huPiece, hu, htrue⟩ := hcover t ht
  have huSuffix := witness_in_suffix σ P α k hk c b a φ hst hi.2 t ht.1 u hu (htrue u huPiece)
  have huJ := P.mem_last_of_left_condition i hlast u.2 huSuffix
  have he : j = i := P.eq_of_shared_point huPiece huJ
  have hφ : Node.holds σ P α k (.plain φ) := by
    simp only [Node.holds, dif_pos hk]
    simpa only [he] using htrue
  let K : MarkedInterval := ⟨S.left, J.right - (a : ℝ), b, ○⟩
  have hsub : S.carrier ⊆ K.carrier := by
    intro t ht
    obtain ⟨j, u, huPiece, hu, htrue⟩ := hcover t ht
    change (a : ℝ) ≤ u.1 - t at hu
    have huSuffix := witness_in_suffix σ P α k hk c b a φ hst hi.2 t ht.1 u hu (htrue u huPiece)
    have hur := P.lt_right_of_mem_last i hlast
      (P.mem_last_of_left_condition i hlast u.2 huSuffix)
    exact ⟨ht.1, Or.inl (by change t < J.right - (a : ℝ); linarith)⟩
  have hr := ((MarkedInterval.subset_iff (show S.carrier.Nonempty from
    ⟨t, ht⟩)).1 hsub).2
  change J.right <[Marker.imp J.rightBoundary ○] (J.right - (a : ℝ)) at hr
  have ha : (a : ℝ) = 0 := by
    rcases hr with h | ⟨h, _⟩ <;> linarith [a.coe_nonneg]
  exact ⟨Subtype.ext ha, hφ⟩

/-- Literal `↑` `◇` completeness, including the zero-delay
branch `[φ]` at the last interval. -/
theorem upperEventually_complete [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c d : Clock) (b : Marker) (a : NNReal) (φ : Formula Var) (hcd : c ≠ d)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk (.upper c b .eventually a φ))
    (hst : ∀ j, σ.Stable (P.interval j) φ)
    (hs : Node.holds σ P α k (.predicate (.upper c b .eventually a φ))) :
    ∃ B ∈ upperEventuallyBranches c d b a φ, Node.holds σ P α k B := by
  classical
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · let m := (P.interval ⟨k.1 + 1, hn⟩).leftBoundary
      refine ⟨upperEventuallyDefer c d b m a φ, ?_, ?_⟩
      · cases m <;> simp [upperEventuallyBranches]
      · simp only [upperEventuallyDefer, Node.holds, dif_pos hk, dif_pos hn]
        refine ⟨?_, rfl⟩
        apply (upper_frozen_transport σ P α k hn c d b m .eventually a φ hcd rfl).1
        simpa only [Node.holds, dif_pos hk] using hs
    · obtain ⟨hz, hφ⟩ := upperEventually_complete_last σ P α k c b a φ
        (by omega) (hi hk) hst hs
      exact ⟨.plain φ, by simp [upperEventuallyBranches, hz], hφ⟩
  · simp [Node.holds, hk] at hs

end STLTableau.UnboundedClocked
