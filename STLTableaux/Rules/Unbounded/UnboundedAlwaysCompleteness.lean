import STLTableaux.Rules.Unbounded.UnboundedClockedRules

namespace STLTableau.UnboundedClocked
open scoped STL
open STLTableau.IntervalPredicate
variable {Clock Var : Type*}

private theorem plain_of_ray_overlap (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (hk : k.1 < P.size)
    (c : Clock) (b : Marker) (a : NNReal) (φ : Formula Var)
    (hst : σ.Stable (P.interval ⟨k.1,hk⟩) φ)
    (hs : satisfies σ (P.interval ⟨k.1,hk⟩) α (.upper c b .always a φ))
    (hcut : (P.interval ⟨k.1,hk⟩).left - (α c : ℝ) + (a : ℝ)
      <[Marker.conj b (P.interval ⟨k.1,hk⟩).rightBoundary]
        (P.interval ⟨k.1,hk⟩).right) :
    ∀ t : σ.Time, t.1 ∈ P.interval ⟨k.1,hk⟩ → (σ,t)⊨φ := by
  let J := P.interval ⟨k.1,hk⟩
  let I := cappedInterval σ J α c c a
  have hf := (upper_iff_capped σ J α c b .always a φ (P.left_le_right _)).1 hs
  have hr : IntervalPredicate.Satisfies σ J α (.upper c b .always I φ) := by
    intro t ht _
    exact hf t ht
  have hD : J.carrier ⊆ σ.domain := by
    intro t ht
    rw [← P.covers]
    exact Set.mem_iUnion.2 ⟨⟨k.1,hk⟩, ht⟩
  have hφ := IntervalPredicate.satisfies_plain_of_upper_always_of_marked_overlap
    σ J α c b I φ (P.nonempty _) hD hcut hst hr
  exact hφ

private theorem future_ray (σ : FiniteSignal Var) (J K : MarkedInterval)
    (α β : ClockValuation Clock) (c : Clock) (b m : Marker) (a : NNReal) (φ : Formula Var)
    (hc : (β c : ℝ) = (a : ℝ)) (hadj : J.right = K.left)
    (hcut : J.left - (α c : ℝ) + (a : ℝ) <[Marker.conj b J.rightBoundary] J.right)
    (hs : satisfies σ J α (.upper c b .always a φ)) :
    ∀ t : σ.Time, K.left - (β c : ℝ) + (a : ℝ) <[m] t.1 → (σ,t)⊨φ := by
  intro t ht
  have htl : K.left ≤ t.1 := by
    rw [hc, sub_add_cancel] at ht
    exact ht.elim le_of_lt (fun h => h.1.le)
  apply hs t
  change J.left - (α c : ℝ) + (a : ℝ) <[b] t.1
  rcases hcut with hcut | ⟨he, hb⟩
  · left
    rw [hadj] at hcut
    exact hcut.trans_le htl
  · have hle : J.left - (α c : ℝ) + (a : ℝ) ≤ t.1 := by
      rw [he, hadj]
      exact htl
    rcases hle.lt_or_eq with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, ((Marker.includes_conj _ _).1 hb).1⟩

/-- Literal `↑` `□` completeness for `[a,∞)`. Only operand stability
is needed in addition to the satisfied source; no finite timing restriction. -/
theorem upperAlways_complete [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c d : Clock) (b : Marker) (a : NNReal) (φ : Formula Var) (hcd : c ≠ d)
    (hst : ∀ j, σ.Stable (P.interval j) φ)
    (hs : Node.holds σ P α k (.predicate (.upper c b .always a φ))) :
    ∃ B ∈ upperAlwaysBranches c d b a φ, Node.holds σ P α k B := by
  by_cases hk : k.1 < P.size
  · let i : Fin P.size := ⟨k.1,hk⟩
    let γ := ClockResetSet.elapse α (Judgement.duration P i)
    have hsrc : satisfies σ (P.interval i) α (.upper c b .always a φ) := by
      simpa only [Node.holds, dif_pos hk] using hs
    by_cases hn : k.1 + 1 < P.size
    · let j : Fin P.size := ⟨k.1+1,hn⟩
      let m := (P.interval j).leftBoundary
      by_cases hg : (γ c : ℝ) <[Marker.imp b m] (a : ℝ)
      · refine ⟨upperAlwaysDefer c d b m a φ, ?_, ?_⟩
        · cases m <;> simp [upperAlwaysBranches]
        · simp only [upperAlwaysDefer, Node.holds, dif_pos hk, dif_pos hn]
          refine ⟨(Node.holds_lt σ P γ _ c _ a).2 hg, ?_, rfl⟩
          exact (upper_frozen_transport σ P α k hn c d b m .always a φ hcd rfl).1 hsrc
      · have hg' : (a : ℝ) <[Marker.conj b (¬ₘ m)] (γ c : ℝ) :=
          by
            by_contra hnot
            exact hg ((Judgement.upperAlways_guard_complement _ _ _ _).2 hnot)
        have hcut : (P.interval i).left - (α c : ℝ) + (a : ℝ)
            <[Marker.conj b (P.interval i).rightBoundary] (P.interval i).right := by
          have hm := P.adjacent_rightBoundary_eq_complement_leftBoundary i hn
          change (P.interval i).left - (α c : ℝ) + (a : ℝ)
            <[Marker.conj b (P.interval i).rightBoundary] (P.interval i).right
          rw [hm]
          change (a : ℝ) <[Marker.conj b (¬ₘ m)]
            ((α c : ℝ) + ((P.interval i).right - (P.interval i).left)) at hg'
          rcases hg' with h | ⟨h, hm⟩
          · left; linarith
          · right; exact ⟨by linarith, hm⟩
        have hφ := plain_of_ray_overlap σ P α k hk c b a φ (hst i) hsrc hcut
        let β := ((ClockResetSet.singleton c a).union (ClockResetSet.singleton d 0)).apply γ
        have hβc : (β c : ℝ) = (a : ℝ) := by simp [β, ClockResetSet.apply,
          ClockResetSet.union, ClockResetSet.singleton]
        have hf := future_ray σ (P.interval i) (P.interval j) α β c b m a φ hβc
          (P.adjacent_right_eq_left i hn) hcut hsrc
        refine ⟨upperAlwaysCheck c d b m a φ, ?_, ?_⟩
        · cases m <;> simp [upperAlwaysBranches]
        · simp only [upperAlwaysCheck, Node.holds, dif_pos hk, dif_pos hn]
          exact ⟨hφ, (Node.holds_gt σ P γ _ c _ a).2 hg', hf, rfl⟩
    · have hlast : k.1+1 = P.size := by omega
      by_cases hg : γ c ≤ a
      · refine ⟨alwaysWait c a, by simp [upperAlwaysBranches], ?_⟩
        simp only [alwaysWait, Node.holds, dif_pos hk]
        exact ⟨hg, hlast⟩
      · have hgt : a < γ c := lt_of_not_ge hg
        have hcut : (P.interval i).left - (α c : ℝ) + (a : ℝ)
            <[Marker.conj b (P.interval i).rightBoundary] (P.interval i).right := by
          left
          have hgR : (a : ℝ) < (α c : ℝ) +
              ((P.interval i).right - (P.interval i).left) := hgt
          linarith
        have hφ := plain_of_ray_overlap σ P α k hk c b a φ (hst i) hsrc hcut
        refine ⟨alwaysLast c a φ, by simp [upperAlwaysBranches], ?_⟩
        simp only [alwaysLast, Node.holds, dif_pos hk]
        exact ⟨hφ, hgt, hlast⟩
  · simp [Node.holds, hk] at hs

private theorem defer_to_bounded [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c d : Clock) (b q m : Marker) (a : NNReal) (φ : Formula Var) (hcd : c ≠ d) :
    Node.holds σ P α k (upperAlwaysDefer c d b m a φ) →
      Node.holds σ P α k (boundedAlwaysDefer c d b q m a φ) := by
  intro h
  by_cases hk : k.1 < P.size <;> by_cases hn : k.1 + 1 < P.size <;>
    simp_all [upperAlwaysDefer, boundedAlwaysDefer, Node.holds,
      satisfies, temporalSatisfies, scope, ClockResetSet.apply, ClockResetSet.singleton,
      Ne.symm hcd] <;> aesop

private theorem check_to_bounded [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c d : Clock) (b q m : Marker) (a : NNReal) (φ : Formula Var) :
    Node.holds σ P α k (upperAlwaysCheck c d b m a φ) →
      Node.holds σ P α k (boundedAlwaysCheck c d b q m a φ) := by
  intro h
  by_cases hk : k.1 < P.size <;> by_cases hn : k.1 + 1 < P.size <;>
    simp_all [upperAlwaysCheck, boundedAlwaysCheck, Node.holds,
      satisfies, temporalSatisfies, scope, ClockResetSet.apply, ClockResetSet.singleton,
      ClockResetSet.union]

/-- `↑↓` scope always has the same unbounded checking ray as `↑` `□`.
The retained branch keeps the original right clock; no semantic change to
the literal bounded rule is made. -/
theorem boundedAlways_complete [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c d : Clock) (b q : Marker) (a : NNReal) (φ : Formula Var) (hcd : c ≠ d)
    (hst : ∀ j, σ.Stable (P.interval j) φ)
    (hs : Node.holds σ P α k (.predicate (.bounded c d b q .always a φ))) :
    ∃ B ∈ boundedAlwaysBranches c d b q a φ, Node.holds σ P α k B := by
  have hu : Node.holds σ P α k (.predicate (.upper c b .always a φ)) := by
    by_cases hk : k.1 < P.size
    · simpa only [Node.holds, dif_pos hk, satisfies, temporalSatisfies, scope] using hs
    · simp [Node.holds, hk] at hs
  obtain ⟨B, hm, hB⟩ := upperAlways_complete σ P α k c d b a φ hcd hst hu
  simp only [upperAlwaysBranches, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [boundedAlwaysBranches], defer_to_bounded σ P α k c d b q ○ a φ hcd hB⟩
  · exact ⟨_, by simp [boundedAlwaysBranches], defer_to_bounded σ P α k c d b q ● a φ hcd hB⟩
  · exact ⟨_, by simp [boundedAlwaysBranches], hB⟩
  · exact ⟨_, by simp [boundedAlwaysBranches], hB⟩
  · exact ⟨_, by simp [boundedAlwaysBranches], check_to_bounded σ P α k c d b q ○ a φ hB⟩
  · exact ⟨_, by simp [boundedAlwaysBranches], check_to_bounded σ P α k c d b q ● a φ hB⟩

end STLTableau.UnboundedClocked
