import STLTableaux.Rules.Unbounded.UnboundedClockedRules

namespace STLTableau.UnboundedClocked
open scoped STL
variable {Clock Var : Type*}

/-- The literal selected `↑` `◇` check branch is satisfied when
its current and guard obligations hold. Unbounded witnesses retain their
original values because the remaining raw scope is a subset of the source. -/
theorem upper_check_witness [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (hn : k.1 + 1 < P.size)
    (c d : Clock) (b : Marker) (a : NNReal) (φ : Formula Var) (hcd : c ≠ d)
    (hg : (a : ℝ) <[Marker.conj b (¬ₘ (P.interval ⟨k.1 + 1, hn⟩).leftBoundary)]
      (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩) c : ℝ))
    (hplain : Node.holds σ P α k (.plain φ))
    (hsource : Node.holds σ P α k (.predicate (.upper c b .eventually a φ))) :
    Node.holds σ P α k
      (upperEventuallyCheck c d b (P.interval ⟨k.1 + 1, hn⟩).leftBoundary a φ) := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let j : Fin P.size := ⟨k.1 + 1, hn⟩
  let m := (P.interval j).leftBoundary
  let γ := ClockResetSet.elapse α (Judgement.duration P i)
  let β := ((ClockResetSet.singleton c a).union (ClockResetSet.singleton d 0)).apply γ
  have hβc : β c = a := by
    simp [β, ClockResetSet.apply, ClockResetSet.union, ClockResetSet.singleton]
  have hβd : β d = 0 := by
    change ((ClockResetSet.singleton c a).union (ClockResetSet.singleton d 0)).apply γ d = 0
    rw [ClockResetSet.apply_union_eq_right_of_not_mem _ _ γ (by simp [Ne.symm hcd])]
    exact ClockResetSet.apply_singleton_self d 0 γ
  have hc : (P.interval j).left - (γ c : ℝ) = (P.interval i).left - (α c : ℝ) :=
    Judgement.next_left_sub_elapse_eq P α i hn c
  have hadj := P.adjacent_right_eq_left i hn
  have hm := P.adjacent_rightBoundary_eq_complement_leftBoundary i hn
  have hU : satisfies σ (P.interval i) α (.upper c b .eventually a φ) := by
    simpa only [Node.holds, dif_pos hk] using hsource
  have hnext : satisfies σ (P.interval j) β (.bounded c d m (¬ₘ m) .eventually a φ) := by
    intro t ht
    have hl : (P.interval j).left - (a : ℝ) ≤ t := by
      have hl := ht.1
      change (P.interval j).left - (β c : ℝ) < t ∨
        ((P.interval j).left - (β c : ℝ) = t ∧ m.Includes) at hl
      rw [hβc] at hl
      exact hl.elim le_of_lt (fun h => h.1.le)
    apply hU t
    constructor
    · change (P.interval i).left - (α c : ℝ) <[b] t
      rw [← hc]
      rcases hg with hg | ⟨hg, hb⟩
      · left; change (a : ℝ) < (γ c : ℝ) at hg; linarith
      · rcases hl.lt_or_eq with ht | ht
        · left; change (a : ℝ) = (γ c : ℝ) at hg; linarith
        · right
          exact ⟨by change (a : ℝ) = (γ c : ℝ) at hg; linarith,
            ((Marker.includes_conj _ _).1 hb).1⟩
    · have hr := ht.2
      change t <[¬ₘ m] ((P.interval j).left - (β d : ℝ)) at hr
      rw [hβd, NNReal.coe_zero, sub_zero, ← hadj, ← hm] at hr
      exact hr
  have hguard := (Node.holds_gt σ P γ ⟨k.1 + 1, by omega⟩ c
    (Marker.conj b (¬ₘ m)) a).2 hg
  simp only [upperEventuallyCheck, Node.holds, dif_pos hk, dif_pos hn] at hplain ⊢
  exact ⟨hplain, hguard, hnext, trivial⟩

/-- Selected `↑↓` `◇` check, retaining the frozen right endpoint. -/
theorem bounded_check_witness [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (hn : k.1 + 1 < P.size)
    (c d : Clock) (b q : Marker) (a : NNReal) (φ : Formula Var) (hcd : c ≠ d)
    (hg : (a : ℝ) <[Marker.conj b (¬ₘ (P.interval ⟨k.1 + 1, hn⟩).leftBoundary)]
      (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩) c : ℝ))
    (hdg : (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩) d : ℝ)
      <[Marker.conj q (P.interval ⟨k.1 + 1, hn⟩).leftBoundary] (a : ℝ))
    (hplain : Node.holds σ P α k (.plain φ))
    (hsource : Node.holds σ P α k (.predicate (.bounded c d b q .eventually a φ))) :
    Node.holds σ P α k
      (boundedEventuallyCheck c d b q (P.interval ⟨k.1 + 1, hn⟩).leftBoundary a φ) := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let j : Fin P.size := ⟨k.1 + 1, hn⟩
  let m := (P.interval j).leftBoundary
  let γ := ClockResetSet.elapse α (Judgement.duration P i)
  let β := (ClockResetSet.singleton c a).apply γ
  have hβc : β c = a := ClockResetSet.apply_singleton_self c a γ
  have hβd : β d = γ d := ClockResetSet.apply_singleton_of_ne a γ hcd.symm
  have hc : (P.interval j).left - (γ c : ℝ) = (P.interval i).left - (α c : ℝ) :=
    Judgement.next_left_sub_elapse_eq P α i hn c
  have hd : (P.interval j).left - (β d : ℝ) = (P.interval i).left - (α d : ℝ) := by
    rw [hβd]
    exact Judgement.next_left_sub_elapse_eq P α i hn d
  have hU : satisfies σ (P.interval i) α (.bounded c d b q .eventually a φ) := by
    simpa only [Node.holds, dif_pos hk] using hsource
  have hnext : satisfies σ (P.interval j) β (.bounded c d m q .eventually a φ) := by
    intro t ht
    have hl : (P.interval j).left - (a : ℝ) ≤ t := by
      have hl := ht.1
      change (P.interval j).left - (β c : ℝ) < t ∨
        ((P.interval j).left - (β c : ℝ) = t ∧ m.Includes) at hl
      rw [hβc] at hl
      exact hl.elim le_of_lt (fun h => h.1.le)
    apply hU t
    constructor
    · change (P.interval i).left - (α c : ℝ) <[b] t
      rw [← hc]
      rcases hg with hg | ⟨hg, hb⟩
      · left; change (a : ℝ) < (γ c : ℝ) at hg; linarith
      · rcases hl.lt_or_eq with ht | ht
        · left; change (a : ℝ) = (γ c : ℝ) at hg; linarith
        · right
          exact ⟨by change (a : ℝ) = (γ c : ℝ) at hg; linarith,
            ((Marker.includes_conj _ _).1 hb).1⟩
    · have hr := ht.2
      change t <[q] ((P.interval j).left - (β d : ℝ)) at hr
      rw [hd] at hr
      exact hr
  have hguard := (Node.holds_gt σ P γ ⟨k.1 + 1, by omega⟩ c
    (Marker.conj b (¬ₘ m)) a).2 hg
  have hdguard := (Node.holds_lt σ P γ ⟨k.1 + 1, by omega⟩ d (Marker.conj q m) a).2 hdg
  simp only [boundedEventuallyCheck, Node.holds, dif_pos hk, dif_pos hn] at hplain ⊢
  exact ⟨hplain, hguard, hdguard, hnext, trivial⟩

end STLTableau.UnboundedClocked
