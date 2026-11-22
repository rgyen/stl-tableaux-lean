import STLTableaux.Rules.Catalogue.ClockedExpansion

/-! Exact selected check branches, strengthening the existing existential
completeness helpers without changing their hypotheses or semantics. -/
namespace STLTableau
open scoped STL
open STLTableau.ExpansionRule
variable {Clock Var : Type*}
theorem bounded_check_witness [DecidableEq Clock]
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size)
    (hg : I.lower <[Marker.conj b (¬ₘ (P.interval ⟨k.1 + 1, hn⟩).leftBoundary)]
      (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩) c : ℝ))
    (hdg : (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩) d : ℝ)
      <[Marker.conj q (P.interval ⟨k.1 + 1, hn⟩).leftBoundary] I.lower)
    (hφ : (σ, P, α, k)⊨ⱼ(Judgement.predicate (.plain φ)))
    (h : (σ, P, α, k)⊨ⱼ((boundedEventually c d b q I φ).source : Judgement Clock Var)) :
    Judgement.Satisfies σ P α k (boundedEventually_check c d b q (P.interval ⟨k.1 + 1, hn⟩).leftBoundary I φ) := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let j : Fin P.size := ⟨k.1 + 1, hn⟩
  let m := (P.interval j).leftBoundary
  let a : NNReal := ⟨I.lower, I.lower_nonnegative⟩
  let γ := ClockResetSet.elapse α (Judgement.duration P i)
  let β := (⟦c ↦ᶜ a⟧).apply γ
  have hβc : β c = a := ClockResetSet.apply_singleton_self c a γ
  have hβd : β d = γ d := ClockResetSet.apply_singleton_of_ne a γ hcd.symm
  have hc := Judgement.next_left_sub_elapse_eq P α i hn c
  have hd : (P.interval j).left - (β d : ℝ) = (P.interval i).left - (α d : ℝ) := by
    rw [hβd]
    exact Judgement.next_left_sub_elapse_eq P α i hn d
  have hU : (σ, P.interval i, α)⊨ᵢ(↑↓[c, d, b, q]◇[I]φ) := by
    simpa only [boundedEventually, Judgement.Satisfies, dif_pos hk] using h
  have hnext : (σ, P.interval j, β)⊨ᵢ(↑↓[c, d, m, q]◇[I]φ) := by
    intro t ht
    have hl : (P.interval j).left - I.lower < t ∨
        ((P.interval j).left - I.lower = t ∧ m.Includes) := by
      have hl := ht.1
      change (P.interval j).left - (β c : ℝ) < t ∨
        ((P.interval j).left - (β c : ℝ) = t ∧ m.Includes) at hl
      rw [hβc] at hl
      exact hl
    have hlow : (P.interval j).left - I.lower ≤ t := hl.elim le_of_lt (fun h => h.1.le)
    have htOld : t ∈ IntervalPredicate.scope (P.interval i) α (↑↓[c, d, b, q]◇[I]φ) := by
      constructor
      · change (P.interval i).left - (α c : ℝ) < t ∨
          ((P.interval i).left - (α c : ℝ) = t ∧ b.Includes)
        have hc' : (P.interval j).left - (γ c : ℝ) = (P.interval i).left - (α c : ℝ) := hc
        rw [← hc']
        rcases hg with hg | ⟨hg, hm⟩
        · left; linarith
        · rcases hlow.lt_or_eq with ht | ht
          · left; linarith
          · exact Or.inr ⟨by linarith, ((Marker.includes_conj _ _).1 hm).1⟩
      · have hr := ht.2
        change t < (P.interval j).left - (β d : ℝ) ∨
          (t = (P.interval j).left - (β d : ℝ) ∧ q.Includes) at hr
        rw [hd] at hr
        exact hr
    obtain ⟨u, huI, _, huφ⟩ := hU t htOld
    refine ⟨u, huI, ?_, huφ⟩
    have hdelay : I.lower ≤ u.1 - t := huI.1
    rcases hl with hl | ⟨hl, hm⟩
    · left; linarith
    · by_cases hlt : (P.interval j).left < u.1
      · exact Or.inl hlt
      · exact Or.inr ⟨by linarith, hm⟩
  have hguard : (σ, P, γ, ⟨k.1 + 1, by omega⟩)⊨ⱼ(c >ᶜ[Marker.conj b (¬ₘ m)] a) :=
    (Judgement.satisfies_markedGT _ _ _ _ _ _ _).2 hg
  have hdguard : (σ, P, γ, ⟨k.1 + 1, by omega⟩)⊨ⱼ(d <ᶜ[Marker.conj q m] a) :=
    (Judgement.satisfies_markedLT _ _ _ _ _ _ _).2 hdg
  simp only [boundedEventually_check, Judgement.Satisfies, dif_pos hk, dif_pos hn] at hφ ⊢
  exact ⟨hφ, hguard, hdguard, hnext, by trivial⟩


theorem upper_check_witness [DecidableEq Clock]
    (c d : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (hpos : 0 < I.lower)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size)
    (hg : I.lower <[Marker.conj b (¬ₘ (P.interval ⟨k.1 + 1, hn⟩).leftBoundary)]
      (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩) c : ℝ))
    (hφ : (σ, P, α, k)⊨ⱼ(Judgement.predicate (.plain φ)))
    (h : (σ, P, α, k)⊨ⱼ((upperEventually c d b I φ).source : Judgement Clock Var)) :
    Judgement.Satisfies σ P α k (upperEventually_check c d b (P.interval ⟨k.1 + 1, hn⟩).leftBoundary I φ) := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let j : Fin P.size := ⟨k.1 + 1, hn⟩
  let m := (P.interval j).leftBoundary
  let a : NNReal := ⟨I.lower, I.lower_nonnegative⟩
  let γ := ClockResetSet.elapse α (Judgement.duration P i)
  let β := ((⟦c ↦ᶜ a⟧).union ⟦d ↦ᶜ 0⟧).apply γ
  have hβc : β c = a := by
    simp [β, ClockResetSet.apply, ClockResetSet.union, ClockResetSet.singleton]
  have hβd : β d = 0 := by
    change ((⟦c ↦ᶜ a⟧).union ⟦d ↦ᶜ 0⟧).apply γ d = 0
    rw [ClockResetSet.apply_union_eq_right_of_not_mem _ _ γ (by simp [Ne.symm hcd])]
    exact ClockResetSet.apply_singleton_self d 0 γ
  have hc : (P.interval j).left - (γ c : ℝ) = (P.interval i).left - (α c : ℝ) :=
    Judgement.next_left_sub_elapse_eq P α i hn c
  have hadj : (P.interval i).right = (P.interval j).left := P.adjacent_right_eq_left i hn
  have hm : (P.interval i).rightBoundary = ¬ₘ m :=
    P.adjacent_rightBoundary_eq_complement_leftBoundary i hn
  have hU : (σ, P.interval i, α)⊨ᵢ(↑[c, b]◇[I]φ) := by
    simpa only [upperEventually, Judgement.Satisfies, dif_pos hk] using h
  have hnext : (σ, P.interval j, β)⊨ᵢ(↑↓[c, d, m, ¬ₘ m]◇[I]φ) := by
    intro t ht
    have hl : (P.interval j).left - I.lower < t ∨
        ((P.interval j).left - I.lower = t ∧ m.Includes) := by
      have hl := ht.1
      change (P.interval j).left - (β c : ℝ) < t ∨
        ((P.interval j).left - (β c : ℝ) = t ∧ m.Includes) at hl
      rw [hβc] at hl
      exact hl
    have hlow : (P.interval j).left - I.lower ≤ t := hl.elim le_of_lt (fun h => h.1.le)
    have htOld : t ∈ IntervalPredicate.scope (P.interval i) α (↑[c, b]◇[I]φ) := by
      constructor
      · change (P.interval i).left - (α c : ℝ) < t ∨
          ((P.interval i).left - (α c : ℝ) = t ∧ b.Includes)
        rw [← hc]
        rcases hg with hg | ⟨hg, hb⟩
        · left; linarith
        · rcases hlow.lt_or_eq with ht | ht
          · left; linarith
          · exact Or.inr ⟨by linarith, ((Marker.includes_conj _ _).1 hb).1⟩
      · have hr := ht.2
        change t < (P.interval j).left - (β d : ℝ) ∨
          (t = (P.interval j).left - (β d : ℝ) ∧ (¬ₘ m).Includes) at hr
        rw [hβd, NNReal.coe_zero, sub_zero, ← hadj, ← hm] at hr
        exact hr
    obtain ⟨u, huI, _, huφ⟩ := hU t htOld
    refine ⟨u, huI, ?_, huφ⟩
    have hdelay : I.lower ≤ u.1 - t := huI.1
    rcases hl with hl | ⟨hl, hm⟩
    · left; linarith
    · by_cases hlt : (P.interval j).left < u.1
      · exact Or.inl hlt
      · exact Or.inr ⟨by linarith, hm⟩
  have hguard : (σ, P, γ, ⟨k.1 + 1, by omega⟩)⊨ⱼ(c >ᶜ[Marker.conj b (¬ₘ m)] a) :=
    (Judgement.satisfies_markedGT _ _ _ _ _ _ _).2 hg
  simp only [upperEventually_check, Judgement.Satisfies, dif_pos hk, dif_pos hn] at hφ ⊢
  exact ⟨hφ, hguard, hnext, by trivial⟩


end STLTableau
