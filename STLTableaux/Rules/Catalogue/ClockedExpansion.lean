/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Rules.Catalogue.Expansion

/-! # Clocked expansion rules

Marker schemas are expanded into their two finite alternatives. A branch's
`lty` test chooses the marker in the current semantic context.
-/

namespace STLTableau.Judgement

open scoped STL

/-- Compile a marked less-than guard to one of the existing clock judgements. -/
def markedLT {Clock Var : Type*} (c : Clock) (m : Marker) (a : NNReal) :
    Judgement Clock Var :=
  match m with
  | ○ => c <ᶜ a
  | ● => c ≤ᶜ a

/-- Compile the reversed marked comparison to a greater-than guard. -/
def markedGT {Clock Var : Type*} (c : Clock) (m : Marker) (a : NNReal) :
    Judgement Clock Var :=
  match m with
  | ○ => c >ᶜ a
  | ● => c ≥ᶜ a

scoped[STL] notation:50 c:51 " <ᶜ[" m "] " a:51 =>
  STLTableau.Judgement.markedLT c m a
scoped[STL] notation:50 c:51 " >ᶜ[" m "] " a:51 =>
  STLTableau.Judgement.markedGT c m a

@[simp] theorem satisfies_markedLT {Clock Var : Type*} (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock) (k : Position P)
    (c : Clock) (m : Marker) (a : NNReal) :
    ((σ,P,α,k)⊨ⱼ(c <ᶜ[m] a)) ↔ ((α c : ℝ) <[m] (a : ℝ)) := by
  cases m <;> simp [markedLT, Satisfies, ClockRelation.Holds]

@[simp] theorem satisfies_markedGT {Clock Var : Type*} (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock) (k : Position P)
    (c : Clock) (m : Marker) (a : NNReal) :
    ((σ,P,α,k)⊨ⱼ(c >ᶜ[m] a)) ↔ ((a : ℝ) <[m] (α c : ℝ)) := by
  cases m <;> simp [markedGT, Satisfies, ClockRelation.Holds]

@[simp] theorem nonPredicateSatisfies_markedLT {Clock Var : Type*} (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock) (k : Position P)
    (c : Clock) (m : Marker) (a : NNReal) :
    NonPredicateSatisfies σ P α k (c <ᶜ[m] a) ↔ ((α c : ℝ) <[m] (a : ℝ)) := by
  cases m <;> simp [markedLT, NonPredicateSatisfies, ClockRelation.Holds]

/-- Crossing a right cut is equivalent to passing the shifted left cut
with the complementary marker. -/
theorem not_markedLT_add_complement_iff (t shift boundary : ℝ) (m : Marker) :
    (¬ ((t + shift) <[¬ₘ m] boundary)) ↔ ((boundary - shift) <[m] t) := by
  cases m with
  | «open» =>
    simp only [Marker.complement_open, markedLT_closed, not_le, markedLT_open]
    exact sub_lt_iff_lt_add.symm
  | closed =>
    simp only [Marker.complement_closed, markedLT_open, not_lt, markedLT_closed]
    exact sub_le_iff_le_add.symm

/-- The defer and check guards are exact complements, including equality. -/
theorem upperAlways_guard_complement (x a : ℝ) (b m : Marker) :
    (x <[Marker.imp b m] a) ↔
      ¬(a <[Marker.conj b (Marker.complement m)] x) := by
  cases b <;> cases m <;>
    simp [Marker.imp, Marker.conj, Marker.complement]

/-- `↑↓` `□` continuation and finish guards are exact complements. -/
theorem boundedAlways_right_guard_complement (x z : ℝ) (q m : Marker) :
    (x <[Marker.conj q m] z) ↔ ¬(z <[Marker.notConj q m] x) := by
  cases q <;> cases m <;> simp [Marker.conj, Marker.notConj]

@[simp] theorem evaluatedInvariant_markedLT {Clock Var : Type*}
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P) (c : Clock) (m : Marker) (a : NNReal) :
    EvaluatedInvariant σ P α k (c <ᶜ[m] a) := by
  cases m <;> trivial

@[simp] theorem evaluatedInvariant_markedGT {Clock Var : Type*}
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P) (c : Clock) (m : Marker) (a : NNReal) :
    EvaluatedInvariant σ P α k (c >ᶜ[m] a) := by
  cases m <;> trivial

end STLTableau.Judgement

namespace STLTableau.ExpansionRule

open scoped STL

variable {Clock Var : Type*}

private theorem exists_marker_iff (p : Marker → Prop) :
    (∃ m, p m) ↔ p ○ ∨ p ● := by
  constructor
  · rintro ⟨m, hm⟩
    cases m
    · exact Or.inl hm
    · exact Or.inr hm
  · rintro (h | h)
    · exact ⟨○, h⟩
    · exact ⟨●, h⟩

/-- The eventually opening schema `TemporalOpen`, enumerating both markers. -/
def openEventually [DecidableEq Clock] (c : Clock) (I : BoundedTimeInterval)
    (φ : Formula Var) : ExpansionRule Clock Var where
  source := .plain (◇[(I : TimeInterval)] φ)
  branches := [
    ⟦c ↦ᶜ 0⟧ ·ⱼ ((↑[c,○]◇[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[○]),
    ⟦c ↦ᶜ 0⟧ ·ⱼ ((↑[c,●]◇[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[●])]
  branches_nonempty := by simp

/-- Opening eventually is correct without stability, including at terminal positions. -/
theorem openEventually_correct_at [DecidableEq Clock] (c : Clock)
    (I : BoundedTimeInterval) (φ : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) :
    ((σ,P,α,k)⊨ⱼ((openEventually c I φ).source : Judgement Clock Var)) ↔
      (openEventually c I φ).BranchSatisfied σ P α k := by
  change ((σ,P,α,k)⊨ⱼ
    ((IntervalPredicate.plain (◇[(I : TimeInterval)] φ) :
      IntervalPredicate Clock Var) : Judgement Clock Var)) ↔ _
  rw [Judgement.satisfies_plain_eventually_iff_reset_upper σ P α k c I φ]
  rw [exists_marker_iff]
  simp [BranchSatisfied, openEventually]

/-- The always opening schema `TemporalOpen`, enumerating both markers. -/
def openAlways [DecidableEq Clock] (c : Clock) (I : BoundedTimeInterval)
    (φ : Formula Var) : ExpansionRule Clock Var where
  source := .plain (□[(I : TimeInterval)] φ)
  branches := [
    ⟦c ↦ᶜ 0⟧ ·ⱼ ((↑[c,○]□[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[○]),
    ⟦c ↦ᶜ 0⟧ ·ⱼ ((↑[c,●]□[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[●])]
  branches_nonempty := by simp

/-- Opening always is correct without stability, including at terminal positions. -/
theorem openAlways_correct_at [DecidableEq Clock] (c : Clock)
    (I : BoundedTimeInterval) (φ : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) :
    ((σ,P,α,k)⊨ⱼ((openAlways c I φ).source : Judgement Clock Var)) ↔
      (openAlways c I φ).BranchSatisfied σ P α k := by
  change ((σ,P,α,k)⊨ⱼ
    ((IntervalPredicate.plain (□[(I : TimeInterval)] φ) :
      IntervalPredicate Clock Var) : Judgement Clock Var)) ↔ _
  rw [Judgement.satisfies_plain_always_iff_reset_upper σ P α k c I φ]
  rw [exists_marker_iff]
  simp [BranchSatisfied, openAlways]

/-- `RuleAlwaysUpBranchThree`: defer checking, resetting only the new clock. -/
def upperAlways_defer [DecidableEq Clock] (c d : Clock) (b m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) : Judgement Clock Var :=
  Xⱼ ((c <ᶜ[Marker.imp b m] (⟨I.lower, I.lower_nonnegative⟩ : NNReal)) ∧ⱼ
    (⟦d ↦ᶜ 0⟧ ·ⱼ ((↑↓[c,d,b,¬ₘ m]□[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[m])))

/-- `RuleAlwaysUpBranchFour`: check now and reset the remaining region.
Correctness requires the reset clocks to be distinct. -/
def upperAlways_check [DecidableEq Clock] (c d : Clock) (b m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) : Judgement Clock Var :=
  let a : NNReal := ⟨I.lower, I.lower_nonnegative⟩
  Judgement.predicate (.plain φ) ∧ⱼ
    Xⱼ ((c >ᶜ[Marker.conj b (¬ₘ m)] a) ∧ⱼ
      (((⟦c ↦ᶜ a⟧).union ⟦d ↦ᶜ 0⟧) ·ⱼ
        ((↑↓[c,d,m,¬ₘ m]□[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[m])))

/-- The four `↑` `□` branch schemas, with the two marker-dependent
schemas each instantiated twice. This definition alone asserts no correctness. -/
def upperAlways [DecidableEq Clock] (c d : Clock) (b : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) : ExpansionRule Clock Var where
  source := ↑[c,b]□[I]φ
  branches := [
    upperAlways_defer c d b ○ I φ,
    upperAlways_defer c d b ● I φ,
    Xⱼ ((c ≤ᶜ (⟨I.lower, I.lower_nonnegative⟩ : NNReal)) ∧ⱼ ∗),
    Judgement.predicate (.plain φ) ∧ⱼ
      Xⱼ ((c >ᶜ (⟨I.lower, I.lower_nonnegative⟩ : NNReal)) ∧ⱼ ∗),
    upperAlways_check c d b ○ I φ,
    upperAlways_check c d b ● I φ]
  branches_nonempty := by simp

@[simp] theorem upperAlways_branch_count [DecidableEq Clock] (c d : Clock)
    (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var) :
    (upperAlways c d b I φ).branches.length = 6 := rfl

/-- Soundness of `↑` `□` branch three, with explicit reset freshness.
The guard accounts for equality at the next boundary; no stability is needed. -/
theorem upperAlways_defer_sound [DecidableEq Clock] (c d : Clock) (b m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) (hcd : c ≠ d) :
    upperAlways_defer c d b m I φ ⇒ⱼ
      ((↑[c,b]□[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  intro σ P α k h
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · let i : Fin P.size := ⟨k.1, hk⟩
      let j : Fin P.size := ⟨k.1 + 1, hn⟩
      let γ := ClockResetSet.elapse α (Judgement.duration P i)
      let β := (⟦d ↦ᶜ 0⟧).apply γ
      have hβc : β c = γ c := ClockResetSet.apply_singleton_of_ne 0 γ hcd
      have hβd : β d = 0 := ClockResetSet.apply_singleton_self d 0 γ
      have hadj : (P.interval i).right = (P.interval j).left :=
        P.adjacent_right_eq_left i hn
      have hc : (P.interval i).left - (α c : ℝ) =
          (P.interval j).left - (β c : ℝ) := by
        rw [hβc]
        exact (Judgement.next_left_sub_elapse_eq P α i hn c).symm
      have hd : (P.interval i).right = (P.interval j).left - (β d : ℝ) := by
        simpa only [hβd, NNReal.coe_zero, sub_zero] using hadj
      simp only [upperAlways_defer, Judgement.Satisfies, dif_pos hk, dif_pos hn] at h ⊢
      have hmarker : (P.interval j).leftBoundary = m := h.2.2
      have hm : (P.interval i).rightBoundary = Marker.complement m :=
        (P.adjacent_rightBoundary_eq_complement_leftBoundary i hn).trans
          (congrArg Marker.complement hmarker)
      have hg : (β c : ℝ) <[Marker.imp b (P.interval j).leftBoundary] I.lower := by
        rw [hβc, hmarker]
        exact (Judgement.satisfies_markedLT σ P γ ⟨k.1 + 1, by omega⟩ c
          (Marker.imp b m) ⟨I.lower, I.lower_nonnegative⟩).1 h.1
      exact IntervalPredicate.satisfies_upper_always_of_bounded_next_of_guard
        σ (P.interval i) (P.interval j) α β c d b (¬ₘ m) I φ hc hd hm hg h.2.1
    · simp [upperAlways_defer, Judgement.Satisfies, hk, hn] at h
  · simp [upperAlways_defer, Judgement.Satisfies, hk] at h

/-- `↑` `□` branch one: at the end of the partition the guard places
the entire checking region beyond all remaining signal times. -/
theorem upperAlways_terminal_wait_sound (c : Clock) (b : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) :
    (Xⱼ ((c ≤ᶜ (⟨I.lower, I.lower_nonnegative⟩ : NNReal)) ∧ⱼ ∗)) ⇒ⱼ
      ((↑[c,b]□[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  intro σ P α k h
  by_cases hk : k.1 < P.size
  · let i : Fin P.size := ⟨k.1, hk⟩
    simp only [Judgement.Satisfies, dif_pos hk] at h ⊢
    have hlast : i.1 + 1 = P.size := h.2
    have hg : (ClockResetSet.elapse α (Judgement.duration P i) c : ℝ) ≤ I.lower := h.1
    change (α c : ℝ) + ((P.interval i).right - (P.interval i).left) ≤ I.lower at hg
    intro t ht hs
    have htJ := P.mem_last_of_left_condition i hlast t.2 hs
    have htr := P.lt_right_of_mem_last i hlast htJ
    have htl : (P.interval i).left - (α c : ℝ) + I.lower ≤ t.1 :=
      MarkedInterval.left_le_of_mem ht
    exact (by linarith : False).elim
  · simp only [Judgement.Satisfies, dif_neg hk] at h

/-- `↑` `□` branch two: every checked signal point lies in the last
piece, where the unclocked predicate holds. The clock guard is not needed for soundness. -/
theorem upperAlways_terminal_check_sound (c : Clock) (b : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) :
    (Judgement.predicate (.plain φ) ∧ⱼ
      Xⱼ ((c >ᶜ (⟨I.lower, I.lower_nonnegative⟩ : NNReal)) ∧ⱼ ∗)) ⇒ⱼ
      ((↑[c,b]□[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  intro σ P α k h
  by_cases hk : k.1 < P.size
  · simp only [Judgement.Satisfies, dif_pos hk, IntervalPredicate.Satisfies] at h ⊢
    intro t _ hs
    exact h.1 t (P.mem_last_of_left_condition ⟨k.1, hk⟩ h.2.2 t.2 hs)
  · simp [Judgement.Satisfies, hk] at h

/-- Soundness of `↑` `□` branch four. The current unclocked predicate
covers the current piece; the reset predicate covers all remaining checks. -/
theorem upperAlways_check_sound [DecidableEq Clock] (c d : Clock) (b m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) (hcd : c ≠ d) :
    upperAlways_check c d b m I φ ⇒ⱼ
      ((↑[c,b]□[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  intro σ P α k h
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
        rw [ClockResetSet.apply_union_eq_right_of_not_mem _ _ γ
          (by simp [Ne.symm hcd])]
        exact ClockResetSet.apply_singleton_self d 0 γ
      have hadj : (P.interval i).right = (P.interval j).left :=
        P.adjacent_right_eq_left i hn
      have hm : (P.interval i).rightBoundary = Marker.complement (P.interval j).leftBoundary :=
        P.adjacent_rightBoundary_eq_complement_leftBoundary i hn
      simp only [upperAlways_check, Judgement.Satisfies, dif_pos hk, dif_pos hn] at h ⊢
      have hmarker : (P.interval j).leftBoundary = m := h.2.2.2
      have hnext : (σ,P.interval j,β)⊨ᵢ(↑↓[c,d,m,¬ₘ m]□[I]φ) := h.2.2.1
      intro t ht hs
      rcases IntervalPredicate.mem_or_inCurrentSuffix_of_adjacent
          (P.interval i) (P.interval j) hadj hm hs with htJ | htK
      · exact h.1 t htJ
      · apply hnext t _ htK
        change ((P.interval j).left - (β c : ℝ) + I.lower < t.1 ∨
            ((P.interval j).left - (β c : ℝ) + I.lower = t.1 ∧ m.Includes)) ∧
          (t.1 < (P.interval j).left - (β d : ℝ) + I.upper ∨
            (t.1 = (P.interval j).left - (β d : ℝ) + I.upper ∧ (¬ₘ m).Includes))
        rw [hβc, hβd]
        constructor
        · change ((P.interval j).left - I.lower + I.lower < t.1 ∨
            ((P.interval j).left - I.lower + I.lower = t.1 ∧ m.Includes))
          simpa only [sub_add_cancel, IntervalPredicate.InCurrentSuffix, hmarker] using htK
        · have hright : t.1 < (P.interval i).right + I.upper ∨
              (t.1 = (P.interval i).right + I.upper ∧ (P.interval i).rightBoundary.Includes) := ht.2
          simpa only [NNReal.coe_zero, sub_zero, hadj, hm, hmarker] using hright
    · simp [upperAlways_check, Judgement.Satisfies, hk, hn] at h
  · simp [upperAlways_check, Judgement.Satisfies, hk] at h

/-- All six concrete `↑` `□` branches (four manuscript schemas) are sound.
Fresh reset clocks are required, but neither stability nor an extra invariant
is needed in this direction. -/
theorem upperAlways_sound_at [DecidableEq Clock] (c d : Clock) (b : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) (hcd : c ≠ d)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (h : (upperAlways c d b I φ).BranchSatisfied σ P α k) :
    (σ,P,α,k)⊨ⱼ((upperAlways c d b I φ).source : Judgement Clock Var) := by
  obtain ⟨B, hB, h⟩ := h
  simp only [upperAlways, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl
  · exact upperAlways_defer_sound c d b ○ I φ hcd σ P α k h
  · exact upperAlways_defer_sound c d b ● I φ hcd σ P α k h
  · exact upperAlways_terminal_wait_sound c b I φ σ P α k h
  · exact upperAlways_terminal_check_sound c b I φ σ P α k h
  · exact upperAlways_check_sound c d b ○ I φ hcd σ P α k h
  · exact upperAlways_check_sound c d b ● I φ hcd σ P α k h

/-- Completeness of `↑` `□` expansion at the last declaring interval.
Only the two terminal branches are needed. -/
theorem upperAlways_complete_at_last [DecidableEq Clock] (c d : Clock) (b : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hlast : k.1 + 1 = P.size)
    (hs : σ.StablePartition (□[(I : TimeInterval)] φ) P)
    (h : (σ,P,α,k)⊨ⱼ((upperAlways c d b I φ).source : Judgement Clock Var)) :
    (upperAlways c d b I φ).BranchSatisfied σ P α k := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let a : NNReal := ⟨I.lower, I.lower_nonnegative⟩
  let γ := ClockResetSet.elapse α (Judgement.duration P i)
  by_cases hle : γ c ≤ a
  · refine ⟨Xⱼ ((c ≤ᶜ a) ∧ⱼ ∗), by simp [upperAlways, a], ?_⟩
    simp only [Judgement.Satisfies, dif_pos hk]
    exact ⟨hle, hlast⟩
  · have hgt : a < γ c := lt_of_not_ge hle
    have hg : I.lower < (α c : ℝ) +
        ((P.interval i).right - (P.interval i).left) := hgt
    have hDomain : (P.interval i).carrier ⊆ σ.domain := by
      intro t ht
      rw [← P.covers]
      exact Set.mem_iUnion.2 ⟨i, ht⟩
    have hJ : (P.interval i).left < (P.interval i).right := by
      obtain ⟨t, ht⟩ := P.nonempty i
      exact (MarkedInterval.left_le_of_mem ht).trans_lt (P.lt_right_of_mem_last i hlast ht)
    have hφ : (σ,P.interval i,α)⊨ᵢ(.plain φ) := by
      apply IntervalPredicate.satisfies_plain_of_upper_always_of_overlap
        σ (P.interval i) α c b I φ hJ hDomain (by linarith)
        (hs i φ (.neg (.until_right (.neg (.refl φ)))))
      simpa only [upperAlways, Judgement.Satisfies, dif_pos hk] using h
    refine ⟨Judgement.predicate (.plain φ) ∧ⱼ Xⱼ ((c >ᶜ a) ∧ⱼ ∗),
      by simp [upperAlways, a], ?_⟩
    simp only [Judgement.Satisfies, dif_pos hk]
    exact ⟨hφ, hgt, hlast⟩

/-- At a nonterminal declaring interval, the defer guard guarantees a
satisfied defer branch. The remaining check-guard case is separate. -/
theorem upperAlways_defer_complete_at [DecidableEq Clock]
    (c d : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size)
    (hg : (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩) c : ℝ)
      <[Marker.imp b (P.interval ⟨k.1 + 1, hn⟩).leftBoundary] I.lower)
    (h : (σ,P,α,k)⊨ⱼ((upperAlways c d b I φ).source : Judgement Clock Var)) :
    (upperAlways c d b I φ).BranchSatisfied σ P α k := by
  have hk : k.1 < P.size := by omega
  let γ := ClockResetSet.elapse α (Judgement.duration P ⟨k.1, hk⟩)
  obtain ⟨m, hreset⟩ := Judgement.satisfies_next_reset_bounded_always_of_upper_at
    σ P α k hn c d b I φ hcd h
  have hmarker : (P.interval ⟨k.1 + 1, hn⟩).leftBoundary = m := by
    have hreset' := hreset
    simp only [Judgement.Satisfies, dif_pos hk, dif_pos hn] at hreset'
    exact hreset'.2
  have hguard : (σ,P,γ,⟨k.1 + 1, by omega⟩)⊨ⱼ
      (c <ᶜ[Marker.imp b m] (⟨I.lower, I.lower_nonnegative⟩ : NNReal)) := by
    apply (Judgement.satisfies_markedLT _ _ _ _ _ _ _).2
    rw [← hmarker]
    exact hg
  refine ⟨upperAlways_defer c d b m I φ, ?_, ?_⟩
  · cases m <;> simp [upperAlways]
  · simp only [upperAlways_defer, Judgement.Satisfies, dif_pos hk, dif_pos hn] at hreset ⊢
    exact ⟨hguard, hreset⟩

/-- Completeness of the check/reset case, including touching endpoints and
singleton declaring intervals. -/
theorem upperAlways_check_complete_at [DecidableEq Clock]
    (c d : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size)
    (hg : I.lower <[Marker.conj b (Marker.complement
        (P.interval ⟨k.1 + 1, hn⟩).leftBoundary)]
      (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩) c : ℝ))
    (hs : σ.StablePartition (□[(I : TimeInterval)] φ) P)
    (h : (σ,P,α,k)⊨ⱼ((upperAlways c d b I φ).source : Judgement Clock Var)) :
    (upperAlways c d b I φ).BranchSatisfied σ P α k := by
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
  have hadj : (P.interval i).right = (P.interval j).left :=
    P.adjacent_right_eq_left i hn
  have hm : (P.interval i).rightBoundary = Marker.complement m :=
    P.adjacent_rightBoundary_eq_complement_leftBoundary i hn
  have hcut : (P.interval i).left - (α c : ℝ) + I.lower
      <[Marker.conj b (P.interval i).rightBoundary] (P.interval i).right := by
    rw [hm]
    change I.lower <[Marker.conj b (Marker.complement m)]
      ((α c : ℝ) + ((P.interval i).right - (P.interval i).left)) at hg
    rcases hg with hlt | ⟨heq, hb⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, hb⟩
  have hU : (σ,P.interval i,α)⊨ᵢ(↑[c,b]□[I]φ) := by
    simpa only [upperAlways, Judgement.Satisfies, dif_pos hk] using h
  have hDomain : (P.interval i).carrier ⊆ σ.domain := by
    intro t ht
    rw [← P.covers]
    exact Set.mem_iUnion.2 ⟨i, ht⟩
  have hφ := IntervalPredicate.satisfies_plain_of_upper_always_of_marked_overlap
    σ (P.interval i) α c b I φ (P.nonempty i) hDomain hcut
    (hs i φ (.neg (.until_right (.neg (.refl φ))))) hU
  have hnext : (σ,P.interval j,β)⊨ᵢ(↑↓[c,d,m,¬ₘ m]□[I]φ) := by
    intro t ht hsuffix
    apply hU t
    · have htl : (P.interval j).left ≤ t.1 := by
        have hl := MarkedInterval.left_le_of_mem ht
        change (P.interval j).left - (β c : ℝ) + I.lower ≤ t.1 at hl
        rw [hβc] at hl
        change (P.interval j).left - I.lower + I.lower ≤ t.1 at hl
        simpa only [sub_add_cancel] using hl
      constructor
      · rcases hcut with hlt | ⟨heq, hb⟩
        · exact Or.inl ((hlt.trans_eq hadj).trans_le htl)
        · rcases htl.lt_or_eq with hlt | heq'
          · exact Or.inl ((heq.trans hadj).trans_lt hlt)
          · exact Or.inr ⟨heq.trans (hadj.trans heq'),
              ((Marker.includes_conj _ _).1 hb).1⟩
      · have hr : t.1 < (P.interval j).left - (β d : ℝ) + I.upper ∨
            (t.1 = (P.interval j).left - (β d : ℝ) + I.upper ∧ (¬ₘ m).Includes) := ht.2
        change t.1 < (P.interval i).right + I.upper ∨
          (t.1 = (P.interval i).right + I.upper ∧ (P.interval i).rightBoundary.Includes)
        simpa only [hβd, NNReal.coe_zero, sub_zero, hadj, hm] using hr
    · exact IntervalPredicate.inCurrentSuffix_of_adjacent
        (P.interval i) (P.interval j) (P.nonempty i) hadj hsuffix
  have hguard : (σ,P,γ,⟨k.1 + 1, by omega⟩)⊨ⱼ
      (c >ᶜ[Marker.conj b (¬ₘ m)] a) :=
    (Judgement.satisfies_markedGT _ _ _ _ _ _ _).2 hg
  refine ⟨upperAlways_check c d b m I φ, ?_, ?_⟩
  · cases m <;> simp [upperAlways]
  · simp only [upperAlways_check, Judgement.Satisfies, dif_pos hk, dif_pos hn]
    exact ⟨hφ, hguard, hnext, rfl⟩

/-- Full `↑` `□` completeness, with fresh reset clocks and full stability. -/
theorem upperAlways_complete_at [DecidableEq Clock] (c d : Clock) (b : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) (hcd : c ≠ d)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hs : σ.StablePartition (□[(I : TimeInterval)] φ) P)
    (h : (σ,P,α,k)⊨ⱼ((upperAlways c d b I φ).source : Judgement Clock Var)) :
    (upperAlways c d b I φ).BranchSatisfied σ P α k := by
  classical
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · let γ := ClockResetSet.elapse α (Judgement.duration P ⟨k.1, hk⟩)
      let m := (P.interval ⟨k.1 + 1, hn⟩).leftBoundary
      by_cases hg : (γ c : ℝ) <[Marker.imp b m] I.lower
      · exact upperAlways_defer_complete_at c d b I φ hcd σ P α k hn hg h
      · have hc : I.lower <[Marker.conj b (Marker.complement m)] (γ c : ℝ) := by
          by_contra hc
          exact hg ((Judgement.upperAlways_guard_complement _ _ b m).2 hc)
        exact upperAlways_check_complete_at c d b I φ hcd σ P α k hn hc hs h
    · exact upperAlways_complete_at_last c d b I φ σ P α k (by omega) hs h
  · simp [Judgement.Satisfies, hk] at h

/-- Correctness of all four `↑` `□` continuation schemas. -/
theorem upperAlways_correct_at [DecidableEq Clock] (c d : Clock) (b : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) (hcd : c ≠ d)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hs : σ.StablePartition (□[(I : TimeInterval)] φ) P) :
    ((σ,P,α,k)⊨ⱼ((upperAlways c d b I φ).source : Judgement Clock Var)) ↔
      (upperAlways c d b I φ).BranchSatisfied σ P α k :=
  ⟨upperAlways_complete_at c d b I φ hcd σ P α k hs,
    upperAlways_sound_at c d b I φ hcd σ P α k⟩

/-- `↑↓` `□` branch one: defer with unchanged clocks. -/
def boundedAlways_defer (c d : Clock) (b q m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) : Judgement Clock Var :=
  Xⱼ (lty[m] ∧ⱼ
    (c <ᶜ[Marker.imp b m] (⟨I.lower, I.lower_nonnegative⟩ : NNReal)) ∧ⱼ
    (↑↓[c,d,b,q]□[I]φ : IntervalPredicate Clock Var))

/-- `↑↓` `□` branch four: check now and reset only the left clock. -/
def boundedAlways_check [DecidableEq Clock] (c d : Clock) (b q m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) : Judgement Clock Var :=
  let a : NNReal := ⟨I.lower, I.lower_nonnegative⟩
  let z : NNReal := ⟨I.upper, I.lower_nonnegative.trans I.nonSingular.le⟩
  Judgement.predicate (.plain φ) ∧ⱼ
    Xⱼ ((c >ᶜ[Marker.conj b (¬ₘ m)] a) ∧ⱼ
      (d <ᶜ[Marker.conj q m] z) ∧ⱼ
      (⟦c ↦ᶜ a⟧ ·ⱼ ((↑↓[c,d,m,q]□[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[m])))

/-- `↑↓` `□` branch five: finish checking, with no next predicate. -/
def boundedAlways_finish (c d : Clock) (b q m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) : Judgement Clock Var :=
  Judgement.predicate (.plain φ) ∧ⱼ
    Xⱼ (lty[m] ∧ⱼ
      (c >ᶜ[Marker.conj b (¬ₘ m)] (⟨I.lower, I.lower_nonnegative⟩ : NNReal)) ∧ⱼ
      (d >ᶜ[Marker.notConj q m]
        (⟨I.upper, I.lower_nonnegative.trans I.nonSingular.le⟩ : NNReal)))

/-- The five `↑↓` `□` schemas, with three marker schemas expanded
into two choices each. Correctness is proved separately. -/
def boundedAlways [DecidableEq Clock] (c d : Clock) (b q : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) : ExpansionRule Clock Var where
  source := ↑↓[c,d,b,q]□[I]φ
  branches := [
    boundedAlways_defer c d b q ○ I φ,
    boundedAlways_defer c d b q ● I φ,
    Xⱼ ((c ≤ᶜ (⟨I.lower, I.lower_nonnegative⟩ : NNReal)) ∧ⱼ ∗),
    Judgement.predicate (.plain φ) ∧ⱼ
      Xⱼ ((c >ᶜ (⟨I.lower, I.lower_nonnegative⟩ : NNReal)) ∧ⱼ ∗),
    boundedAlways_check c d b q ○ I φ,
    boundedAlways_check c d b q ● I φ,
    boundedAlways_finish c d b q ○ I φ,
    boundedAlways_finish c d b q ● I φ]
  branches_nonempty := by simp

@[simp] theorem boundedAlways_branch_count [DecidableEq Clock] (c d : Clock)
    (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var) :
    (boundedAlways c d b q I φ).branches.length = 8 := rfl

/-- `↑↓` `□` terminal waiting reuses `↑` `□` soundness and
the already proved `↑`-to-`↑↓` implication. -/
theorem boundedAlways_terminal_wait_sound (c d : Clock) (b q : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) :
    (Xⱼ ((c ≤ᶜ (⟨I.lower, I.lower_nonnegative⟩ : NNReal)) ∧ⱼ ∗)) ⇒ⱼ
      ((↑↓[c,d,b,q]□[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  intro σ P α k h
  exact Judgement.upper_always_implies_bounded c d b q I φ σ P α k
    (upperAlways_terminal_wait_sound c b I φ σ P α k h)

/-- `↑↓` `□` terminal checking also needs no extra invariant for soundness. -/
theorem boundedAlways_terminal_check_sound (c d : Clock) (b q : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) :
    (Judgement.predicate (.plain φ) ∧ⱼ
      Xⱼ ((c >ᶜ (⟨I.lower, I.lower_nonnegative⟩ : NNReal)) ∧ⱼ ∗)) ⇒ⱼ
      ((↑↓[c,d,b,q]□[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  intro σ P α k h
  exact Judgement.upper_always_implies_bounded c d b q I φ σ P α k
    (upperAlways_terminal_check_sound c b I φ σ P α k h)

/-- `↑↓` `□` defer soundness. No reset or clock-distinctness condition
is needed, since both clocks simply advance by the current duration. -/
theorem boundedAlways_defer_sound (c d : Clock) (b q m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) :
    boundedAlways_defer c d b q m I φ ⇒ⱼ
      ((↑↓[c,d,b,q]□[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  intro σ P α k h
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · let i : Fin P.size := ⟨k.1, hk⟩
      let j : Fin P.size := ⟨k.1 + 1, hn⟩
      let β := ClockResetSet.elapse α (Judgement.duration P i)
      have hc : (P.interval i).left - (α c : ℝ) =
          (P.interval j).left - (β c : ℝ) :=
        (Judgement.next_left_sub_elapse_eq P α i hn c).symm
      have hd : (P.interval i).left - (α d : ℝ) =
          (P.interval j).left - (β d : ℝ) :=
        (Judgement.next_left_sub_elapse_eq P α i hn d).symm
      simp only [boundedAlways_defer, Judgement.Satisfies, dif_pos hk, dif_pos hn] at h ⊢
      have hmarker : (P.interval j).leftBoundary = m := h.1
      have hg : (β c : ℝ) <[Marker.imp b (P.interval j).leftBoundary] I.lower := by
        rw [hmarker]
        exact (Judgement.satisfies_markedLT σ P β ⟨k.1 + 1, by omega⟩ c
          (Marker.imp b m) ⟨I.lower, I.lower_nonnegative⟩).1 h.2.1
      exact IntervalPredicate.satisfies_bounded_always_of_next_of_guard
        σ (P.interval i) (P.interval j) α β c d b q I φ hc hd hg h.2.2
    · simp [boundedAlways_defer, Judgement.Satisfies, hk, hn] at h
  · simp [boundedAlways_defer, Judgement.Satisfies, hk] at h

/-- The finish guard excludes every checking point in the next suffix.
Soundness needs neither stability nor an invariant, including at termination. -/
theorem boundedAlways_finish_sound (c d : Clock) (b q m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) :
    boundedAlways_finish c d b q m I φ ⇒ⱼ
      ((↑↓[c,d,b,q]□[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  intro σ P α k h
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · let i : Fin P.size := ⟨k.1, hk⟩
      let j : Fin P.size := ⟨k.1 + 1, hn⟩
      let β := ClockResetSet.elapse α (Judgement.duration P i)
      have hc : (P.interval i).left - (α c : ℝ) =
          (P.interval j).left - (β c : ℝ) :=
        (Judgement.next_left_sub_elapse_eq P α i hn c).symm
      have hd : (P.interval i).left - (α d : ℝ) =
          (P.interval j).left - (β d : ℝ) :=
        (Judgement.next_left_sub_elapse_eq P α i hn d).symm
      simp only [boundedAlways_finish, Judgement.Satisfies, dif_pos hk, dif_pos hn] at h ⊢
      have hmarker : (P.interval j).leftBoundary = m := h.2.1
      have hg : I.upper <[Marker.notConj q (P.interval j).leftBoundary] (β d : ℝ) := by
        rw [hmarker]
        exact (Judgement.satisfies_markedGT σ P β ⟨k.1 + 1, by omega⟩ d
          (Marker.notConj q m) ⟨I.upper, I.lower_nonnegative.trans I.nonSingular.le⟩).1 h.2.2.2
      intro t ht hs
      rcases IntervalPredicate.mem_or_inCurrentSuffix_of_adjacent (P.interval i) (P.interval j)
          (P.adjacent_right_eq_left i hn)
          (P.adjacent_rightBoundary_eq_complement_leftBoundary i hn) hs with htJ | htK
      · exact h.1 t htJ
      · apply False.elim
        apply IntervalPredicate.not_mem_alwaysRegion_of_finish_guard
          (P.interval j) β c d b q I φ hg htK
        change (t : ℝ) ∈ IntervalPredicate.alwaysRegion
          (IntervalPredicate.scope (P.interval i) α (↑↓[c,d,b,q]□[I]φ)) I at ht
        simpa only [IntervalPredicate.scope, hc, hd] using ht
    · have hlast : k.1 + 1 = P.size := by omega
      simp only [boundedAlways_finish, Judgement.Satisfies, dif_pos hk, dif_neg hn] at h ⊢
      intro t _ hs
      exact h.1 t (P.mem_last_of_left_condition ⟨k.1, hk⟩ hlast t.2 hs)
  · simp [boundedAlways_finish, Judgement.Satisfies, hk] at h

/-- Checking the current piece and resetting the left clock covers every
remaining checking point. Only reset-clock freshness is required. -/
theorem boundedAlways_check_sound [DecidableEq Clock] (c d : Clock) (b q m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) (hcd : c ≠ d) :
    boundedAlways_check c d b q m I φ ⇒ⱼ
      ((↑↓[c,d,b,q]□[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  intro σ P α k h
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
      simp only [boundedAlways_check, Judgement.Satisfies, dif_pos hk, dif_pos hn] at h ⊢
      have hmarker : (P.interval j).leftBoundary = m := h.2.2.2.2
      have hnext : (σ,P.interval j,β)⊨ᵢ(↑↓[c,d,m,q]□[I]φ) := h.2.2.2.1
      intro t ht hs
      rcases IntervalPredicate.mem_or_inCurrentSuffix_of_adjacent
          (P.interval i) (P.interval j) (P.adjacent_right_eq_left i hn)
          (P.adjacent_rightBoundary_eq_complement_leftBoundary i hn) hs with htJ | htK
      · exact h.1 t htJ
      · apply hnext t _ htK
        change ((P.interval j).left - (β c : ℝ) + I.lower < t.1 ∨
            ((P.interval j).left - (β c : ℝ) + I.lower = t.1 ∧ m.Includes)) ∧
          (t.1 < (P.interval j).left - (β d : ℝ) + I.upper ∨
            (t.1 = (P.interval j).left - (β d : ℝ) + I.upper ∧ q.Includes))
        constructor
        · rw [hβc]
          change ((P.interval j).left - I.lower + I.lower < t.1 ∨
            ((P.interval j).left - I.lower + I.lower = t.1 ∧ m.Includes))
          simpa only [sub_add_cancel, IntervalPredicate.InCurrentSuffix, hmarker] using htK
        · rw [← hd]
          exact ht.2
    · simp [boundedAlways_check, Judgement.Satisfies, hk, hn] at h
  · simp [boundedAlways_check, Judgement.Satisfies, hk] at h

/-- All eight concrete `↑↓` `□` branches (five manuscript schemas) are
sound under reset-clock freshness, without stability or invariant hypotheses. -/
theorem boundedAlways_sound_at [DecidableEq Clock] (c d : Clock) (b q : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) (hcd : c ≠ d)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (h : (boundedAlways c d b q I φ).BranchSatisfied σ P α k) :
    (σ,P,α,k)⊨ⱼ((boundedAlways c d b q I φ).source : Judgement Clock Var) := by
  obtain ⟨B, hB, h⟩ := h
  simp only [boundedAlways, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact boundedAlways_defer_sound c d b q ○ I φ σ P α k h
  · exact boundedAlways_defer_sound c d b q ● I φ σ P α k h
  · exact boundedAlways_terminal_wait_sound c d b q I φ σ P α k h
  · exact boundedAlways_terminal_check_sound c d b q I φ σ P α k h
  · exact boundedAlways_check_sound c d b q ○ I φ hcd σ P α k h
  · exact boundedAlways_check_sound c d b q ● I φ hcd σ P α k h
  · exact boundedAlways_finish_sound c d b q ○ I φ σ P α k h
  · exact boundedAlways_finish_sound c d b q ● I φ σ P α k h

/-- Under the defer guard, `↑↓` `□` satisfaction supplies a defer
branch without any stability assumption. -/
theorem boundedAlways_defer_complete_at [DecidableEq Clock]
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size)
    (hg : (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩) c : ℝ)
      <[Marker.imp b (P.interval ⟨k.1 + 1, hn⟩).leftBoundary] I.lower)
    (h : (σ,P,α,k)⊨ⱼ((boundedAlways c d b q I φ).source : Judgement Clock Var)) :
    (boundedAlways c d b q I φ).BranchSatisfied σ P α k := by
  have hk : k.1 < P.size := by omega
  let β := ClockResetSet.elapse α (Judgement.duration P ⟨k.1, hk⟩)
  let m := (P.interval ⟨k.1 + 1, hn⟩).leftBoundary
  have hnext := Judgement.satisfies_next_bounded_always_of_current_at
    σ P α k hn c d b q I φ h
  have hguard : (σ,P,β,⟨k.1 + 1, by omega⟩)⊨ⱼ
      (c <ᶜ[Marker.imp b m] (⟨I.lower, I.lower_nonnegative⟩ : NNReal)) :=
    (Judgement.satisfies_markedLT _ _ _ _ _ _ _).2 hg
  refine ⟨boundedAlways_defer c d b q m I φ, ?_, ?_⟩
  · cases m <;> simp [boundedAlways]
  · simp only [boundedAlways_defer, Judgement.Satisfies, dif_pos hk, dif_pos hn] at hnext ⊢
    exact ⟨rfl, hguard, hnext⟩

/-- Conditional completeness of check/reset. The current unclocked obligation
is explicit here; deriving it from stability and the invariant is separate. -/
theorem boundedAlways_check_complete_of_plain [DecidableEq Clock]
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size)
    (hg : I.lower <[Marker.conj b (¬ₘ (P.interval ⟨k.1 + 1, hn⟩).leftBoundary)]
      (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩) c : ℝ))
    (hdg : (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩) d : ℝ)
      <[Marker.conj q (P.interval ⟨k.1 + 1, hn⟩).leftBoundary] I.upper)
    (hφ : (σ,P,α,k)⊨ⱼ(Judgement.predicate (.plain φ)))
    (h : (σ,P,α,k)⊨ⱼ((boundedAlways c d b q I φ).source : Judgement Clock Var)) :
    (boundedAlways c d b q I φ).BranchSatisfied σ P α k := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let j : Fin P.size := ⟨k.1 + 1, hn⟩
  let m := (P.interval j).leftBoundary
  let a : NNReal := ⟨I.lower, I.lower_nonnegative⟩
  let γ := ClockResetSet.elapse α (Judgement.duration P i)
  let β := (⟦c ↦ᶜ a⟧).apply γ
  have hβc : β c = a := ClockResetSet.apply_singleton_self c a γ
  have hβd : β d = γ d := ClockResetSet.apply_singleton_of_ne a γ hcd.symm
  have hd : (P.interval i).left - (α d : ℝ) =
      (P.interval j).left - (β d : ℝ) := by
    rw [hβd]
    exact (Judgement.next_left_sub_elapse_eq P α i hn d).symm
  have hadj : (P.interval i).right = (P.interval j).left :=
    P.adjacent_right_eq_left i hn
  have hcut : (P.interval i).left - (α c : ℝ) + I.lower
      <[Marker.conj b (¬ₘ m)] (P.interval j).left := by
    change I.lower <[Marker.conj b (¬ₘ m)]
      ((α c : ℝ) + ((P.interval i).right - (P.interval i).left)) at hg
    rcases hg with hlt | ⟨heq, hb⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, hb⟩
  have hU : (σ,P.interval i,α)⊨ᵢ(↑↓[c,d,b,q]□[I]φ) := by
    simpa only [boundedAlways, Judgement.Satisfies, dif_pos hk] using h
  have hnext : (σ,P.interval j,β)⊨ᵢ(↑↓[c,d,m,q]□[I]φ) := by
    intro t ht hs
    apply hU t
    · have htl : (P.interval j).left ≤ t.1 := hs.elim le_of_lt (fun h => h.1.le)
      constructor
      · rcases hcut with hlt | ⟨heq, hb⟩
        · exact Or.inl (hlt.trans_le htl)
        · rcases htl.lt_or_eq with hlt | heq'
          · exact Or.inl (heq.trans_lt hlt)
          · exact Or.inr ⟨heq.trans heq', ((Marker.includes_conj _ _).1 hb).1⟩
      · have hr : t.1 < (P.interval j).left - (β d : ℝ) + I.upper ∨
            (t.1 = (P.interval j).left - (β d : ℝ) + I.upper ∧ q.Includes) := ht.2
        rw [← hd] at hr
        exact hr
    · exact IntervalPredicate.inCurrentSuffix_of_adjacent
        (P.interval i) (P.interval j) (P.nonempty i) hadj hs
  have hguard : (σ,P,γ,⟨k.1 + 1, by omega⟩)⊨ⱼ(c >ᶜ[Marker.conj b (¬ₘ m)] a) :=
    (Judgement.satisfies_markedGT _ _ _ _ _ _ _).2 hg
  have hdguard : (σ,P,γ,⟨k.1 + 1, by omega⟩)⊨ⱼ
      (d <ᶜ[Marker.conj q m] (⟨I.upper, I.lower_nonnegative.trans I.nonSingular.le⟩ : NNReal)) :=
    (Judgement.satisfies_markedLT _ _ _ _ _ _ _).2 hdg
  refine ⟨boundedAlways_check c d b q m I φ, ?_, ?_⟩
  · cases m <;> simp [boundedAlways]
  · simp only [boundedAlways_check, Judgement.Satisfies, dif_pos hk, dif_pos hn] at hφ ⊢
    exact ⟨hφ, hguard, hdguard, hnext, rfl⟩

/-- Conditional finish completeness: current checking and both finish
guards directly provide the branch at the actual next marker. -/
theorem boundedAlways_finish_complete_of_plain [DecidableEq Clock]
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size)
    (hg : I.lower <[Marker.conj b (¬ₘ (P.interval ⟨k.1 + 1, hn⟩).leftBoundary)]
      (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩) c : ℝ))
    (hdg : I.upper <[Marker.notConj q (P.interval ⟨k.1 + 1, hn⟩).leftBoundary]
      (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩) d : ℝ))
    (hφ : (σ,P,α,k)⊨ⱼ(Judgement.predicate (.plain φ))) :
    (boundedAlways c d b q I φ).BranchSatisfied σ P α k := by
  have hk : k.1 < P.size := by omega
  let γ := ClockResetSet.elapse α (Judgement.duration P ⟨k.1, hk⟩)
  let m := (P.interval ⟨k.1 + 1, hn⟩).leftBoundary
  have hguard : (σ,P,γ,⟨k.1 + 1, by omega⟩)⊨ⱼ
      (c >ᶜ[Marker.conj b (¬ₘ m)] (⟨I.lower, I.lower_nonnegative⟩ : NNReal)) :=
    (Judgement.satisfies_markedGT _ _ _ _ _ _ _).2 hg
  have hdguard : (σ,P,γ,⟨k.1 + 1, by omega⟩)⊨ⱼ
      (d >ᶜ[Marker.notConj q m] (⟨I.upper, I.lower_nonnegative.trans I.nonSingular.le⟩ : NNReal)) :=
    (Judgement.satisfies_markedGT _ _ _ _ _ _ _).2 hdg
  refine ⟨boundedAlways_finish c d b q m I φ, ?_, ?_⟩
  · cases m <;> simp [boundedAlways]
  · simp only [boundedAlways_finish, Judgement.Satisfies, dif_pos hk, dif_pos hn] at hφ ⊢
    exact ⟨hφ, rfl, hguard, hdguard⟩

/-- With a next interval, stability and the predicate invariant suffice
for `↑↓` `□` completeness. No separate unclocked obligation is assumed. -/
theorem boundedAlways_complete_at_next [DecidableEq Clock]
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size)
    (hinv : IntervalPredicate.Invariant (P.interval ⟨k.1, by omega⟩) α (↑↓[c,d,b,q]□[I]φ))
    (hs : σ.StablePartition (□[(I : TimeInterval)] φ) P)
    (h : (σ,P,α,k)⊨ⱼ((boundedAlways c d b q I φ).source : Judgement Clock Var)) :
    (boundedAlways c d b q I φ).BranchSatisfied σ P α k := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let j : Fin P.size := ⟨k.1 + 1, hn⟩
  let m := (P.interval j).leftBoundary
  let γ := ClockResetSet.elapse α (Judgement.duration P i)
  by_cases hg : (γ c : ℝ) <[Marker.imp b m] I.lower
  · exact boundedAlways_defer_complete_at c d b q I φ σ P α k hn hg h
  · have hcheck : I.lower <[Marker.conj b (¬ₘ m)] (γ c : ℝ) := by
      by_contra hc
      exact hg ((Judgement.upperAlways_guard_complement _ _ _ _).2 hc)
    have hm : (P.interval i).rightBoundary = Marker.complement m :=
      P.adjacent_rightBoundary_eq_complement_leftBoundary i hn
    have hcut : (P.interval i).left - (α c : ℝ) + I.lower
        <[Marker.conj b (P.interval i).rightBoundary] (P.interval i).right := by
      rw [hm]
      change I.lower <[Marker.conj b (¬ₘ m)]
        ((α c : ℝ) + ((P.interval i).right - (P.interval i).left)) at hcheck
      rcases hcheck with hlt | ⟨heq, hb⟩
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, hb⟩
    have hDomain : (P.interval i).carrier ⊆ σ.domain := by
      intro t ht
      rw [← P.covers]
      exact Set.mem_iUnion.2 ⟨i, ht⟩
    have hU : (σ,P.interval i,α)⊨ᵢ(↑↓[c,d,b,q]□[I]φ) := by
      simpa only [boundedAlways, Judgement.Satisfies, dif_pos hk] using h
    have hplain := IntervalPredicate.satisfies_plain_of_bounded_always_of_marked_overlap
      σ (P.interval i) α c d b q I φ (P.nonempty i) hDomain hcut hinv
      (hs i φ (.neg (.until_right (.neg (.refl φ))))) hU
    have hφ : (σ,P,α,k)⊨ⱼ(Judgement.predicate (.plain φ)) := by
      simpa only [Judgement.Satisfies, dif_pos hk] using hplain
    by_cases hdg : (γ d : ℝ) <[Marker.conj q m] I.upper
    · exact boundedAlways_check_complete_of_plain c d b q I φ hcd σ P α k hn hcheck hdg hφ h
    · have hfinish : I.upper <[Marker.notConj q m] (γ d : ℝ) := by
        by_contra hf
        exact hdg ((Judgement.boundedAlways_right_guard_complement _ _ _ _).2 hf)
      exact boundedAlways_finish_complete_of_plain c d b q I φ σ P α k hn hcheck hfinish hφ

/-- At the last interval, the two terminal branches suffice. Clock
distinctness is unnecessary because neither branch resets a clock. -/
theorem boundedAlways_complete_at_last [DecidableEq Clock]
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hlast : k.1 + 1 = P.size)
    (hinv : IntervalPredicate.Invariant (P.interval ⟨k.1, by omega⟩) α (↑↓[c,d,b,q]□[I]φ))
    (hs : σ.StablePartition (□[(I : TimeInterval)] φ) P)
    (h : (σ,P,α,k)⊨ⱼ((boundedAlways c d b q I φ).source : Judgement Clock Var)) :
    (boundedAlways c d b q I φ).BranchSatisfied σ P α k := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let a : NNReal := ⟨I.lower, I.lower_nonnegative⟩
  let γ := ClockResetSet.elapse α (Judgement.duration P i)
  by_cases hle : γ c ≤ a
  · refine ⟨Xⱼ ((c ≤ᶜ a) ∧ⱼ ∗), by simp [boundedAlways, a], ?_⟩
    simp only [Judgement.Satisfies, dif_pos hk]
    exact ⟨hle, hlast⟩
  · have hgt : a < γ c := lt_of_not_ge hle
    have hg : I.lower < (α c : ℝ) +
        ((P.interval i).right - (P.interval i).left) := hgt
    have hDomain : (P.interval i).carrier ⊆ σ.domain := by
      intro t ht
      rw [← P.covers]
      exact Set.mem_iUnion.2 ⟨i, ht⟩
    have hφ : (σ,P.interval i,α)⊨ᵢ(.plain φ) := by
      apply IntervalPredicate.satisfies_plain_of_bounded_always_of_marked_overlap
        σ (P.interval i) α c d b q I φ (P.nonempty i) hDomain
        (Or.inl (by linarith)) hinv
        (hs i φ (.neg (.until_right (.neg (.refl φ)))))
      simpa only [boundedAlways, Judgement.Satisfies, dif_pos hk] using h
    refine ⟨Judgement.predicate (.plain φ) ∧ⱼ Xⱼ ((c >ᶜ a) ∧ⱼ ∗),
      by simp [boundedAlways, a], ?_⟩
    simp only [Judgement.Satisfies, dif_pos hk]
    exact ⟨hφ, hgt, hlast⟩

/-- Full `↑↓` `□` completeness. The invariant is required only at
a declaring position, so this statement also covers the terminal position. -/
theorem boundedAlways_complete_at [DecidableEq Clock]
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hinv : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α (↑↓[c,d,b,q]□[I]φ))
    (hs : σ.StablePartition (□[(I : TimeInterval)] φ) P)
    (h : (σ,P,α,k)⊨ⱼ((boundedAlways c d b q I φ).source : Judgement Clock Var)) :
    (boundedAlways c d b q I φ).BranchSatisfied σ P α k := by
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · exact boundedAlways_complete_at_next c d b q I φ hcd σ P α k hn (hinv hk) hs h
    · exact boundedAlways_complete_at_last c d b q I φ σ P α k (by omega) (hinv hk) hs h
  · simp [Judgement.Satisfies, hk] at h

/-- Correctness of all five `↑↓` `□` continuation schemas under
the invariant, full stability, and reset-clock freshness. -/
theorem boundedAlways_correct_at [DecidableEq Clock]
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hinv : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α (↑↓[c,d,b,q]□[I]φ))
    (hs : σ.StablePartition (□[(I : TimeInterval)] φ) P) :
    ((σ,P,α,k)⊨ⱼ((boundedAlways c d b q I φ).source : Judgement Clock Var)) ↔
      (boundedAlways c d b q I φ).BranchSatisfied σ P α k :=
  ⟨boundedAlways_complete_at c d b q I φ hcd σ P α k hinv hs,
    boundedAlways_sound_at c d b q I φ hcd σ P α k⟩

/-- `RuleFinallyUpDownBranchOne`: defer the `↑↓` `◇`. -/
def boundedEventually_defer (c d : Clock) (b q m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) : Judgement Clock Var :=
  Xⱼ (lty[m] ∧ⱼ
    (c <ᶜ[Marker.imp b m] (⟨I.upper, I.lower_nonnegative.trans I.nonSingular.le⟩ : NNReal)) ∧ⱼ
    (↑↓[c,d,b,q]◇[I]φ : IntervalPredicate Clock Var))

/-- `RuleFinallyUpDownBranchTwo`: discharge current witnesses and reset
the left clock for the remaining scope. -/
def boundedEventually_check [DecidableEq Clock] (c d : Clock) (b q m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) : Judgement Clock Var :=
  let a : NNReal := ⟨I.lower, I.lower_nonnegative⟩
  Judgement.predicate (.plain φ) ∧ⱼ
    Xⱼ ((c >ᶜ[Marker.conj b (¬ₘ m)] a) ∧ⱼ
      (d <ᶜ[Marker.conj q m] a) ∧ⱼ
      (⟦c ↦ᶜ a⟧ ·ⱼ ((↑↓[c,d,m,q]◇[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[m])))

/-- `RuleFinallyUpDownBranchThree`: all remaining witnesses are current. -/
def boundedEventually_finish (d : Clock) (q m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) : Judgement Clock Var :=
  Judgement.predicate (.plain φ) ∧ⱼ
    Xⱼ ((d >ᶜ[Marker.notConj q m] (⟨I.lower, I.lower_nonnegative⟩ : NNReal)) ∧ⱼ lty[m])

/-- The three `↑↓` `◇` schemas, enumerating both marker choices.
The finish schema precedes check/reset as in the displayed rule. -/
def boundedEventually [DecidableEq Clock] (c d : Clock) (b q : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) : ExpansionRule Clock Var where
  source := ↑↓[c,d,b,q]◇[I]φ
  branches := [boundedEventually_defer c d b q ○ I φ,
    boundedEventually_defer c d b q ● I φ,
    boundedEventually_finish d q ○ I φ,
    boundedEventually_finish d q ● I φ,
    boundedEventually_check c d b q ○ I φ,
    boundedEventually_check c d b q ● I φ]
  branches_nonempty := by simp

@[simp] theorem boundedEventually_branch_count [DecidableEq Clock]
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var) :
    (boundedEventually c d b q I φ).branches.length = 6 := rfl

/-- Defer soundness reuses the unconditional eventuality transition.
The guard is not needed in this direction, nor is stability or an invariant. -/
theorem boundedEventually_defer_sound (c d : Clock) (b q m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) :
    boundedEventually_defer c d b q m I φ ⇒ⱼ
      ((↑↓[c,d,b,q]◇[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  intro σ P α k h
  apply Judgement.next_bounded_eventually_implies_bounded c d b q I φ σ P α k
  by_cases hk : k.1 < P.size
  · simp only [boundedEventually_defer, Judgement.Satisfies, dif_pos hk] at h ⊢
    exact h.2.2
  · simp [boundedEventually_defer, Judgement.Satisfies, hk] at h

/-- Finish soundness at consecutive intervals, using the predicate invariant
to obtain witnesses in the current piece. No stability or freshness is needed. -/
theorem boundedEventually_finish_sound_at_next
    (c d : Clock) (b q m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size)
    (hinv : IntervalPredicate.Invariant (P.interval ⟨k.1, by omega⟩) α (↑↓[c,d,b,q]◇[I]φ))
    (h : (σ,P,α,k)⊨ⱼ(boundedEventually_finish d q m I φ)) :
    (σ,P,α,k)⊨ⱼ((↑↓[c,d,b,q]◇[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let j : Fin P.size := ⟨k.1 + 1, hn⟩
  let γ := ClockResetSet.elapse α (Judgement.duration P i)
  simp only [boundedEventually_finish, Judgement.Satisfies, dif_pos hk, dif_pos hn] at h ⊢
  have hmarker : (P.interval j).leftBoundary = m := h.2.2
  have hm : (P.interval i).rightBoundary = ¬ₘ m :=
    (P.adjacent_rightBoundary_eq_complement_leftBoundary i hn).trans
      (congrArg Marker.complement hmarker)
  have hg : I.lower <[Marker.notConj q m] (γ d : ℝ) :=
    (Judgement.satisfies_markedGT σ P γ ⟨k.1 + 1, by omega⟩ d
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
  exact IntervalPredicate.satisfies_bounded_eventually_of_plain_of_finish
    σ (P.interval i) α c d b q I φ (P.nonempty i) hDomain hinv hguard h.1

/-- At the last interval the next marker is closed, and the current right
marker is open; the same witness-intersection argument still applies. -/
theorem boundedEventually_finish_sound_at_last
    (c d : Clock) (b q m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hlast : k.1 + 1 = P.size)
    (hinv : IntervalPredicate.Invariant (P.interval ⟨k.1, by omega⟩) α (↑↓[c,d,b,q]◇[I]φ))
    (h : (σ,P,α,k)⊨ⱼ(boundedEventually_finish d q m I φ)) :
    (σ,P,α,k)⊨ⱼ((↑↓[c,d,b,q]◇[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  have hk : k.1 < P.size := by omega
  have hn : ¬k.1 + 1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let γ := ClockResetSet.elapse α (Judgement.duration P i)
  simp only [boundedEventually_finish, Judgement.Satisfies, dif_pos hk, dif_neg hn] at h ⊢
  have hmarker : m = ● := h.2.2
  have hg : I.lower <[Marker.notConj q m] (γ d : ℝ) :=
    (Judgement.satisfies_markedGT σ P γ ⟨k.1 + 1, by omega⟩ d
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
  exact IntervalPredicate.satisfies_bounded_eventually_of_plain_of_finish
    σ (P.interval i) α c d b q I φ (P.nonempty i) hDomain hinv hguard h.1

/-- Finish soundness at every position under the eventuality invariant.
No stability or clock-distinctness assumption is required. -/
theorem boundedEventually_finish_sound_at
    (c d : Clock) (b q m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hinv : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α (↑↓[c,d,b,q]◇[I]φ))
    (h : (σ,P,α,k)⊨ⱼ(boundedEventually_finish d q m I φ)) :
    (σ,P,α,k)⊨ⱼ((↑↓[c,d,b,q]◇[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · exact boundedEventually_finish_sound_at_next c d b q m I φ σ P α k hn (hinv hk) h
    · exact boundedEventually_finish_sound_at_last c d b q m I φ σ P α k (by omega) (hinv hk) h
  · simp [boundedEventually_finish, Judgement.Satisfies, hk] at h

/-- Check/reset soundness splits the scope into current-witness points and
points retained by the reset predicate. The invariant supplies current
witnesses; clock freshness preserves the remaining scope's right endpoint. -/
theorem boundedEventually_check_sound_at [DecidableEq Clock]
    (c d : Clock) (b q m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hinv : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α (↑↓[c,d,b,q]◇[I]φ))
    (h : (σ,P,α,k)⊨ⱼ(boundedEventually_check c d b q m I φ)) :
    (σ,P,α,k)⊨ⱼ((↑↓[c,d,b,q]◇[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
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
      simp only [boundedEventually_check, Judgement.Satisfies, dif_pos hk, dif_pos hn] at h ⊢
      have hmarker : (P.interval j).leftBoundary = m := h.2.2.2.2
      have hm : (P.interval i).rightBoundary = ¬ₘ m :=
        (P.adjacent_rightBoundary_eq_complement_leftBoundary i hn).trans
          (congrArg Marker.complement hmarker)
      have hnext : (σ,P.interval j,β)⊨ᵢ(↑↓[c,d,m,q]◇[I]φ) := h.2.2.2.1
      have hDomain : (P.interval i).carrier ⊆ σ.domain := by
        intro t ht
        rw [← P.covers]
        exact Set.mem_iUnion.2 ⟨i, ht⟩
      intro t ht
      by_cases hcut : t + I.lower <[(P.interval i).rightBoundary] (P.interval i).right
      · exact IntervalPredicate.exists_current_witness_of_bounded_eventually_invariant
          σ (P.interval i) α c d b q I φ (P.nonempty i) hDomain (hinv hk) h.1 t ht hcut
      · have htNext : t ∈ IntervalPredicate.scope (P.interval j) β (↑↓[c,d,m,q]◇[I]φ) := by
          constructor
          · change ((P.interval j).left - (β c : ℝ)) <[m] t
            rw [hβc, ← hadj]
            apply (Judgement.not_markedLT_add_complement_iff t I.lower _ m).1
            simpa only [hm] using hcut
          · change t < (P.interval j).left - (β d : ℝ) ∨
              (t = (P.interval j).left - (β d : ℝ) ∧ q.Includes)
            rw [← hd]
            exact ht.2
        obtain ⟨u, hu, hs, hφ⟩ := hnext t htNext
        exact ⟨u, hu, IntervalPredicate.inCurrentSuffix_of_adjacent
          (P.interval i) (P.interval j) (P.nonempty i) hadj hs, hφ⟩
    · simp [boundedEventually_check, Judgement.Satisfies, hk, hn] at h
  · simp [boundedEventually_check, Judgement.Satisfies, hk] at h

/-- Soundness of all three `↑↓` `◇` schemas (six concrete
branches), under the source invariant and reset-clock freshness. -/
theorem boundedEventually_sound_at [DecidableEq Clock]
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hinv : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α (↑↓[c,d,b,q]◇[I]φ))
    (h : (boundedEventually c d b q I φ).BranchSatisfied σ P α k) :
    (σ,P,α,k)⊨ⱼ((boundedEventually c d b q I φ).source : Judgement Clock Var) := by
  obtain ⟨B, hB, h⟩ := h
  simp only [boundedEventually, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl
  · exact boundedEventually_defer_sound c d b q ○ I φ σ P α k h
  · exact boundedEventually_defer_sound c d b q ● I φ σ P α k h
  · exact boundedEventually_finish_sound_at c d b q ○ I φ σ P α k hinv h
  · exact boundedEventually_finish_sound_at c d b q ● I φ σ P α k hinv h
  · exact boundedEventually_check_sound_at c d b q ○ I φ hcd σ P α k hinv h
  · exact boundedEventually_check_sound_at c d b q ● I φ hcd σ P α k hinv h

/-- At the last interval every witness is current, so stability gives the
unclocked obligation and scope containment forces the finish guard. -/
theorem boundedEventually_complete_at_last [DecidableEq Clock]
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hlast : k.1 + 1 = P.size)
    (hinv : IntervalPredicate.Invariant (P.interval ⟨k.1, by omega⟩) α (↑↓[c,d,b,q]◇[I]φ))
    (hs : σ.StablePartition (◇[(I : TimeInterval)] φ) P)
    (h : (σ,P,α,k)⊨ⱼ((boundedEventually c d b q I φ).source : Judgement Clock Var)) :
    (boundedEventually c d b q I φ).BranchSatisfied σ P α k := by
  have hk : k.1 < P.size := by omega
  have hn : ¬k.1 + 1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let γ := ClockResetSet.elapse α (Judgement.duration P i)
  let S := (IntervalPredicate.scope (P.interval i) α (↑↓[c,d,b,q]◇[I]φ)).toMarkedInterval
  have hS : S.carrier.Nonempty :=
    IntervalPredicate.bounded_eventually_scope_nonempty_of_invariant
      (P.interval i) α c d b q I φ hinv
  have hU : (σ,P.interval i,α)⊨ᵢ(↑↓[c,d,b,q]◇[I]φ) := by
    simpa only [boundedEventually, Judgement.Satisfies, dif_pos hk] using h
  have hSne := hS
  obtain ⟨t, ht⟩ := hS
  obtain ⟨u, _, hu, huφ⟩ := hU t ht
  have huJ := P.mem_last_of_left_condition i hlast u.2 hu
  have hφ : (σ,P.interval i,α)⊨ᵢ(.plain φ) := by
    intro v hv
    exact (hs i φ (.until_right (.refl φ)) u v huJ hv).1 huφ
  let K : MarkedInterval := ⟨S.left, (P.interval i).right - I.lower, b, ○⟩
  have hsub : S.carrier ⊆ K.carrier := by
    intro t ht
    obtain ⟨u, huI, hu, _⟩ := hU t ht
    have hur := P.lt_right_of_mem_last i hlast (P.mem_last_of_left_condition i hlast u.2 hu)
    have hlo : I.lower ≤ u.1 - t := huI.1
    exact ⟨ht.1, Or.inl (by change t < (P.interval i).right - I.lower; linarith)⟩
  have hr := ((MarkedInterval.subset_iff hSne).1 hsub).2
  have hg : I.lower <[Marker.notConj q ●] (γ d : ℝ) := by
    change (P.interval i).left - (α d : ℝ) <[Marker.imp q ○]
      (P.interval i).right - I.lower at hr
    change I.lower <[Marker.notConj q ●]
      ((α d : ℝ) + ((P.interval i).right - (P.interval i).left))
    have hm : Marker.imp q ○ = Marker.notConj q ● := by cases q <;> rfl
    rw [hm] at hr
    rcases hr with hlt | ⟨heq, hm⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, hm⟩
  have hguard : (σ,P,γ,⟨k.1 + 1, by omega⟩)⊨ⱼ
      (d >ᶜ[Marker.notConj q ●] (⟨I.lower, I.lower_nonnegative⟩ : NNReal)) :=
    (Judgement.satisfies_markedGT _ _ _ _ _ _ _).2 hg
  refine ⟨boundedEventually_finish d q ● I φ, by simp [boundedEventually], ?_⟩
  simp only [boundedEventually_finish, Judgement.Satisfies, dif_pos hk, dif_neg hn]
  exact ⟨hφ, hguard, trivial⟩

/-- If the current stable piece does not satisfy the operand, all witnesses
lie in the next suffix. Scope containment also derives the defer guard. -/
theorem boundedEventually_defer_complete_of_not_plain [DecidableEq Clock]
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size)
    (hinv : IntervalPredicate.Invariant (P.interval ⟨k.1, by omega⟩) α (↑↓[c,d,b,q]◇[I]φ))
    (hs : σ.StablePartition (◇[(I : TimeInterval)] φ) P)
    (hnot : ¬(σ,P,α,k)⊨ⱼ(Judgement.predicate (.plain φ)))
    (h : (σ,P,α,k)⊨ⱼ((boundedEventually c d b q I φ).source : Judgement Clock Var)) :
    (boundedEventually c d b q I φ).BranchSatisfied σ P α k := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let j : Fin P.size := ⟨k.1 + 1, hn⟩
  let m := (P.interval j).leftBoundary
  let γ := ClockResetSet.elapse α (Judgement.duration P i)
  let S := (IntervalPredicate.scope (P.interval i) α (↑↓[c,d,b,q]◇[I]φ)).toMarkedInterval
  have hS : S.carrier.Nonempty :=
    IntervalPredicate.bounded_eventually_scope_nonempty_of_invariant
      (P.interval i) α c d b q I φ hinv
  have hU : (σ,P.interval i,α)⊨ᵢ(↑↓[c,d,b,q]◇[I]φ) := by
    simpa only [boundedEventually, Judgement.Satisfies, dif_pos hk] using h
  have hnone : ∀ u : σ.Time, u.1 ∈ P.interval i → ¬(σ,u)⊨φ := by
    intro u hu hφ
    apply hnot
    simp only [Judgement.Satisfies, dif_pos hk]
    intro v hv
    exact (hs i φ (.until_right (.refl φ)) u v hu hv).1 hφ
  have hwitness : ∀ t ∈ S, ∃ u : σ.Time,
      u.1 ∈ (I : TimeInterval).translate t ∧
      IntervalPredicate.InCurrentSuffix (P.interval j) u.1 ∧ (σ,u)⊨φ := by
    intro t ht
    obtain ⟨u, huI, hu, hφ⟩ := hU t ht
    rcases IntervalPredicate.mem_or_inCurrentSuffix_of_adjacent (P.interval i) (P.interval j)
        (P.adjacent_right_eq_left i hn)
        (P.adjacent_rightBoundary_eq_complement_leftBoundary i hn) hu with huJ | huK
    · exact (hnone u huJ hφ).elim
    · exact ⟨u, huI, huK, hφ⟩
  have hc : (P.interval j).left - (γ c : ℝ) = (P.interval i).left - (α c : ℝ) :=
    Judgement.next_left_sub_elapse_eq P α i hn c
  have hd : (P.interval j).left - (γ d : ℝ) = (P.interval i).left - (α d : ℝ) :=
    Judgement.next_left_sub_elapse_eq P α i hn d
  have hnext : (σ,P.interval j,γ)⊨ᵢ(↑↓[c,d,b,q]◇[I]φ) := by
    intro t ht
    apply hwitness t
    change t ∈ (IntervalPredicate.scope (P.interval i) α (↑↓[c,d,b,q]◇[I]φ)).toMarkedInterval
    change t ∈ IntervalPredicate.scope (P.interval i) α (↑↓[c,d,b,q]◇[I]φ)
    simpa only [IntervalPredicate.scope, hc, hd] using ht
  let K : MarkedInterval := ⟨(P.interval j).left - I.upper, S.right, m, q⟩
  have hsub : S.carrier ⊆ K.carrier := by
    intro t ht
    obtain ⟨u, huI, hu, _⟩ := hwitness t ht
    have hr : u.1 - t ≤ I.upper := huI.2
    refine ⟨?_, ht.2⟩
    change (P.interval j).left - I.upper < t ∨
      ((P.interval j).left - I.upper = t ∧ m.Includes)
    rcases hu with hu | ⟨hu, hm⟩
    · left; linarith
    · by_cases hlt : (P.interval j).left - I.upper < t
      · exact Or.inl hlt
      · exact Or.inr ⟨by linarith, hm⟩
  have hl := ((MarkedInterval.subset_iff hS).1 hsub).1
  have hg : (γ c : ℝ) <[Marker.imp b m] I.upper := by
    change (P.interval j).left - I.upper <[Marker.imp b m]
      (P.interval i).left - (α c : ℝ) at hl
    rw [← hc] at hl
    rcases hl with hlt | ⟨heq, hm⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, hm⟩
  have hguard : (σ,P,γ,⟨k.1 + 1, by omega⟩)⊨ⱼ
      (c <ᶜ[Marker.imp b m] (⟨I.upper, I.lower_nonnegative.trans I.nonSingular.le⟩ : NNReal)) :=
    (Judgement.satisfies_markedLT _ _ _ _ _ _ _).2 hg
  refine ⟨boundedEventually_defer c d b q m I φ, ?_, ?_⟩
  · cases m <;> simp [boundedEventually]
  · simp only [boundedEventually_defer, Judgement.Satisfies, dif_pos hk, dif_pos hn]
    exact ⟨rfl, hguard, hnext⟩

/-- Given the check guards and the current unclocked predicate, source
satisfaction supplies the reset continuation without stability or invariants. -/
theorem boundedEventually_check_complete_of_plain [DecidableEq Clock]
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size)
    (hg : I.lower <[Marker.conj b (¬ₘ (P.interval ⟨k.1 + 1, hn⟩).leftBoundary)]
      (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩) c : ℝ))
    (hdg : (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩) d : ℝ)
      <[Marker.conj q (P.interval ⟨k.1 + 1, hn⟩).leftBoundary] I.lower)
    (hφ : (σ,P,α,k)⊨ⱼ(Judgement.predicate (.plain φ)))
    (h : (σ,P,α,k)⊨ⱼ((boundedEventually c d b q I φ).source : Judgement Clock Var)) :
    (boundedEventually c d b q I φ).BranchSatisfied σ P α k := by
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
  have hU : (σ,P.interval i,α)⊨ᵢ(↑↓[c,d,b,q]◇[I]φ) := by
    simpa only [boundedEventually, Judgement.Satisfies, dif_pos hk] using h
  have hnext : (σ,P.interval j,β)⊨ᵢ(↑↓[c,d,m,q]◇[I]φ) := by
    intro t ht
    have hl : (P.interval j).left - I.lower < t ∨
        ((P.interval j).left - I.lower = t ∧ m.Includes) := by
      have hl := ht.1
      change (P.interval j).left - (β c : ℝ) < t ∨
        ((P.interval j).left - (β c : ℝ) = t ∧ m.Includes) at hl
      rw [hβc] at hl
      exact hl
    have hlow : (P.interval j).left - I.lower ≤ t := hl.elim le_of_lt (fun h => h.1.le)
    have htOld : t ∈ IntervalPredicate.scope (P.interval i) α (↑↓[c,d,b,q]◇[I]φ) := by
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
  have hguard : (σ,P,γ,⟨k.1 + 1, by omega⟩)⊨ⱼ(c >ᶜ[Marker.conj b (¬ₘ m)] a) :=
    (Judgement.satisfies_markedGT _ _ _ _ _ _ _).2 hg
  have hdguard : (σ,P,γ,⟨k.1 + 1, by omega⟩)⊨ⱼ(d <ᶜ[Marker.conj q m] a) :=
    (Judgement.satisfies_markedLT _ _ _ _ _ _ _).2 hdg
  refine ⟨boundedEventually_check c d b q m I φ, ?_, ?_⟩
  · cases m <;> simp [boundedEventually]
  · simp only [boundedEventually_check, Judgement.Satisfies, dif_pos hk, dif_pos hn] at hφ ⊢
    exact ⟨hφ, hguard, hdguard, hnext, rfl⟩

/-- The current unclocked predicate and the finish guard select the finish
branch at the actual next marker. No source or invariant is needed here. -/
theorem boundedEventually_finish_complete_of_plain [DecidableEq Clock]
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size)
    (hg : I.lower <[Marker.notConj q (P.interval ⟨k.1 + 1, hn⟩).leftBoundary]
      (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩) d : ℝ))
    (hφ : (σ,P,α,k)⊨ⱼ(Judgement.predicate (.plain φ))) :
    (boundedEventually c d b q I φ).BranchSatisfied σ P α k := by
  have hk : k.1 < P.size := by omega
  let γ := ClockResetSet.elapse α (Judgement.duration P ⟨k.1, hk⟩)
  let m := (P.interval ⟨k.1 + 1, hn⟩).leftBoundary
  have hguard : (σ,P,γ,⟨k.1 + 1, by omega⟩)⊨ⱼ
      (d >ᶜ[Marker.notConj q m] (⟨I.lower, I.lower_nonnegative⟩ : NNReal)) :=
    (Judgement.satisfies_markedGT _ _ _ _ _ _ _).2 hg
  refine ⟨boundedEventually_finish d q m I φ, ?_, ?_⟩
  · cases m <;> simp [boundedEventually]
  · simp only [boundedEventually_finish, Judgement.Satisfies, dif_pos hk, dif_pos hn] at hφ ⊢
    exact ⟨hφ, hguard, rfl⟩

/-- If the left clock has not reached the checking threshold, every
witness is already in the next suffix, independently of the current operand. -/
theorem boundedEventually_defer_complete_of_lower_guard [DecidableEq Clock]
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size)
    (hg : (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩) c : ℝ)
      <[Marker.imp b (P.interval ⟨k.1 + 1, hn⟩).leftBoundary] I.lower)
    (h : (σ,P,α,k)⊨ⱼ((boundedEventually c d b q I φ).source : Judgement Clock Var)) :
    (boundedEventually c d b q I φ).BranchSatisfied σ P α k := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let j : Fin P.size := ⟨k.1 + 1, hn⟩
  let m := (P.interval j).leftBoundary
  let γ := ClockResetSet.elapse α (Judgement.duration P i)
  have hc : (P.interval j).left - (γ c : ℝ) = (P.interval i).left - (α c : ℝ) :=
    Judgement.next_left_sub_elapse_eq P α i hn c
  have hd : (P.interval j).left - (γ d : ℝ) = (P.interval i).left - (α d : ℝ) :=
    Judgement.next_left_sub_elapse_eq P α i hn d
  have hU : (σ,P.interval i,α)⊨ᵢ(↑↓[c,d,b,q]◇[I]φ) := by
    simpa only [boundedEventually, Judgement.Satisfies, dif_pos hk] using h
  have hnext : (σ,P.interval j,γ)⊨ᵢ(↑↓[c,d,b,q]◇[I]φ) := by
    intro t ht
    have htOld : t ∈ IntervalPredicate.scope (P.interval i) α (↑↓[c,d,b,q]◇[I]φ) := by
      simpa only [IntervalPredicate.scope, hc, hd] using ht
    obtain ⟨u, huI, _, huφ⟩ := hU t htOld
    refine ⟨u, huI, ?_, huφ⟩
    have hl : (P.interval j).left - (γ c : ℝ) < t ∨
        ((P.interval j).left - (γ c : ℝ) = t ∧ b.Includes) := ht.1
    have hu : I.lower ≤ u.1 - t := huI.1
    change (γ c : ℝ) <[Marker.imp b m] I.lower at hg
    rcases hg with hg | ⟨hg, hm⟩
    · left; rcases hl with hl | ⟨hl, _⟩ <;> linarith
    · rcases hl with hl | ⟨hl, hb⟩
      · left; linarith
      · by_cases hlt : (P.interval j).left < u.1
        · exact Or.inl hlt
        · exact Or.inr ⟨by linarith, (Marker.includes_imp _ _).1 hm hb⟩
  have hupper : (γ c : ℝ) <[Marker.imp b m] I.upper := by
    left
    have hle : (γ c : ℝ) ≤ I.lower := hg.elim le_of_lt (fun h => h.1.le)
    exact hle.trans_lt I.nonSingular
  have hguard : (σ,P,γ,⟨k.1 + 1, by omega⟩)⊨ⱼ
      (c <ᶜ[Marker.imp b m] (⟨I.upper, I.lower_nonnegative.trans I.nonSingular.le⟩ : NNReal)) :=
    (Judgement.satisfies_markedLT _ _ _ _ _ _ _).2 hupper
  refine ⟨boundedEventually_defer c d b q m I φ, ?_, ?_⟩
  · cases m <;> simp [boundedEventually]
  · simp only [boundedEventually_defer, Judgement.Satisfies, dif_pos hk, dif_pos hn]
    exact ⟨rfl, hguard, hnext⟩

/-- Complete case split for `↑↓` `◇` at every position. -/
theorem boundedEventually_complete_at [DecidableEq Clock]
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hinv : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α (↑↓[c,d,b,q]◇[I]φ))
    (hs : σ.StablePartition (◇[(I : TimeInterval)] φ) P)
    (h : (σ,P,α,k)⊨ⱼ((boundedEventually c d b q I φ).source : Judgement Clock Var)) :
    (boundedEventually c d b q I φ).BranchSatisfied σ P α k := by
  classical
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · let γ := ClockResetSet.elapse α (Judgement.duration P ⟨k.1, hk⟩)
      let m := (P.interval ⟨k.1 + 1, hn⟩).leftBoundary
      by_cases hφ : (σ,P,α,k)⊨ⱼ(Judgement.predicate (.plain φ))
      · by_cases hf : I.lower <[Marker.notConj q m] (γ d : ℝ)
        · exact boundedEventually_finish_complete_of_plain c d b q I φ σ P α k hn hf hφ
        · have hdg : (γ d : ℝ) <[Marker.conj q m] I.lower :=
            (Judgement.boundedAlways_right_guard_complement _ _ _ _).2 hf
          by_cases hg : (γ c : ℝ) <[Marker.imp b m] I.lower
          · exact boundedEventually_defer_complete_of_lower_guard c d b q I φ σ P α k hn hg h
          · have hc : I.lower <[Marker.conj b (¬ₘ m)] (γ c : ℝ) := by
              by_contra hh
              exact hg ((Judgement.upperAlways_guard_complement _ _ _ _).2 hh)
            exact boundedEventually_check_complete_of_plain c d b q I φ hcd σ P α k hn hc hdg hφ h
      · exact boundedEventually_defer_complete_of_not_plain c d b q I φ σ P α k hn (hinv hk) hs hφ h
    · exact boundedEventually_complete_at_last c d b q I φ σ P α k (by omega) (hinv hk) hs h
  · simp [Judgement.Satisfies, hk] at h

/-- Correctness of all three `↑↓` `◇` continuation schemas. -/
theorem boundedEventually_correct_at [DecidableEq Clock]
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hinv : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α (↑↓[c,d,b,q]◇[I]φ))
    (hs : σ.StablePartition (◇[(I : TimeInterval)] φ) P) :
    ((σ,P,α,k)⊨ⱼ((boundedEventually c d b q I φ).source : Judgement Clock Var)) ↔
      (boundedEventually c d b q I φ).BranchSatisfied σ P α k :=
  ⟨boundedEventually_complete_at c d b q I φ hcd σ P α k hinv hs,
    boundedEventually_sound_at c d b q I φ hcd σ P α k hinv⟩

/-- `RuleFinallyUpBranchOne`: defer after freezing the current right
endpoint with a fresh clock. -/
def upperEventually_defer [DecidableEq Clock] (c d : Clock) (b m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) : Judgement Clock Var :=
  Xⱼ ((c <ᶜ[Marker.imp b m]
    (⟨I.upper, I.lower_nonnegative.trans I.nonSingular.le⟩ : NNReal)) ∧ⱼ
    (⟦d ↦ᶜ 0⟧ ·ⱼ ((↑↓[c,d,b,¬ₘ m]◇[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[m])))

/-- The judgement part of `RuleFinallyUpBranchTwo`; the enclosing rule
includes this schema only when the timing lower bound is positive. -/
def upperEventually_check [DecidableEq Clock] (c d : Clock) (b m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) : Judgement Clock Var :=
  let a : NNReal := ⟨I.lower, I.lower_nonnegative⟩
  Judgement.predicate (.plain φ) ∧ⱼ
    Xⱼ ((c >ᶜ[Marker.conj b (¬ₘ m)] a) ∧ⱼ
      ((⟦c ↦ᶜ a⟧).union ⟦d ↦ᶜ 0⟧ ·ⱼ
        ((↑↓[c,d,m,¬ₘ m]◇[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[m])))

/-- The `↑` form of `◇` has two defer branches. A zero lower bound adds
the branch `[φ]`; a positive lower bound adds two check branches. -/
noncomputable def upperEventually [DecidableEq Clock] (c d : Clock) (b : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) : ExpansionRule Clock Var := by
  classical
  exact {
    source := ↑[c,b]◇[I]φ
    branches := [upperEventually_defer c d b ○ I φ, upperEventually_defer c d b ● I φ] ++
      if I.lower = 0 then [Judgement.predicate (.plain φ)]
      else [upperEventually_check c d b ○ I φ, upperEventually_check c d b ● I φ]
    branches_nonempty := by simp }

@[simp] theorem upperEventually_branch_count_of_zero [DecidableEq Clock]
    (c d : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hzero : I.lower = 0) : (upperEventually c d b I φ).branches.length = 3 := by
  simp [upperEventually, hzero]

@[simp] theorem upperEventually_branch_count_of_pos [DecidableEq Clock]
    (c d : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hpos : 0 < I.lower) : (upperEventually c d b I φ).branches.length = 4 := by
  simp [upperEventually, ne_of_gt hpos]

/-- Defer soundness directly reuses the `↑`-to-next-`↑↓` transition.
Neither the clock guard, stability, nor an invariant is needed here. -/
theorem upperEventually_defer_sound [DecidableEq Clock]
    (c d : Clock) (b m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) : upperEventually_defer c d b m I φ ⇒ⱼ
      ((↑[c,b]◇[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  intro σ P α k h
  apply Judgement.next_reset_bounded_eventually_implies_upper c d b m I φ hcd σ P α k
  by_cases hk : k.1 < P.size
  · simp only [upperEventually_defer, Judgement.Satisfies, dif_pos hk] at h ⊢
    exact h.2
  · simp [upperEventually_defer, Judgement.Satisfies, hk] at h

/-- Soundness of the zero-lower-bound branch `[φ]` under the source
invariant, without stability or distinct-clock assumptions. -/
theorem upperEventually_plain_sound_at
    (c : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hzero : I.lower = 0) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hinv : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α (↑[c,b]◇[I]φ))
    (h : (σ,P,α,k)⊨ⱼ(Judgement.predicate (.plain φ))) :
    (σ,P,α,k)⊨ⱼ((↑[c,b]◇[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  by_cases hk : k.1 < P.size
  · let i : Fin P.size := ⟨k.1, hk⟩
    have hDomain : (P.interval i).carrier ⊆ σ.domain := by
      intro t ht
      rw [← P.covers]
      exact Set.mem_iUnion.2 ⟨i, ht⟩
    simp only [Judgement.Satisfies, dif_pos hk] at h ⊢
    exact IntervalPredicate.satisfies_upper_eventually_of_plain_of_zero
      σ (P.interval i) α c b I φ (P.nonempty i) hDomain hzero (hinv hk) h
  · simp [Judgement.Satisfies, hk] at h

/-- `↑` `◇` check/reset soundness. The current-witness argument
and the reset continuation cover complementary parts of the source scope. -/
theorem upperEventually_check_sound_at [DecidableEq Clock]
    (c d : Clock) (b m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hinv : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α (↑[c,b]◇[I]φ))
    (h : (σ,P,α,k)⊨ⱼ(upperEventually_check c d b m I φ)) :
    (σ,P,α,k)⊨ⱼ((↑[c,b]◇[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
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
      simp only [upperEventually_check, Judgement.Satisfies, dif_pos hk, dif_pos hn] at h ⊢
      have hmarker : (P.interval j).leftBoundary = m := h.2.2.2
      have hm : (P.interval i).rightBoundary = ¬ₘ m :=
        (P.adjacent_rightBoundary_eq_complement_leftBoundary i hn).trans
          (congrArg Marker.complement hmarker)
      have hnext : (σ,P.interval j,β)⊨ᵢ(↑↓[c,d,m,¬ₘ m]◇[I]φ) := h.2.2.1
      have hDomain : (P.interval i).carrier ⊆ σ.domain := by
        intro t ht
        rw [← P.covers]
        exact Set.mem_iUnion.2 ⟨i, ht⟩
      intro t ht
      by_cases hcut : t + I.lower <[(P.interval i).rightBoundary] (P.interval i).right
      · exact IntervalPredicate.exists_current_witness_of_marked_bounds
          σ (P.interval i) α c b I φ (P.nonempty i) hDomain (hinv hk).1 h.1 t ht.1 hcut
      · have htNext : t ∈ IntervalPredicate.scope (P.interval j) β (↑↓[c,d,m,¬ₘ m]◇[I]φ) := by
          constructor
          · change ((P.interval j).left - (β c : ℝ)) <[m] t
            rw [hβc, ← hadj]
            apply (Judgement.not_markedLT_add_complement_iff t I.lower _ m).1
            simpa only [hm] using hcut
          · change t < (P.interval j).left - (β d : ℝ) ∨
              (t = (P.interval j).left - (β d : ℝ) ∧ (¬ₘ m).Includes)
            rw [hβd, NNReal.coe_zero, sub_zero, ← hadj, ← hm]
            exact ht.2
        obtain ⟨u, hu, hs, hφ⟩ := hnext t htNext
        exact ⟨u, hu, IntervalPredicate.inCurrentSuffix_of_adjacent
          (P.interval i) (P.interval j) (P.nonempty i) hadj hs, hφ⟩
    · simp [upperEventually_check, Judgement.Satisfies, hk, hn] at h
  · simp [upperEventually_check, Judgement.Satisfies, hk] at h

/-- Soundness of every `↑` `◇` branch, with numerical side
conditions enforced by the branch list. Stability is unnecessary. -/
theorem upperEventually_sound_at [DecidableEq Clock]
    (c d : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hinv : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α (↑[c,b]◇[I]φ))
    (h : (upperEventually c d b I φ).BranchSatisfied σ P α k) :
    (σ,P,α,k)⊨ⱼ((upperEventually c d b I φ).source : Judgement Clock Var) := by
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

/-- At the last interval, `↑` `◇` satisfaction forces a zero
lower bound and the current unclocked operand, hence satisfies the branch `[φ]`. -/
theorem upperEventually_complete_at_last [DecidableEq Clock]
    (c d : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hlast : k.1 + 1 = P.size)
    (hinv : IntervalPredicate.Invariant (P.interval ⟨k.1, by omega⟩) α (↑[c,b]◇[I]φ))
    (hs : σ.StablePartition (◇[(I : TimeInterval)] φ) P)
    (h : (σ,P,α,k)⊨ⱼ((upperEventually c d b I φ).source : Judgement Clock Var)) :
    (upperEventually c d b I φ).BranchSatisfied σ P α k := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let S := (IntervalPredicate.scope (P.interval i) α (↑[c,b]◇[I]φ)).toMarkedInterval
  have hS : S.carrier.Nonempty :=
    IntervalPredicate.upper_eventually_scope_nonempty_of_invariant (P.interval i) α c b I φ hinv
  have hU : (σ,P.interval i,α)⊨ᵢ(↑[c,b]◇[I]φ) := by
    simpa only [upperEventually, Judgement.Satisfies, dif_pos hk] using h
  let K : MarkedInterval := ⟨S.left, (P.interval i).right - I.lower, b, ○⟩
  have hsub : S.carrier ⊆ K.carrier := by
    intro t ht
    obtain ⟨u, huI, hu, _⟩ := hU t ht
    have hur := P.lt_right_of_mem_last i hlast (P.mem_last_of_left_condition i hlast u.2 hu)
    have hlo : I.lower ≤ u.1 - t := huI.1
    exact ⟨ht.1, Or.inl (by change t < (P.interval i).right - I.lower; linarith)⟩
  have hr := ((MarkedInterval.subset_iff hS).1 hsub).2
  have hzero : I.lower = 0 := by
    have hle : (P.interval i).right ≤ (P.interval i).right - I.lower :=
      hr.elim le_of_lt (fun h => h.1.le)
    linarith [I.lower_nonnegative]
  obtain ⟨t, ht⟩ := hS
  obtain ⟨u, _, hu, huφ⟩ := hU t ht
  have huJ := P.mem_last_of_left_condition i hlast u.2 hu
  have hφ : (σ,P.interval i,α)⊨ᵢ(.plain φ) := by
    intro v hv
    exact (hs i φ (.until_right (.refl φ)) u v huJ hv).1 huφ
  refine ⟨Judgement.predicate (.plain φ), ?_, ?_⟩
  · simp [upperEventually, hzero]
  · simpa only [Judgement.Satisfies, dif_pos hk] using hφ

/-- The branch `[φ]` at zero lower bound is available at any position. -/
theorem upperEventually_plain_complete_of_zero [DecidableEq Clock]
    (c d : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hzero : I.lower = 0) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hφ : (σ,P,α,k)⊨ⱼ(Judgement.predicate (.plain φ))) :
    (upperEventually c d b I φ).BranchSatisfied σ P α k :=
  ⟨Judgement.predicate (.plain φ), by simp [upperEventually, hzero], hφ⟩

/-- Conditional check completeness: the reset scope is contained in the
source scope, and its lower endpoint forces all witnesses into the next suffix. -/
theorem upperEventually_check_complete_of_plain [DecidableEq Clock]
    (c d : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (hpos : 0 < I.lower)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size)
    (hg : I.lower <[Marker.conj b (¬ₘ (P.interval ⟨k.1 + 1, hn⟩).leftBoundary)]
      (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩) c : ℝ))
    (hφ : (σ,P,α,k)⊨ⱼ(Judgement.predicate (.plain φ)))
    (h : (σ,P,α,k)⊨ⱼ((upperEventually c d b I φ).source : Judgement Clock Var)) :
    (upperEventually c d b I φ).BranchSatisfied σ P α k := by
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
  have hU : (σ,P.interval i,α)⊨ᵢ(↑[c,b]◇[I]φ) := by
    simpa only [upperEventually, Judgement.Satisfies, dif_pos hk] using h
  have hnext : (σ,P.interval j,β)⊨ᵢ(↑↓[c,d,m,¬ₘ m]◇[I]φ) := by
    intro t ht
    have hl : (P.interval j).left - I.lower < t ∨
        ((P.interval j).left - I.lower = t ∧ m.Includes) := by
      have hl := ht.1
      change (P.interval j).left - (β c : ℝ) < t ∨
        ((P.interval j).left - (β c : ℝ) = t ∧ m.Includes) at hl
      rw [hβc] at hl
      exact hl
    have hlow : (P.interval j).left - I.lower ≤ t := hl.elim le_of_lt (fun h => h.1.le)
    have htOld : t ∈ IntervalPredicate.scope (P.interval i) α (↑[c,b]◇[I]φ) := by
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
  have hguard : (σ,P,γ,⟨k.1 + 1, by omega⟩)⊨ⱼ(c >ᶜ[Marker.conj b (¬ₘ m)] a) :=
    (Judgement.satisfies_markedGT _ _ _ _ _ _ _).2 hg
  refine ⟨upperEventually_check c d b m I φ, ?_, ?_⟩
  · cases m <;> simp [upperEventually, ne_of_gt hpos]
  · simp only [upperEventually_check, Judgement.Satisfies, dif_pos hk, dif_pos hn] at hφ ⊢
    exact ⟨hφ, hguard, hnext, rfl⟩

/-- Package future witnesses and the guard into the defer branch of the `↑` rule.
Resetting the right clock preserves the current scope exactly. -/
theorem upperEventually_defer_complete_of_future_witnesses [DecidableEq Clock]
    (c d : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size)
    (hg : (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩) c : ℝ)
      <[Marker.imp b (P.interval ⟨k.1 + 1, hn⟩).leftBoundary] I.upper)
    (hw : ∀ t ∈ IntervalPredicate.scope (P.interval ⟨k.1, by omega⟩) α (↑[c,b]◇[I]φ),
      ∃ u : σ.Time, u.1 ∈ (I : TimeInterval).translate t ∧
        IntervalPredicate.InCurrentSuffix (P.interval ⟨k.1 + 1, hn⟩) u.1 ∧ (σ,u)⊨φ) :
    (upperEventually c d b I φ).BranchSatisfied σ P α k := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let j : Fin P.size := ⟨k.1 + 1, hn⟩
  let m := (P.interval j).leftBoundary
  let γ := ClockResetSet.elapse α (Judgement.duration P i)
  let β := (⟦d ↦ᶜ 0⟧).apply γ
  have hβc : β c = γ c := ClockResetSet.apply_singleton_of_ne 0 γ hcd
  have hβd : β d = 0 := ClockResetSet.apply_singleton_self d 0 γ
  have hc : (P.interval j).left - (β c : ℝ) = (P.interval i).left - (α c : ℝ) := by
    rw [hβc]
    exact Judgement.next_left_sub_elapse_eq P α i hn c
  have hadj : (P.interval i).right = (P.interval j).left := P.adjacent_right_eq_left i hn
  have hm : (P.interval i).rightBoundary = ¬ₘ m :=
    P.adjacent_rightBoundary_eq_complement_leftBoundary i hn
  have hnext : (σ,P.interval j,β)⊨ᵢ(↑↓[c,d,b,¬ₘ m]◇[I]φ) := by
    intro t ht
    apply hw t
    constructor
    · have hl := ht.1
      change (P.interval j).left - (β c : ℝ) <[b] t at hl
      rw [hc] at hl
      exact hl
    · have hr := ht.2
      change t <[(¬ₘ m)] (P.interval j).left - (β d : ℝ) at hr
      rw [hβd, NNReal.coe_zero, sub_zero, ← hadj, ← hm] at hr
      exact hr
  have hguard : (σ,P,γ,⟨k.1 + 1, by omega⟩)⊨ⱼ
      (c <ᶜ[Marker.imp b m] (⟨I.upper, I.lower_nonnegative.trans I.nonSingular.le⟩ : NNReal)) :=
    (Judgement.satisfies_markedLT _ _ _ _ _ _ _).2 hg
  refine ⟨upperEventually_defer c d b m I φ, ?_, ?_⟩
  · cases m <;> simp [upperEventually]
  · simp only [upperEventually_defer, Judgement.Satisfies, dif_pos hk, dif_pos hn]
    exact ⟨hguard, hnext, rfl⟩

/-- A left clock below the lower threshold forces all witnesses into the
next suffix, without stability or an invariant. -/
theorem upperEventually_defer_complete_of_lower_guard [DecidableEq Clock]
    (c d : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size)
    (hg : (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩) c : ℝ)
      <[Marker.imp b (P.interval ⟨k.1 + 1, hn⟩).leftBoundary] I.lower)
    (h : (σ,P,α,k)⊨ⱼ((upperEventually c d b I φ).source : Judgement Clock Var)) :
    (upperEventually c d b I φ).BranchSatisfied σ P α k := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let j : Fin P.size := ⟨k.1 + 1, hn⟩
  let m := (P.interval j).leftBoundary
  let γ := ClockResetSet.elapse α (Judgement.duration P i)
  have hc : (P.interval j).left - (γ c : ℝ) = (P.interval i).left - (α c : ℝ) :=
    Judgement.next_left_sub_elapse_eq P α i hn c
  have hU : (σ,P.interval i,α)⊨ᵢ(↑[c,b]◇[I]φ) := by
    simpa only [upperEventually, Judgement.Satisfies, dif_pos hk] using h
  apply upperEventually_defer_complete_of_future_witnesses c d b I φ hcd σ P α k hn
  · left
    have hle : (γ c : ℝ) ≤ I.lower := hg.elim le_of_lt (fun h => h.1.le)
    exact hle.trans_lt I.nonSingular
  · intro t ht
    obtain ⟨u, huI, _, huφ⟩ := hU t ht
    refine ⟨u, huI, ?_, huφ⟩
    have hl : (P.interval j).left - (γ c : ℝ) <[b] t := by rw [hc]; exact ht.1
    have hu : I.lower ≤ u.1 - t := huI.1
    change (γ c : ℝ) <[Marker.imp b m] I.lower at hg
    rcases hg with hg | ⟨hg, hm⟩
    · left; rcases hl with hl | ⟨hl, _⟩ <;> linarith
    · rcases hl with hl | ⟨hl, hb⟩
      · left; linarith
      · by_cases hlt : (P.interval j).left < u.1
        · exact Or.inl hlt
        · exact Or.inr ⟨by linarith, (Marker.includes_imp _ _).1 hm hb⟩

/-- Exhaustive next-interval completeness when the current operand holds.
A zero lower bound permits the branch `[φ]`; at positive lower bounds the complementary guards
select defer or check/reset. -/
theorem upperEventually_complete_at_next_of_plain [DecidableEq Clock]
    (c d : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size)
    (hφ : (σ,P,α,k)⊨ⱼ(Judgement.predicate (.plain φ)))
    (h : (σ,P,α,k)⊨ⱼ((upperEventually c d b I φ).source : Judgement Clock Var)) :
    (upperEventually c d b I φ).BranchSatisfied σ P α k := by
  classical
  by_cases hz : I.lower = 0
  · exact upperEventually_plain_complete_of_zero c d b I φ hz σ P α k hφ
  · have hpos : 0 < I.lower := lt_of_le_of_ne I.lower_nonnegative (Ne.symm hz)
    let γ := ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩)
    let m := (P.interval ⟨k.1 + 1, hn⟩).leftBoundary
    by_cases hg : (γ c : ℝ) <[Marker.imp b m] I.lower
    · exact upperEventually_defer_complete_of_lower_guard c d b I φ hcd σ P α k hn hg h
    · have hc : I.lower <[Marker.conj b (¬ₘ m)] (γ c : ℝ) := by
        by_contra hh
        exact hg ((Judgement.upperAlways_guard_complement _ _ _ _).2 hh)
      exact upperEventually_check_complete_of_plain c d b I φ hcd hpos σ P α k hn hc hφ h

/-- If the operand does not hold on a stable current interval, all witnesses lie in later
intervals; their
upper delay bound implies the defer guard by marked scope containment. -/
theorem upperEventually_defer_complete_of_not_plain [DecidableEq Clock]
    (c d : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size)
    (hinv : IntervalPredicate.Invariant (P.interval ⟨k.1, by omega⟩) α (↑[c,b]◇[I]φ))
    (hs : σ.StablePartition (◇[(I : TimeInterval)] φ) P)
    (hnot : ¬(σ,P,α,k)⊨ⱼ(Judgement.predicate (.plain φ)))
    (h : (σ,P,α,k)⊨ⱼ((upperEventually c d b I φ).source : Judgement Clock Var)) :
    (upperEventually c d b I φ).BranchSatisfied σ P α k := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let j : Fin P.size := ⟨k.1 + 1, hn⟩
  let m := (P.interval j).leftBoundary
  let γ := ClockResetSet.elapse α (Judgement.duration P i)
  let S := (IntervalPredicate.scope (P.interval i) α (↑[c,b]◇[I]φ)).toMarkedInterval
  have hS : S.carrier.Nonempty :=
    IntervalPredicate.upper_eventually_scope_nonempty_of_invariant (P.interval i) α c b I φ hinv
  have hU : (σ,P.interval i,α)⊨ᵢ(↑[c,b]◇[I]φ) := by
    simpa only [upperEventually, Judgement.Satisfies, dif_pos hk] using h
  have hnone : ∀ u : σ.Time, u.1 ∈ P.interval i → ¬(σ,u)⊨φ := by
    intro u hu hφ
    apply hnot
    simp only [Judgement.Satisfies, dif_pos hk]
    intro v hv
    exact (hs i φ (.until_right (.refl φ)) u v hu hv).1 hφ
  have hw : ∀ t ∈ S, ∃ u : σ.Time,
      u.1 ∈ (I : TimeInterval).translate t ∧
      IntervalPredicate.InCurrentSuffix (P.interval j) u.1 ∧ (σ,u)⊨φ := by
    intro t ht
    obtain ⟨u, huI, hu, hφ⟩ := hU t ht
    rcases IntervalPredicate.mem_or_inCurrentSuffix_of_adjacent (P.interval i) (P.interval j)
        (P.adjacent_right_eq_left i hn)
        (P.adjacent_rightBoundary_eq_complement_leftBoundary i hn) hu with huJ | huK
    · exact (hnone u huJ hφ).elim
    · exact ⟨u, huI, huK, hφ⟩
  let K : MarkedInterval := ⟨(P.interval j).left - I.upper, S.right, m, S.rightBoundary⟩
  have hsub : S.carrier ⊆ K.carrier := by
    intro t ht
    obtain ⟨u, huI, hu, _⟩ := hw t ht
    have hr : u.1 - t ≤ I.upper := huI.2
    refine ⟨?_, ht.2⟩
    change (P.interval j).left - I.upper < t ∨
      ((P.interval j).left - I.upper = t ∧ m.Includes)
    rcases hu with hu | ⟨hu, hm⟩
    · left; linarith
    · by_cases hlt : (P.interval j).left - I.upper < t
      · exact Or.inl hlt
      · exact Or.inr ⟨by linarith, hm⟩
  have hl := ((MarkedInterval.subset_iff hS).1 hsub).1
  have hc : (P.interval j).left - (γ c : ℝ) = (P.interval i).left - (α c : ℝ) :=
    Judgement.next_left_sub_elapse_eq P α i hn c
  have hg : (γ c : ℝ) <[Marker.imp b m] I.upper := by
    change (P.interval j).left - I.upper <[Marker.imp b m]
      (P.interval i).left - (α c : ℝ) at hl
    rw [← hc] at hl
    rcases hl with hlt | ⟨heq, hm⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, hm⟩
  exact upperEventually_defer_complete_of_future_witnesses c d b I φ hcd σ P α k hn hg hw

/-- Full `↑` `◇` completeness, including last and terminal positions. -/
theorem upperEventually_complete_at [DecidableEq Clock]
    (c d : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hinv : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α (↑[c,b]◇[I]φ))
    (hs : σ.StablePartition (◇[(I : TimeInterval)] φ) P)
    (h : (σ,P,α,k)⊨ⱼ((upperEventually c d b I φ).source : Judgement Clock Var)) :
    (upperEventually c d b I φ).BranchSatisfied σ P α k := by
  classical
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · by_cases hφ : (σ,P,α,k)⊨ⱼ(Judgement.predicate (.plain φ))
      · exact upperEventually_complete_at_next_of_plain c d b I φ hcd σ P α k hn hφ h
      · exact upperEventually_defer_complete_of_not_plain c d b I φ hcd σ P α k hn (hinv hk) hs hφ h
    · exact upperEventually_complete_at_last c d b I φ σ P α k (by omega) (hinv hk) hs h
  · simp [Judgement.Satisfies, hk] at h

/-- Correctness of all `↑` `◇` schemas under the source invariant,
full stability, and reset-clock freshness. Invariant preservation is separate. -/
theorem upperEventually_correct_at [DecidableEq Clock]
    (c d : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hinv : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α (↑[c,b]◇[I]φ))
    (hs : σ.StablePartition (◇[(I : TimeInterval)] φ) P) :
    ((σ,P,α,k)⊨ⱼ((upperEventually c d b I φ).source : Judgement Clock Var)) ↔
      (upperEventually c d b I φ).BranchSatisfied σ P α k :=
  ⟨upperEventually_complete_at c d b I φ hcd σ P α k hinv hs,
    upperEventually_sound_at c d b I φ hcd σ P α k hinv⟩

/-- Preservation of the `↑↓` `◇` invariant by defer, evaluated
at the actual next interval and elapsed valuation, not as a direct set member. -/
theorem boundedEventually_defer_preserves_invariant
    (c d : Clock) (b q m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size)
    (hinv : IntervalPredicate.Invariant (P.interval ⟨k.1, by omega⟩) α (↑↓[c,d,b,q]◇[I]φ))
    (h : Judgement.NonPredicateSatisfies σ P α k (boundedEventually_defer c d b q m I φ)) :
    IntervalPredicate.Invariant (P.interval ⟨k.1 + 1, hn⟩)
      (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩)) (↑↓[c,d,b,q]◇[I]φ) := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let j : Fin P.size := ⟨k.1 + 1, hn⟩
  let β := ClockResetSet.elapse α (Judgement.duration P i)
  simp only [boundedEventually_defer, Judgement.NonPredicateSatisfies, dif_pos hk, dif_pos hn] at h
  have hmarker : (P.interval j).leftBoundary = m := h.1
  have hg : (β c : ℝ) <[Marker.imp b (P.interval j).leftBoundary] I.upper := by
    rw [hmarker]
    exact (Judgement.nonPredicateSatisfies_markedLT σ P β ⟨k.1 + 1, by omega⟩ c
      (Marker.imp b m) ⟨I.upper, I.lower_nonnegative.trans I.nonSingular.le⟩).1 h.2.1
  exact IntervalPredicate.bounded_eventually_invariant_of_equal_increment
    (P.interval i) (P.interval j) α β c d b q I φ
    (Judgement.duration P i : ℝ) (by rfl) (by rfl) hinv hg

/-- Check/reset establishes the target invariant from its own guard.
The source invariant and stability are not required for this branch. -/
theorem boundedEventually_check_preserves_invariant [DecidableEq Clock]
    (c d : Clock) (b q m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size)
    (h : Judgement.NonPredicateSatisfies σ P α k (boundedEventually_check c d b q m I φ)) :
    IntervalPredicate.Invariant (P.interval ⟨k.1 + 1, hn⟩)
      ((⟦c ↦ᶜ (⟨I.lower, I.lower_nonnegative⟩ : NNReal)⟧).apply
        (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩)))
      (↑↓[c,d,m,q]◇[I]φ) := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let j : Fin P.size := ⟨k.1 + 1, hn⟩
  let a : NNReal := ⟨I.lower, I.lower_nonnegative⟩
  let γ := ClockResetSet.elapse α (Judgement.duration P i)
  let β := (⟦c ↦ᶜ a⟧).apply γ
  have hc : β c = a := ClockResetSet.apply_singleton_self c a γ
  have hd : β d = γ d := ClockResetSet.apply_singleton_of_ne a γ hcd.symm
  simp only [boundedEventually_check, Judgement.NonPredicateSatisfies, dif_pos hk, dif_pos hn] at h
  have hm : (P.interval j).leftBoundary = m := h.2.2.2.2
  have hg : (β d : ℝ) <[Marker.conj q (P.interval j).leftBoundary] I.lower := by
    rw [hd, hm]
    exact (Judgement.nonPredicateSatisfies_markedLT σ P γ ⟨k.1 + 1, by omega⟩ d
      (Marker.conj q m) a).1 h.2.2.1
  have hresult := IntervalPredicate.bounded_eventually_invariant_of_left_lower
    (P.interval j) β c d q I φ (by rw [hc]; rfl) hg
  rw [hm] at hresult
  exact hresult

/-- In the check branch of the `↑` form of `◇`, a positive lower timing bound
establishes the invariant of the reset predicate in the `↑↓` form. -/
theorem upperEventually_check_preserves_invariant [DecidableEq Clock]
    (c d : Clock) (b m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (hpos : 0 < I.lower)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size)
    (h : Judgement.NonPredicateSatisfies σ P α k (upperEventually_check c d b m I φ)) :
    IntervalPredicate.Invariant (P.interval ⟨k.1 + 1, hn⟩)
      (((⟦c ↦ᶜ (⟨I.lower, I.lower_nonnegative⟩ : NNReal)⟧).union ⟦d ↦ᶜ 0⟧).apply
        (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩)))
      (↑↓[c,d,m,¬ₘ m]◇[I]φ) := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let j : Fin P.size := ⟨k.1 + 1, hn⟩
  let a : NNReal := ⟨I.lower, I.lower_nonnegative⟩
  let γ := ClockResetSet.elapse α (Judgement.duration P i)
  let β := ((⟦c ↦ᶜ a⟧).union ⟦d ↦ᶜ 0⟧).apply γ
  have hc : β c = a := by
    simp [β, ClockResetSet.apply, ClockResetSet.union, ClockResetSet.singleton]
  have hd : β d = 0 := by
    change ((⟦c ↦ᶜ a⟧).union ⟦d ↦ᶜ 0⟧).apply γ d = 0
    rw [ClockResetSet.apply_union_eq_right_of_not_mem _ _ γ (by simp [Ne.symm hcd])]
    exact ClockResetSet.apply_singleton_self d 0 γ
  simp only [upperEventually_check, Judgement.NonPredicateSatisfies, dif_pos hk, dif_pos hn] at h
  have hm : (P.interval j).leftBoundary = m := h.2.2.2
  have hg : (β d : ℝ) <[Marker.conj (¬ₘ m) (P.interval j).leftBoundary] I.lower := by
    left
    simpa only [hd, NNReal.coe_zero] using hpos
  have hresult := IntervalPredicate.bounded_eventually_invariant_of_left_lower
    (P.interval j) β c d (¬ₘ m) I φ (by rw [hc]; rfl) hg
  rw [hm] at hresult
  exact hresult

/-- The defer branch of the `↑` rule preserves the invariant: the guard supplies reach, and
the source's nonempty-scope condition supplies ordering after the right reset. -/
theorem upperEventually_defer_preserves_invariant [DecidableEq Clock]
    (c d : Clock) (b m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size)
    (hinv : IntervalPredicate.Invariant (P.interval ⟨k.1, by omega⟩) α (↑[c,b]◇[I]φ))
    (h : Judgement.NonPredicateSatisfies σ P α k (upperEventually_defer c d b m I φ)) :
    IntervalPredicate.Invariant (P.interval ⟨k.1 + 1, hn⟩)
      ((⟦d ↦ᶜ 0⟧).apply (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩)))
      (↑↓[c,d,b,¬ₘ m]◇[I]φ) := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let j : Fin P.size := ⟨k.1 + 1, hn⟩
  let γ := ClockResetSet.elapse α (Judgement.duration P i)
  let β := (⟦d ↦ᶜ 0⟧).apply γ
  have hc : β c = γ c := ClockResetSet.apply_singleton_of_ne 0 γ hcd
  have hd : β d = 0 := ClockResetSet.apply_singleton_self d 0 γ
  simp only [upperEventually_defer, Judgement.NonPredicateSatisfies, dif_pos hk, dif_pos hn] at h
  have hm : (P.interval j).leftBoundary = m := h.2.2
  have hr : (P.interval i).rightBoundary = ¬ₘ m :=
    (P.adjacent_rightBoundary_eq_complement_leftBoundary i hn).trans
      (congrArg Marker.complement hm)
  change IntervalPredicate.Invariant (P.interval j) β (↑↓[c,d,b,¬ₘ m]◇[I]φ)
  constructor
  · rw [hc, hm]
    exact (Judgement.nonPredicateSatisfies_markedLT σ P γ ⟨k.1 + 1, by omega⟩ c
      (Marker.imp b m) ⟨I.upper, I.lower_nonnegative.trans I.nonSingular.le⟩).1 h.1
  · rw [hd, hc, NNReal.coe_zero]
    have horder := hinv.2
    change (0 : ℝ) <[Marker.conj b (P.interval i).rightBoundary]
      ((α c : ℝ) + ((P.interval i).right - (P.interval i).left)) at horder
    rw [hr] at horder
    exact horder

/-- `↑↓` `□` check/reset establishes the next predicate invariant
from its right-clock guard and reset, without the source invariant. -/
theorem boundedAlways_check_preserves_invariant [DecidableEq Clock]
    (c d : Clock) (b q m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size)
    (h : Judgement.NonPredicateSatisfies σ P α k (boundedAlways_check c d b q m I φ)) :
    IntervalPredicate.Invariant (P.interval ⟨k.1 + 1, hn⟩)
      ((⟦c ↦ᶜ (⟨I.lower, I.lower_nonnegative⟩ : NNReal)⟧).apply
        (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩)))
      (↑↓[c,d,m,q]□[I]φ) := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let j : Fin P.size := ⟨k.1 + 1, hn⟩
  let a : NNReal := ⟨I.lower, I.lower_nonnegative⟩
  let γ := ClockResetSet.elapse α (Judgement.duration P i)
  let β := (⟦c ↦ᶜ a⟧).apply γ
  have hc : β c = a := ClockResetSet.apply_singleton_self c a γ
  have hd : β d = γ d := ClockResetSet.apply_singleton_of_ne a γ hcd.symm
  simp only [boundedAlways_check, Judgement.NonPredicateSatisfies, dif_pos hk, dif_pos hn] at h
  have hm : (P.interval j).leftBoundary = m := h.2.2.2.2
  have hg : (β d : ℝ) <[Marker.conj q (P.interval j).leftBoundary] I.upper := by
    rw [hd, hm]
    exact (Judgement.nonPredicateSatisfies_markedLT σ P γ ⟨k.1 + 1, by omega⟩ d
      (Marker.conj q m) ⟨I.upper, I.lower_nonnegative.trans I.nonSingular.le⟩).1 h.2.2.1
  have hresult := IntervalPredicate.bounded_always_invariant_of_left_lower
    (P.interval j) β c d q I φ (by rw [hc]; rfl) hg
  rw [hm] at hresult
  exact hresult

/-- `↑` `□` defer resets the right clock to zero, which suffices
to establish the bounded target invariant at any next interval. -/
theorem upperAlways_defer_preserves_invariant [DecidableEq Clock]
    (c d : Clock) (b m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size) :
    IntervalPredicate.Invariant (P.interval ⟨k.1 + 1, hn⟩)
      ((⟦d ↦ᶜ 0⟧).apply (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩)))
      (↑↓[c,d,b,¬ₘ m]□[I]φ) := by
  apply IntervalPredicate.bounded_always_invariant_of_right_zero
  exact ClockResetSet.apply_singleton_self d 0 _

/-- `↑` `□` check resets the right clock to zero as well; freshness
ensures the simultaneous left-clock reset does not override it. -/
theorem upperAlways_check_preserves_invariant [DecidableEq Clock]
    (c d : Clock) (m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size) :
    IntervalPredicate.Invariant (P.interval ⟨k.1 + 1, hn⟩)
      (((⟦c ↦ᶜ (⟨I.lower, I.lower_nonnegative⟩ : NNReal)⟧).union ⟦d ↦ᶜ 0⟧).apply
        (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩)))
      (↑↓[c,d,m,¬ₘ m]□[I]φ) := by
  apply IntervalPredicate.bounded_always_invariant_of_right_zero
  rw [ClockResetSet.apply_union_eq_right_of_not_mem _ _ _ (by simp [Ne.symm hcd])]
  exact ClockResetSet.apply_singleton_self d 0 _

/-- `↑↓` `□` defer preserves the invariant at the elapsed valuation.
The equality case uses the next-marker implication in the guard. -/
theorem boundedAlways_defer_preserves_invariant
    (c d : Clock) (b q m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hn : k.1 + 1 < P.size)
    (hinv : IntervalPredicate.Invariant (P.interval ⟨k.1, by omega⟩) α (↑↓[c,d,b,q]□[I]φ))
    (h : Judgement.NonPredicateSatisfies σ P α k (boundedAlways_defer c d b q m I φ)) :
    IntervalPredicate.Invariant (P.interval ⟨k.1 + 1, hn⟩)
      (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩)) (↑↓[c,d,b,q]□[I]φ) := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let j : Fin P.size := ⟨k.1 + 1, hn⟩
  let β := ClockResetSet.elapse α (Judgement.duration P i)
  simp only [boundedAlways_defer, Judgement.NonPredicateSatisfies, dif_pos hk, dif_pos hn] at h
  have hm : (P.interval j).leftBoundary = m := h.1
  have hg : (β c : ℝ) <[Marker.imp b (P.interval j).leftBoundary] I.lower := by
    rw [hm]
    exact (Judgement.nonPredicateSatisfies_markedLT σ P β ⟨k.1 + 1, by omega⟩ c
      (Marker.imp b m) ⟨I.lower, I.lower_nonnegative⟩).1 h.2.1
  exact IntervalPredicate.bounded_always_invariant_of_equal_increment
    (P.interval i) (P.interval j) α β c d b q I φ
    (Judgement.duration P i : ℝ) (by rfl) (by rfl) hinv hg

/-- The entire `↑↓` `□` defer judgement passes recursive invariant
checking, not only its next predicate considered in isolation. -/
theorem boundedAlways_defer_evaluatedInvariant
    (c d : Clock) (b q m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hinv : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α (↑↓[c,d,b,q]□[I]φ))
    (h : Judgement.NonPredicateSatisfies σ P α k (boundedAlways_defer c d b q m I φ)) :
    Judgement.EvaluatedInvariant σ P α k (boundedAlways_defer c d b q m I φ) := by
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · have hp := boundedAlways_defer_preserves_invariant c d b q m I φ σ P α k hn (hinv hk) h
      cases hg : Marker.imp b m <;>
        simpa [boundedAlways_defer, Judgement.EvaluatedInvariant, Judgement.markedLT, hg, hk, hn]
          using hp
    · simp [boundedAlways_defer, Judgement.EvaluatedInvariant, hk, hn]
  · simp [boundedAlways_defer, Judgement.NonPredicateSatisfies, hk,
      IntervalPredicate.Invariant] at *

/-- Recursive invariant checking for the entire `↑↓` `□` check branch. -/
theorem boundedAlways_check_evaluatedInvariant [DecidableEq Clock]
    (c d : Clock) (b q m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (h : Judgement.NonPredicateSatisfies σ P α k (boundedAlways_check c d b q m I φ)) :
    Judgement.EvaluatedInvariant σ P α k (boundedAlways_check c d b q m I φ) := by
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · have hp := boundedAlways_check_preserves_invariant c d b q m I φ hcd σ P α k hn h
      simpa [boundedAlways_check, Judgement.EvaluatedInvariant, hk, hn,
        IntervalPredicate.Invariant] using hp
    · simp [boundedAlways_check, Judgement.EvaluatedInvariant, hk, hn, IntervalPredicate.Invariant]
  · simp [boundedAlways_check, Judgement.NonPredicateSatisfies, hk] at *

/-- Every satisfied `↑↓` `□` branch passes recursive invariant
checking under the source invariant and reset-clock freshness. -/
theorem boundedAlways_preserves_evaluatedInvariant [DecidableEq Clock]
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hinv : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α (↑↓[c,d,b,q]□[I]φ))
    (B : Judgement Clock Var) (hB : B ∈ (boundedAlways c d b q I φ).branches)
    (h : Judgement.NonPredicateSatisfies σ P α k B) : Judgement.EvaluatedInvariant σ P α k B := by
  simp only [boundedAlways, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact boundedAlways_defer_evaluatedInvariant c d b q ○ I φ σ P α k hinv h
  · exact boundedAlways_defer_evaluatedInvariant c d b q ● I φ σ P α k hinv h
  · by_cases hk : k.1 < P.size
    · simp [Judgement.EvaluatedInvariant, hk]
    · simp_all [Judgement.NonPredicateSatisfies]
  · by_cases hk : k.1 < P.size
    · simp [Judgement.EvaluatedInvariant, IntervalPredicate.Invariant, hk]
    · simp_all [Judgement.NonPredicateSatisfies]
  · exact boundedAlways_check_evaluatedInvariant c d b q ○ I φ hcd σ P α k h
  · exact boundedAlways_check_evaluatedInvariant c d b q ● I φ hcd σ P α k h
  · by_cases hk : k.1 < P.size
    · simp [boundedAlways_finish, Judgement.EvaluatedInvariant, IntervalPredicate.Invariant, hk]
    · simp [boundedAlways_finish, Judgement.NonPredicateSatisfies, hk,
        IntervalPredicate.Invariant] at *
  · by_cases hk : k.1 < P.size
    · simp [boundedAlways_finish, Judgement.EvaluatedInvariant, IntervalPredicate.Invariant, hk]
    · simp [boundedAlways_finish, Judgement.NonPredicateSatisfies, hk,
        IntervalPredicate.Invariant] at *

/-- Recursive invariant checking for `↑↓` `◇` defer. -/
theorem boundedEventually_defer_evaluatedInvariant
    (c d : Clock) (b q m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hinv : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α (↑↓[c,d,b,q]◇[I]φ))
    (h : Judgement.NonPredicateSatisfies σ P α k (boundedEventually_defer c d b q m I φ)) :
    Judgement.EvaluatedInvariant σ P α k (boundedEventually_defer c d b q m I φ) := by
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · have hp := boundedEventually_defer_preserves_invariant c d b q m I φ σ P α k hn (hinv hk) h
      simpa [boundedEventually_defer, Judgement.EvaluatedInvariant, hk, hn] using hp
    · simp [boundedEventually_defer, Judgement.EvaluatedInvariant, hk, hn]
  · simp [boundedEventually_defer, Judgement.NonPredicateSatisfies, hk,
      IntervalPredicate.Invariant] at *

/-- Recursive invariant checking for `↑↓` `◇` check/reset. -/
theorem boundedEventually_check_evaluatedInvariant [DecidableEq Clock]
    (c d : Clock) (b q m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (h : Judgement.NonPredicateSatisfies σ P α k (boundedEventually_check c d b q m I φ)) :
    Judgement.EvaluatedInvariant σ P α k (boundedEventually_check c d b q m I φ) := by
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · have hp := boundedEventually_check_preserves_invariant c d b q m I φ hcd σ P α k hn h
      simpa [boundedEventually_check, Judgement.EvaluatedInvariant, hk, hn,
        IntervalPredicate.Invariant] using hp
    · simp [boundedEventually_check, Judgement.EvaluatedInvariant, hk, hn,
        IntervalPredicate.Invariant]
  · simp [boundedEventually_check, Judgement.NonPredicateSatisfies, hk] at *

/-- All six `↑↓` `◇` branches preserve recursively evaluated
invariants, including finish and terminal-position cases. -/
theorem boundedEventually_preserves_evaluatedInvariant [DecidableEq Clock]
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hinv : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α (↑↓[c,d,b,q]◇[I]φ))
    (B : Judgement Clock Var) (hB : B ∈ (boundedEventually c d b q I φ).branches)
    (h : Judgement.NonPredicateSatisfies σ P α k B) : Judgement.EvaluatedInvariant σ P α k B := by
  simp only [boundedEventually, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl
  · exact boundedEventually_defer_evaluatedInvariant c d b q ○ I φ σ P α k hinv h
  · exact boundedEventually_defer_evaluatedInvariant c d b q ● I φ σ P α k hinv h
  · by_cases hk : k.1 < P.size
    · simp [boundedEventually_finish, Judgement.EvaluatedInvariant, IntervalPredicate.Invariant, hk]
    · simp [boundedEventually_finish, Judgement.NonPredicateSatisfies, hk,
        IntervalPredicate.Invariant] at *
  · by_cases hk : k.1 < P.size
    · simp [boundedEventually_finish, Judgement.EvaluatedInvariant, IntervalPredicate.Invariant, hk]
    · simp [boundedEventually_finish, Judgement.NonPredicateSatisfies, hk,
        IntervalPredicate.Invariant] at *
  · exact boundedEventually_check_evaluatedInvariant c d b q ○ I φ hcd σ P α k h
  · exact boundedEventually_check_evaluatedInvariant c d b q ● I φ hcd σ P α k h

/-- Recursive invariant checking for `↑` `□` defer, without freshness. -/
theorem upperAlways_defer_evaluatedInvariant [DecidableEq Clock]
    (c d : Clock) (b m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (h : Judgement.NonPredicateSatisfies σ P α k (upperAlways_defer c d b m I φ)) :
    Judgement.EvaluatedInvariant σ P α k (upperAlways_defer c d b m I φ) := by
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · have hp := upperAlways_defer_preserves_invariant c d b m I φ σ P α k hn
      simpa [upperAlways_defer, Judgement.EvaluatedInvariant, hk, hn] using hp
    · simp [upperAlways_defer, Judgement.EvaluatedInvariant, hk, hn]
  · simp [upperAlways_defer, Judgement.NonPredicateSatisfies, hk] at *

/-- Recursive invariant checking for `↑` `□` check/reset. -/
theorem upperAlways_check_evaluatedInvariant [DecidableEq Clock]
    (c d : Clock) (b m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (h : Judgement.NonPredicateSatisfies σ P α k (upperAlways_check c d b m I φ)) :
    Judgement.EvaluatedInvariant σ P α k (upperAlways_check c d b m I φ) := by
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · have hp := upperAlways_check_preserves_invariant c d m I φ hcd σ P α k hn
      simpa [upperAlways_check, Judgement.EvaluatedInvariant, hk, hn,
        IntervalPredicate.Invariant] using hp
    · simp [upperAlways_check, Judgement.EvaluatedInvariant, hk, hn, IntervalPredicate.Invariant]
  · simp [upperAlways_check, Judgement.NonPredicateSatisfies, hk] at *

/-- All six `↑` `□` branches preserve recursively evaluated invariants.
No source invariant or stability is needed. -/
theorem upperAlways_preserves_evaluatedInvariant [DecidableEq Clock]
    (c d : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (B : Judgement Clock Var) (hB : B ∈ (upperAlways c d b I φ).branches)
    (h : Judgement.NonPredicateSatisfies σ P α k B) : Judgement.EvaluatedInvariant σ P α k B := by
  simp only [upperAlways, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl
  · exact upperAlways_defer_evaluatedInvariant c d b ○ I φ σ P α k h
  · exact upperAlways_defer_evaluatedInvariant c d b ● I φ σ P α k h
  · by_cases hk : k.1 < P.size
    · simp [Judgement.EvaluatedInvariant, hk]
    · simp_all [Judgement.NonPredicateSatisfies]
  · by_cases hk : k.1 < P.size
    · simp [Judgement.EvaluatedInvariant, IntervalPredicate.Invariant, hk]
    · simp_all [Judgement.NonPredicateSatisfies]
  · exact upperAlways_check_evaluatedInvariant c d b ○ I φ hcd σ P α k h
  · exact upperAlways_check_evaluatedInvariant c d b ● I φ hcd σ P α k h

/-- Recursive invariant checking for `↑` `◇` defer. -/
theorem upperEventually_defer_evaluatedInvariant [DecidableEq Clock]
    (c d : Clock) (b m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hinv : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α (↑[c,b]◇[I]φ))
    (h : Judgement.NonPredicateSatisfies σ P α k (upperEventually_defer c d b m I φ)) :
    Judgement.EvaluatedInvariant σ P α k (upperEventually_defer c d b m I φ) := by
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · have hp := upperEventually_defer_preserves_invariant c d b m I φ hcd σ P α k hn (hinv hk) h
      simpa [upperEventually_defer, Judgement.EvaluatedInvariant, hk, hn] using hp
    · simp [upperEventually_defer, Judgement.EvaluatedInvariant, hk, hn]
  · simp [upperEventually_defer, Judgement.NonPredicateSatisfies, hk,
      IntervalPredicate.Invariant] at *

/-- Recursive invariant checking for the positive-lower-bound check schema. -/
theorem upperEventually_check_evaluatedInvariant [DecidableEq Clock]
    (c d : Clock) (b m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (hpos : 0 < I.lower)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (h : Judgement.NonPredicateSatisfies σ P α k (upperEventually_check c d b m I φ)) :
    Judgement.EvaluatedInvariant σ P α k (upperEventually_check c d b m I φ) := by
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · have hp := upperEventually_check_preserves_invariant c d b m I φ hcd hpos σ P α k hn h
      simpa [upperEventually_check, Judgement.EvaluatedInvariant, hk, hn,
        IntervalPredicate.Invariant] using hp
    · simp [upperEventually_check, Judgement.EvaluatedInvariant, hk, hn,
        IntervalPredicate.Invariant]
  · simp [upperEventually_check, Judgement.NonPredicateSatisfies, hk] at *

/-- All `↑` `◇` branches preserve recursively evaluated invariants.
The branch list supplies positivity exactly where check/reset needs it. -/
theorem upperEventually_preserves_evaluatedInvariant [DecidableEq Clock]
    (c d : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hinv : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α (↑[c,b]◇[I]φ))
    (B : Judgement Clock Var) (hB : B ∈ (upperEventually c d b I φ).branches)
    (h : Judgement.NonPredicateSatisfies σ P α k B) : Judgement.EvaluatedInvariant σ P α k B := by
  classical
  by_cases hz : I.lower = 0
  · simp only [upperEventually, if_pos hz, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hB
    rcases hB with rfl | rfl | rfl
    · exact upperEventually_defer_evaluatedInvariant c d b ○ I φ hcd σ P α k hinv h
    · exact upperEventually_defer_evaluatedInvariant c d b ● I φ hcd σ P α k hinv h
    · by_cases hk : k.1 < P.size
      · simp [Judgement.EvaluatedInvariant, IntervalPredicate.Invariant, hk]
      · simp_all [Judgement.NonPredicateSatisfies, Judgement.EvaluatedInvariant]
  · have hpos : 0 < I.lower := lt_of_le_of_ne I.lower_nonnegative (Ne.symm hz)
    simp only [upperEventually, if_neg hz, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hB
    rcases hB with rfl | rfl | rfl | rfl
    · exact upperEventually_defer_evaluatedInvariant c d b ○ I φ hcd σ P α k hinv h
    · exact upperEventually_defer_evaluatedInvariant c d b ● I φ hcd σ P α k hinv h
    · exact upperEventually_check_evaluatedInvariant c d b ○ I φ hcd hpos σ P α k h
    · exact upperEventually_check_evaluatedInvariant c d b ● I φ hcd hpos σ P α k h

/-- The zero reset and actual declaring marker establish the invariant
throughout an eventually opening branch. -/
theorem openEventually_branch_evaluatedInvariant [DecidableEq Clock]
    (c : Clock) (m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (h : Judgement.NonPredicateSatisfies σ P α k (⟦c ↦ᶜ 0⟧ ·ⱼ
      ((↑[c,m]◇[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[m]))) :
    Judgement.EvaluatedInvariant σ P α k (⟦c ↦ᶜ 0⟧ ·ⱼ
      ((↑[c,m]◇[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[m])) := by
  by_cases hk : k.1 < P.size
  · simp only [Judgement.NonPredicateSatisfies, dif_pos hk] at h
    have hp := IntervalPredicate.upper_eventually_invariant_of_zero
      (P.interval ⟨k.1, hk⟩) ((⟦c ↦ᶜ 0⟧).apply α) c m I φ
      (P.nonempty _) (ClockResetSet.apply_singleton_self c 0 α) h.2.symm
    simpa [Judgement.EvaluatedInvariant, hk] using hp
  · simp_all [Judgement.NonPredicateSatisfies, Judgement.EvaluatedInvariant]

/-- Both eventually opening branches preserve recursively evaluated
invariants without any source-invariant or stability assumption. -/
theorem openEventually_preserves_evaluatedInvariant [DecidableEq Clock]
    (c : Clock) (I : BoundedTimeInterval) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (B : Judgement Clock Var) (hB : B ∈ (openEventually c I φ).branches)
    (h : Judgement.NonPredicateSatisfies σ P α k B) : Judgement.EvaluatedInvariant σ P α k B := by
  simp only [openEventually, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl
  · exact openEventually_branch_evaluatedInvariant c ○ I φ σ P α k h
  · exact openEventually_branch_evaluatedInvariant c ● I φ σ P α k h

/-- Both always opening branches have trivial `↑` `□` invariants;
branch satisfaction ensures a valid declaring position. -/
theorem openAlways_preserves_evaluatedInvariant [DecidableEq Clock]
    (c : Clock) (I : BoundedTimeInterval) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (B : Judgement Clock Var) (hB : B ∈ (openAlways c I φ).branches)
    (h : Judgement.NonPredicateSatisfies σ P α k B) : Judgement.EvaluatedInvariant σ P α k B := by
  simp only [openAlways, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl <;> by_cases hk : k.1 < P.size
  · simp [Judgement.EvaluatedInvariant, IntervalPredicate.Invariant, hk]
  · simp_all [Judgement.NonPredicateSatisfies]
  · simp [Judgement.EvaluatedInvariant, IntervalPredicate.Invariant, hk]
  · simp_all [Judgement.NonPredicateSatisfies, Judgement.EvaluatedInvariant]

end STLTableau.ExpansionRule
