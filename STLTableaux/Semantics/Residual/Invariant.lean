/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Semantics.Residual.IntervalPredicate

/-! # Interval-predicate invariants

Clock conditions for the interval predicate invariants (Appendix C.5).
-/

namespace STLTableau.IntervalPredicate

open scoped STL

variable {Clock Var : Type*}

/-- The predicate invariant, evaluated at a declaring interval and
clock valuation. The marker implication represents `¬b ∨ J.leftBoundary`. -/
def Invariant (J : MarkedInterval) (α : ClockValuation Clock) :
    IntervalPredicate Clock Var → Prop
  | .plain _ => True
  | .upper _ _ .always _ _ => True
  | .upper c b .eventually I _ =>
      ((α c : ℝ) <[Marker.imp b J.leftBoundary] I.upper) ∧
      ((0 : ℝ) <[Marker.conj b J.rightBoundary]
        ((α c : ℝ) + (J.right - J.left)))
  | .bounded c d b q .eventually I _ =>
      ((α c : ℝ) <[Marker.imp b J.leftBoundary] I.upper) ∧
      ((α d : ℝ) <[Marker.conj b q] (α c : ℝ))
  | .bounded c d b q .always I _ =>
      ((α d : ℝ) <[Marker.conj b q] ((α c : ℝ) + (I.upper - I.lower))) ∧
      ((α d : ℝ) <[Marker.conj J.leftBoundary q] I.upper)

/-- Predicate invariants depend only on the clocks occurring in the
predicate. -/
theorem invariant_congr (J : MarkedInterval) (α β : ClockValuation Clock)
    (p : IntervalPredicate Clock Var)
    (hagree : ∀ c ∈ p.clockSet, α c = β c) :
    Invariant J α p ↔ Invariant J β p := by
  cases p with
  | plain φ => simp [Invariant]
  | upper c b kind I φ =>
      have hc := hagree c (by simp [IntervalPredicate.clockSet])
      cases kind <;> simp [Invariant, hc]
  | bounded c d b q kind I φ =>
      have hc := hagree c (by simp [IntervalPredicate.clockSet])
      have hd := hagree d (by simp [IntervalPredicate.clockSet])
      cases kind <;> simp [Invariant, hc, hd]

/-- The marked bounds put the origin in the shift `J - I`: the translated
window meets `J`, including equality when the endpoints are included. -/
theorem exists_current_point_of_marked_bounds
    (J : MarkedInterval) (α : ClockValuation Clock)
    (c : Clock) (b : Marker) (I : BoundedTimeInterval)
    (hJ : J.carrier.Nonempty)
    (hreach : (α c : ℝ) <[Marker.imp b J.leftBoundary] I.upper)
    (t : ℝ)
    (hl : J.left - (α c : ℝ) <[b] t)
    (hcut : t + I.lower <[J.rightBoundary] J.right) :
    ∃ u ∈ J, u ∈ (I : TimeInterval).translate t := by
  let K : MarkedInterval := ⟨t + I.lower, t + I.upper, ●, ●⟩
  have hK : K.carrier.Nonempty := (MarkedInterval.nonempty_iff K).2
    (Or.inl (by dsimp [K]; linarith [I.nonSingular]))
  have hJK : J.left <[Marker.conj J.leftBoundary K.rightBoundary] K.right := by
    change J.left < t + I.upper ∨ (J.left = t + I.upper ∧ _)
    rcases hreach with hi | ⟨hi, hm⟩
    · left; rcases hl with hl | ⟨hl, _⟩ <;> linarith
    · rcases hl with hl | ⟨hl, hb⟩
      · left; linarith
      · right
        exact ⟨by linarith, (Marker.includes_conj _ _).2
          ⟨(Marker.includes_imp _ _).1 hm hb, trivial⟩⟩
  have hKJ : K.left <[Marker.conj K.leftBoundary J.rightBoundary] J.right := by
    change t + I.lower < J.right ∨ (t + I.lower = J.right ∧ _)
    rcases hcut with hlt | ⟨heq, hm⟩
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, (Marker.includes_conj _ _).2 ⟨trivial, hm⟩⟩
  obtain ⟨x, hxJ, hxK⟩ := MarkedInterval.inter_nonempty_of_cross_bounds J K hJ hK hJK hKJ
  refine ⟨x, hxJ, ?_⟩
  have hxl := MarkedInterval.left_le_of_mem hxK
  have hxr := MarkedInterval.le_right_of_mem hxK
  change t + I.lower ≤ x at hxl
  change x ≤ t + I.upper at hxr
  change I.lower ≤ x - t ∧ x - t ≤ I.upper
  constructor <;> linarith

/-- A uniformly true current interval supplies a witness when the marked
bounds put the origin in its shifted region. -/
theorem exists_current_witness_of_marked_bounds
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hJ : J.carrier.Nonempty) (hDomain : J.carrier ⊆ σ.domain)
    (hreach : (α c : ℝ) <[Marker.imp b J.leftBoundary] I.upper)
    (hφ : (σ,J,α)⊨ᵢ(.plain φ)) (t : ℝ)
    (hl : J.left - (α c : ℝ) <[b] t)
    (hcut : t + I.lower <[J.rightBoundary] J.right) :
    ∃ u : σ.Time, u.1 ∈ (I : TimeInterval).translate t ∧
      InCurrentSuffix J u.1 ∧ (σ,u)⊨φ := by
  obtain ⟨u, huJ, huI⟩ := exists_current_point_of_marked_bounds J α c b I hJ hreach t hl hcut
  let w : σ.Time := ⟨u, hDomain huJ⟩
  exact ⟨w, huI, huJ.1, hφ w huJ⟩

/-- `↑↓` `◇` specialization of the marked witness bounds. -/
theorem exists_current_witness_of_bounded_eventually_invariant
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hJ : J.carrier.Nonempty) (hDomain : J.carrier ⊆ σ.domain)
    (hinv : Invariant J α (↑↓[c,d,b,q]◇[I]φ))
    (hφ : (σ,J,α)⊨ᵢ(.plain φ)) (t : ℝ)
    (ht : t ∈ scope J α (↑↓[c,d,b,q]◇[I]φ))
    (hcut : t + I.lower <[J.rightBoundary] J.right) :
    ∃ u : σ.Time, u.1 ∈ (I : TimeInterval).translate t ∧
      InCurrentSuffix J u.1 ∧ (σ,u)⊨φ :=
  exists_current_witness_of_marked_bounds σ J α c b I φ hJ hDomain hinv.1 hφ t ht.1 hcut

/-- With zero lower bound, the whole `↑` scope is covered by current
witnesses. The `↑` `◇` invariant supplies the left reach. -/
theorem satisfies_upper_eventually_of_plain_of_zero
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hJ : J.carrier.Nonempty) (hDomain : J.carrier ⊆ σ.domain)
    (hzero : I.lower = 0) (hinv : Invariant J α (↑[c,b]◇[I]φ))
    (hφ : (σ,J,α)⊨ᵢ(.plain φ)) : (σ,J,α)⊨ᵢ(↑[c,b]◇[I]φ) := by
  intro t ht
  apply exists_current_witness_of_marked_bounds σ J α c b I φ hJ hDomain hinv.1 hφ t ht.1
  rw [hzero, add_zero]
  exact ht.2

/-- The finish guard puts every origin up to the tracked right endpoint
on the current side of the split, with its marker taken into account. -/
theorem eventually_finish_cut (J : MarkedInterval) (α : ClockValuation Clock)
    (d : Clock) (q : Marker) (a : ℝ) {t : ℝ}
    (hr : t <[q] (J.left - (α d : ℝ)))
    (hg : a <[Marker.imp q J.rightBoundary] ((α d : ℝ) + (J.right - J.left))) :
    t + a <[J.rightBoundary] J.right := by
  rcases hg with hg | ⟨hg, hm⟩
  · left; rcases hr with hr | ⟨hr, _⟩ <;> linarith
  · rcases hr with hr | ⟨hr, hq⟩
    · left; linarith
    · exact Or.inr ⟨by linarith, (Marker.includes_imp _ _).1 hm hq⟩

/-- The finish guard makes the current-witness lemma apply to the whole scope. -/
theorem satisfies_bounded_eventually_of_plain_of_finish
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hJ : J.carrier.Nonempty) (hDomain : J.carrier ⊆ σ.domain)
    (hinv : Invariant J α (↑↓[c,d,b,q]◇[I]φ))
    (hg : I.lower <[Marker.imp q J.rightBoundary]
      ((α d : ℝ) + (J.right - J.left)))
    (hφ : (σ,J,α)⊨ᵢ(.plain φ)) : (σ,J,α)⊨ᵢ(↑↓[c,d,b,q]◇[I]φ) := by
  intro t ht
  exact exists_current_witness_of_bounded_eventually_invariant
    σ J α c d b q I φ hJ hDomain hinv hφ t ht
    (eventually_finish_cut J α d q I.lower ht.2 hg)

/-- The residual invariant ensures that a `↑↓` `◇` scope is nonempty. -/
theorem bounded_eventually_scope_nonempty_of_invariant
    (J : MarkedInterval) (α : ClockValuation Clock) (c d : Clock)
    (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (h : Invariant J α (↑↓[c,d,b,q]◇[I]φ)) :
    (scope J α (↑↓[c,d,b,q]◇[I]φ)).carrier.Nonempty := by
  apply (MarkedInterval.nonempty_iff _).2
  change J.left - (α c : ℝ) <[Marker.conj b q] J.left - (α d : ℝ)
  rcases h.2 with hlt | ⟨heq, hm⟩
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨by linarith, hm⟩

/-- The first conjunct of the `↑↓` `□` invariant makes the shifted
checking region nonempty. Intersection with the signal suffix is separate. -/
theorem bounded_always_region_nonempty_of_invariant
    (J : MarkedInterval) (α : ClockValuation Clock) (c d : Clock)
    (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (h : Invariant J α (↑↓[c,d,b,q]□[I]φ)) :
    (alwaysRegion (scope J α (↑↓[c,d,b,q]□[I]φ)) I).carrier.Nonempty := by
  apply (MarkedInterval.nonempty_iff _).2
  change J.left - (α c : ℝ) + I.lower <[Marker.conj b q]
    J.left - (α d : ℝ) + I.upper
  rcases h.1 with hlt | ⟨heq, hm⟩
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨by linarith, hm⟩

/-- Nonemptiness of the `↑` `◇` scope required by its invariant. -/
theorem upper_eventually_scope_nonempty_of_invariant
    (J : MarkedInterval) (α : ClockValuation Clock) (c : Clock)
    (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (h : Invariant J α (↑[c,b]◇[I]φ)) :
    (scope J α (↑[c,b]◇[I]φ)).carrier.Nonempty := by
  apply (MarkedInterval.nonempty_iff _).2
  change J.left - (α c : ℝ) <[Marker.conj b J.rightBoundary] J.right
  rcases h.2 with hlt | ⟨heq, hm⟩
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨by linarith, hm⟩

/-- Under the `↑↓` `□` invariant, the right endpoint reaches the
declaring interval. Equality requires both endpoint markers to be closed. -/
theorem bounded_always_right_reaches_of_invariant
    (J : MarkedInterval) (α : ClockValuation Clock) (c d : Clock)
    (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (h : Invariant J α (↑↓[c,d,b,q]□[I]φ)) :
    J.left <[Marker.conj J.leftBoundary q] J.left - (α d : ℝ) + I.upper := by
  rcases h.2 with hlt | ⟨heq, hm⟩
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨by linarith, hm⟩

/-- A checking region that reaches the current right endpoint from the left
overlaps the declaring interval under the invariant. Stability propagates
the resulting truth point to the whole interval, including singleton cases. -/
theorem satisfies_plain_of_bounded_always_of_marked_overlap
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hJ : J.carrier.Nonempty) (hDomain : J.carrier ⊆ σ.domain)
    (hcut : J.left - (α c : ℝ) + I.lower <[Marker.conj b J.rightBoundary] J.right)
    (hinv : Invariant J α (↑↓[c,d,b,q]□[I]φ))
    (hstable : σ.Stable J φ) (h : (σ,J,α)⊨ᵢ(↑↓[c,d,b,q]□[I]φ)) :
    (σ,J,α)⊨ᵢ(.plain φ) := by
  let K := (alwaysRegion (scope J α (↑↓[c,d,b,q]□[I]φ)) I).toMarkedInterval
  have hK : K.carrier.Nonempty :=
    bounded_always_region_nonempty_of_invariant J α c d b q I φ hinv
  have hcross : J.left <[Marker.conj J.leftBoundary K.rightBoundary] K.right :=
    bounded_always_right_reaches_of_invariant J α c d b q I φ hinv
  obtain ⟨x, hxJ, hxK⟩ := MarkedInterval.inter_nonempty_of_cross_bounds J K hJ hK hcross hcut
  let t : σ.Time := ⟨x, hDomain hxJ⟩
  have htφ : (σ,t)⊨φ := h t hxK hxJ.1
  intro u hu
  exact (hstable t u hxJ hu).1 htφ

/-- The `↑↓` `□` checking region meets the current suffix when its
left endpoint precedes the horizon. -/
theorem bounded_always_region_inter_suffix_nonempty_of_invariant
    (J : MarkedInterval) (α : ClockValuation Clock) (c d : Clock)
    (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var) (τ : ℝ)
    (h : Invariant J α (↑↓[c,d,b,q]□[I]φ))
    (hJ : J.left < τ) (hstart : J.left - (α c : ℝ) + I.lower < τ) :
    ((alwaysRegion (scope J α (↑↓[c,d,b,q]□[I]φ)) I).carrier ∩
      (⟨J.left, τ, J.leftBoundary, ○⟩ : MarkedInterval).carrier).Nonempty := by
  exact MarkedInterval.inter_suffix_nonempty _ J.left τ J.leftBoundary
    (bounded_always_region_nonempty_of_invariant J α c d b q I φ h)
    hJ hstart (bounded_always_right_reaches_of_invariant J α c d b q I φ h)

/-- The partition formulation: the declaring interval already
starts before the horizon by nonemptiness and domain coverage. -/
theorem bounded_always_partition_region_nonempty_of_invariant
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (i : Fin P.size)
    (α : ClockValuation Clock) (c d : Clock) (b q : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (h : Invariant (P.interval i) α (↑↓[c,d,b,q]□[I]φ))
    (hstart : (P.interval i).left - (α c : ℝ) + I.lower < σ.horizon) :
    ((alwaysRegion (scope (P.interval i) α (↑↓[c,d,b,q]□[I]φ)) I).carrier ∩
      (⟨(P.interval i).left, σ.horizon, (P.interval i).leftBoundary, ○⟩ :
        MarkedInterval).carrier).Nonempty := by
  have hJ : (P.interval i).left < σ.horizon := by
    obtain ⟨t, ht⟩ := P.nonempty i
    have htD : t ∈ σ.domain := by
      rw [← P.covers]
      exact Set.mem_iUnion.2 ⟨i, ht⟩
    exact (MarkedInterval.left_le_of_mem ht).trans_lt htD.2
  exact bounded_always_region_inter_suffix_nonempty_of_invariant
    (P.interval i) α c d b q I φ σ.horizon h hJ hstart

/-- The eventuality opening reset establishes its invariant when `lty`
selects the declaring interval's actual left marker. -/
theorem upper_eventually_invariant_of_zero
    (J : MarkedInterval) (α : ClockValuation Clock) (c : Clock)
    (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hne : J.carrier.Nonempty) (hc : α c = 0) (hb : b = J.leftBoundary) :
    Invariant J α (↑[c,b]◇[I]φ) := by
  constructor
  · left
    rw [hc, NNReal.coe_zero]
    exact I.lower_nonnegative.trans_lt I.nonSingular
  · rw [hc, NNReal.coe_zero, zero_add, hb]
    rcases (MarkedInterval.nonempty_iff J).1 hne with hlt | ⟨heq, hm⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, hm⟩

/-- Resetting the right clock to zero establishes both `↑↓` `□`
invariant conjuncts, irrespective of endpoint markers and the left clock. -/
theorem bounded_always_invariant_of_right_zero
    (J : MarkedInterval) (α : ClockValuation Clock) (c d : Clock)
    (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var) (hd : α d = 0) :
    Invariant J α (↑↓[c,d,b,q]□[I]φ) := by
  constructor
  · left
    rw [hd, NNReal.coe_zero]
    have hc := (α c).coe_nonneg
    linarith [I.nonSingular]
  · left
    rw [hd, NNReal.coe_zero]
    exact I.lower_nonnegative.trans_lt I.nonSingular

/-- Equal clock increments preserve the `↑↓` `◇` scope ordering;
the defer guard supplies the new declaring interval's reach condition. -/
theorem bounded_eventually_invariant_of_equal_increment
    (J K : MarkedInterval) (α β : ClockValuation Clock)
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (δ : ℝ) (hc : (β c : ℝ) = (α c : ℝ) + δ)
    (hd : (β d : ℝ) = (α d : ℝ) + δ)
    (hinv : Invariant J α (↑↓[c,d,b,q]◇[I]φ))
    (hg : (β c : ℝ) <[Marker.imp b K.leftBoundary] I.upper) :
    Invariant K β (↑↓[c,d,b,q]◇[I]φ) := by
  refine ⟨hg, ?_⟩
  rw [hc, hd]
  rcases hinv.2 with hlt | ⟨heq, hm⟩
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨by linarith, hm⟩

/-- The check/reset target's invariant follows from resetting its left
clock to the timing lower bound and retaining the right-clock guard. -/
theorem bounded_eventually_invariant_of_left_lower
    (J : MarkedInterval) (α : ClockValuation Clock) (c d : Clock)
    (q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hc : (α c : ℝ) = I.lower)
    (hd : (α d : ℝ) <[Marker.conj q J.leftBoundary] I.lower) :
    Invariant J α (↑↓[c,d,J.leftBoundary,q]◇[I]φ) := by
  constructor
  · left
    rw [hc]
    exact I.nonSingular
  · rw [hc]
    have hm : Marker.conj J.leftBoundary q = Marker.conj q J.leftBoundary := by
      cases J.leftBoundary <;> cases q <;> rfl
    rw [hm]
    exact hd

/-- Resetting the `↑↓` `□` left clock to the lower bound makes both
invariant conjuncts follow from the right-clock continuation guard. -/
theorem bounded_always_invariant_of_left_lower
    (J : MarkedInterval) (α : ClockValuation Clock) (c d : Clock)
    (q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hc : (α c : ℝ) = I.lower)
    (hd : (α d : ℝ) <[Marker.conj q J.leftBoundary] I.upper) :
    Invariant J α (↑↓[c,d,J.leftBoundary,q]□[I]φ) := by
  have hm : Marker.conj q J.leftBoundary = Marker.conj J.leftBoundary q := by
    cases q <;> cases J.leftBoundary <;> rfl
  rw [hm] at hd
  constructor
  · rw [hc]
    convert hd using 1
    ring
  · exact hd

/-- Equal clock increments preserve the `↑↓` `□` region ordering.
Together with the defer guard this also gives the next right-reach condition. -/
theorem bounded_always_invariant_of_equal_increment
    (J K : MarkedInterval) (α β : ClockValuation Clock)
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (δ : ℝ) (hc : (β c : ℝ) = (α c : ℝ) + δ)
    (hd : (β d : ℝ) = (α d : ℝ) + δ)
    (hinv : Invariant J α (↑↓[c,d,b,q]□[I]φ))
    (hg : (β c : ℝ) <[Marker.imp b K.leftBoundary] I.lower) :
    Invariant K β (↑↓[c,d,b,q]□[I]φ) := by
  have horder : (β d : ℝ) <[Marker.conj b q] ((β c : ℝ) + (I.upper - I.lower)) := by
    rw [hc, hd]
    rcases hinv.1 with hlt | ⟨heq, hm⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, hm⟩
  refine ⟨horder, ?_⟩
  rcases horder with hlt | ⟨heq, hm⟩
  · left
    have hle := hg.elim le_of_lt (fun h => h.1.le)
    linarith
  · rcases hg with hlt | ⟨heq', hm'⟩
    · left; linarith
    · right
      obtain ⟨hb, hq⟩ := (Marker.includes_conj _ _).1 hm
      exact ⟨by linarith, (Marker.includes_conj _ _).2
        ⟨(Marker.includes_imp _ _).1 hm' hb, hq⟩⟩

end STLTableau.IntervalPredicate
