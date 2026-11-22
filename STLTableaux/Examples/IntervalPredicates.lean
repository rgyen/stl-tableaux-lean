import STLTableaux.Semantics.IntervalSemantics

/-! Predicate scopes (Example 3.4), reset judgements (Example 3.6),
satisfaction on a partition (Example 3.8), and free clocks (Example C.4). -/

namespace STLTableau.Examples.Section3
open scoped STL

private theorem mem_marked (J : MarkedInterval) (t : ℝ) :
    t ∈ J ↔ J.Mem t := Iff.rfl
private theorem mem_scope (S : Scope) (t : ℝ) :
    t ∈ S ↔ S.toMarkedInterval.Mem t := Iff.rfl
attribute [local simp] mem_marked mem_scope

inductive Clock where | c | d deriving DecidableEq
def nonnegative : Formula Unit := .atom ⟨1, fun _ => (), fun v => v 0, .ge⟩
def timing45 : BoundedTimeInterval := ⟨4,5,by norm_num,by norm_num⟩
def timing34 : BoundedTimeInterval := ⟨3,4,by norm_num,by norm_num⟩
def timing24 : BoundedTimeInterval := ⟨2,4,by norm_num,by norm_num⟩
def alwaysExample : IntervalPredicate Clock Unit := ↑[Clock.c,○] □[timing45] nonnegative
def eventuallyExample : IntervalPredicate Clock Unit :=
  ↑↓[Clock.c,Clock.d,●,●] ◇[timing34] nonnegative
def alwaysCell : MarkedInterval := ⟨5,7,●,○⟩
def eventuallyCell : MarkedInterval := ⟨4,6,○,○⟩

/-- Example 3.4. On `[5,7)` with `c = 1`, the always predicate has scope `(4,7)`. -/
theorem always_scope (α : ClockValuation Clock) (hc : α .c = 1) :
    alwaysExample.scope alwaysCell α = ⟨○,4,7,○⟩ := by
  simp [alwaysExample, IntervalPredicate.scope, alwaysCell, hc]; norm_num

theorem eventually_scope (α : ClockValuation Clock) (hc : α .c = 3) (hd : α .d = 1) :
    eventuallyExample.scope eventuallyCell α = ⟨●,1,3,●⟩ := by
  simp [eventuallyExample, IntervalPredicate.scope, eventuallyCell, hc, hd]; norm_num

/-- Example 3.4. The always predicate checks `(8,12)` within the signal domain. -/
theorem always_domain_clipped (σ : FiniteSignal Unit) (α : ClockValuation Clock)
    (hc : α .c = 1) :
    STLTableau.predicateSatisfies σ alwaysCell α alwaysExample ↔
      ∀ t : σ.Time, 8 < t.val ∧ t.val < 12 → 0 ≤ σ.value t () := by
  norm_num [STLTableau.predicateSatisfies, alwaysExample, IntervalPredicate.scope,
    IntervalPredicate.alwaysRegion, alwaysCell, timing45, hc, Scope.carrier,
    Scope.toMarkedInterval, MarkedInterval.carrier, MarkedInterval.Mem,
    Marker.Includes, nonnegative, FiniteSignal.Satisfies, AtomicProposition.Holds,
    RealRelation.Holds]

theorem always_untruncated (σ : FiniteSignal Unit) (α : ClockValuation Clock)
    (hc : α .c = 1) (horizon : 12 ≤ σ.horizon)
    (sat : STLTableau.predicateSatisfies σ alwaysCell α alwaysExample)
    (t : ℝ) (ht : 8 < t ∧ t < 12) :
    0 ≤ σ.value ⟨t, by constructor <;> linarith⟩ () :=
  (always_domain_clipped σ α hc).1 sat _ ht

theorem eventually_witnesses (σ : FiniteSignal Unit) (α : ClockValuation Clock)
    (hc : α .c = 3) (hd : α .d = 1) :
    STLTableau.predicateSatisfies σ eventuallyCell α eventuallyExample ↔
      ∀ t : ℝ, 1 ≤ t ∧ t ≤ 3 →
        ∃ u : σ.Time, u.val ∈ (TimeInterval.bounded timing34).translate t ∧
          0 ≤ σ.value u () := by
  norm_num [STLTableau.predicateSatisfies, eventuallyExample, IntervalPredicate.scope,
    eventuallyCell, hc, hd, Scope.toMarkedInterval,
    MarkedInterval.Mem, Marker.Includes, nonnegative,
    FiniteSignal.Satisfies, AtomicProposition.Holds, RealRelation.Holds]

def reset0 : ClockResetSet Clock := ⟦Clock.c ↦ᶜ 0⟧
def reset73 : ClockResetSet Clock := (⟦Clock.c ↦ᶜ 7⟧).union ⟦Clock.d ↦ᶜ 3⟧
def upper24 : IntervalPredicate Clock Unit := ↑[Clock.c,●] □[timing24] nonnegative
def bounded24 : IntervalPredicate Clock Unit := ↑↓[Clock.c,Clock.d,●,○] □[timing24] nonnegative
/-- Example 3.6. The reset scopes the interval predicate in the `↑` form. -/
def psi1 : Judgement Clock Unit := .conj (.reset reset0 (.predicate upper24)) (.leftMarker ●)
def psi2 : Judgement Clock Unit := .conj (.reset reset73 (.predicate bounded24))
  (.conj (.predicate (.plain nonnegative)) (.next .terminal))

theorem reset_values (α : ClockValuation Clock) :
    reset0.apply α .c = 0 ∧ reset73.apply α .c = 7 ∧ reset73.apply α .d = 3 := by
  constructor
  · rfl
  · constructor <;> rfl

def cells : Fin 3 → MarkedInterval := ![⟨0,1,●,●⟩, ⟨1,3,○,●⟩, ⟨3,4,○,○⟩]

/-- Example 3.8. The partition consists of `[0,1]`, `(1,3]`, and `(3,4)`. -/
def partition : IntervalPartition (Set.Ico (0 : ℝ) 4) where
  size := 3
  interval := cells
  nonempty := by
    intro i; fin_cases i <;> [use 0; use 2; use (7/2 : ℝ)] <;>
      norm_num [cells, MarkedInterval.carrier, MarkedInterval.Mem, Marker.Includes]
  pairwiseDisjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro t hi hj
    fin_cases i <;> fin_cases j <;>
      simp_all [cells, MarkedInterval.carrier, MarkedInterval.Mem, Marker.Includes] <;>
      rcases hi with ⟨hi₁, hi₂⟩ <;> rcases hj with ⟨hj₁, hj₂⟩ <;> linarith
  covers := by
    ext t
    suffices ((0 ≤ t ∧ t ≤ 1) ∨ (1 < t ∧ t ≤ 3) ∨ (3 < t ∧ t < 4)) ↔
        (0 ≤ t ∧ t < 4) by
      simpa [cells, Set.mem_iUnion, Fin.exists_fin_succ, MarkedInterval.carrier,
        MarkedInterval.Mem, Marker.Includes] using this
    constructor
    · intro h
      rcases h with h | h | h <;> rcases h with ⟨h₁,h₂⟩ <;>
        constructor <;> linarith
    · intro h
      by_cases h1 : t ≤ 1
      · left; exact ⟨h.1, h1⟩
      · by_cases h3 : t ≤ 3
        · right; left; exact ⟨by linarith, h3⟩
        · right; right; exact ⟨by linarith, h.2⟩
  ordered := by
    intro i j h; fin_cases i <;> fin_cases j <;> norm_num [cells] at *

theorem first_judgement (σ : FiniteSignal Unit) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (hs : P.size = 3)
    (hcell : P.interval ⟨0, by omega⟩ = cells 0) :
    STLTableau.satisfies σ P α ⟨0,by omega⟩ psi1 ↔
      STLTableau.predicateSatisfies σ (cells 0) (reset0.apply α) upper24 := by
  simp [psi1, STLTableau.satisfies, show 0 < P.size by omega, hcell, cells]

theorem last_judgement (σ : FiniteSignal Unit) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (hs : P.size = 3)
    (hcell : P.interval ⟨2, by omega⟩ = cells 2) :
    STLTableau.satisfies σ P α ⟨2,by omega⟩ psi2 ↔
      STLTableau.predicateSatisfies σ (cells 2) (reset73.apply α) bounded24 ∧
      STLTableau.predicateSatisfies σ (cells 2) α (.plain nonnegative) := by
  simp [psi2, STLTableau.satisfies, hcell, hs]

def signal4 (v : {t : ℝ // 0 ≤ t ∧ t < 4} → Unit → ℝ) : FiniteSignal Unit :=
  ⟨4, by norm_num, v⟩

theorem partition_first (v : {t : ℝ // 0 ≤ t ∧ t < 4} → Unit → ℝ)
    (α : ClockValuation Clock) :
    STLTableau.satisfies (signal4 v) STLTableau.Examples.Section3.partition α
        ⟨0, by norm_num [partition]⟩ psi1 ↔
      STLTableau.predicateSatisfies (signal4 v) (cells 0) (reset0.apply α) upper24 :=
  first_judgement _ _ _ rfl rfl

theorem partition_last (v : {t : ℝ // 0 ≤ t ∧ t < 4} → Unit → ℝ)
    (α : ClockValuation Clock) :
    STLTableau.satisfies (signal4 v) STLTableau.Examples.Section3.partition α
        ⟨2, by norm_num [partition]⟩ psi2 ↔
      STLTableau.predicateSatisfies (signal4 v) (cells 2) (reset73.apply α) bounded24 ∧
      ∀ t : (signal4 v).Time, t.val ∈ cells 2 → 0 ≤ (signal4 v).value t () := by
  rw [last_judgement _ _ _ rfl rfl]
  rfl

def reset2 : ClockResetSet Clock := ⟦Clock.c ↦ᶜ 2⟧
def reset5 : ClockResetSet Clock := ⟦Clock.d ↦ᶜ 5⟧
/-- Example C.4. Only `c` occurs free in `c > 1`. -/
def clockExample : Judgement Clock Unit := .clock .c .gt 1

theorem reset_disjoint : Disjoint reset2.clocks reset5.clocks := by
  apply Set.disjoint_left.mpr
  rintro clock ⟨a, ha⟩ ⟨b, hb⟩
  cases clock
  · change none = some b at hb; cases hb
  · change none = some a at ha; cases ha

theorem reset_consistent : reset2.Consistent reset5 := by
  intro clock a b h₁ h₂
  cases clock
  · change none = some b at h₂; cases h₂
  · change none = some a at h₁; cases h₁

theorem free_clock : Judgement.freeClocks clockExample = {Clock.c} := rfl

theorem reset_assignment (α : ClockValuation Clock) :
    reset5.apply (reset2.apply α) = (reset2.union reset5).apply α :=
  ClockResetSet.apply_apply_eq_union reset2 reset5 reset_consistent α

theorem reset_clock_satisfaction (σ : FiniteSignal Unit) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    STLTableau.satisfies σ P (reset5.apply (reset2.apply α)) k clockExample ↔
      STLTableau.satisfies σ P ((reset2.union reset5).apply α) k clockExample := by
  rw [reset_assignment]

/-- In Example C.4, resetting `c` to 2 makes `c > 1` true under either reset set. -/
theorem reset_clock_true (σ : FiniteSignal Unit) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    STLTableau.satisfies σ P (reset5.apply (reset2.apply α)) k clockExample := by
  change (2 : NNReal) > 1
  norm_num

/-- Resetting `d` preserves satisfaction because `d` does not occur in `c > 1`. -/
theorem other_clock_irrelevant (σ : FiniteSignal Unit) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    STLTableau.satisfies σ P (reset5.apply α) k clockExample ↔
      STLTableau.satisfies σ P α k clockExample := Iff.rfl

end STLTableau.Examples.Section3
