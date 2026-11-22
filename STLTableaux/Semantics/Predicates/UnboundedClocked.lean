import STLTableaux.Semantics.Predicates.Predicates
import STLTableaux.Semantics.Invariants.Invariants
import STLTableaux.Semantics.Intervals.IntervalLemmas

/-! Unbounded clocked-predicate semantics and a finite-cap bridge.
The cap must account for the tracked scope, which may start before zero.
This module does not yet establish the unbounded expansion-rule catalogue. -/
namespace STLTableau.UnboundedClocked
open scoped STL
open STLTableau.IntervalPredicate
variable {Clock Var : Type*}

/-- The original endpoint-shift semantics specialized to `[a,∞)`.
In particular an inverted raw scope does not make an always predicate
vacuous: its checking region remains a ray. -/
def temporalSatisfies (σ : FiniteSignal Var) (kind : TemporalKind)
    (a : NNReal) (φ : Formula Var) (S : Scope) : Prop :=
  match kind with
  | .always => ∀ u : σ.Time, S.left + (a : ℝ) <[S.leftBoundary] u.1 → (σ, u) ⊨ φ
  | .eventually => ∀ t : ℝ, t ∈ S →
      ∃ u : σ.Time, (a : ℝ) ≤ u.1 - t ∧ (σ, u) ⊨ φ

/-- A finite cap is exact if it exceeds every relevant checking endpoint
and every possible witness delay. These conditions apply to arbitrary
scopes, including negative and inverted tracked endpoints. -/
theorem temporal_iff_finite (σ : FiniteSignal Var) (kind : TemporalKind)
    (I : BoundedTimeInterval) (a : NNReal) (φ : Formula Var) (S : Scope)
    (ha : I.lower = (a : ℝ))
    (hleft : σ.horizon - S.left ≤ I.upper)
    (hright : σ.horizon - S.right < I.upper) :
    temporalSatisfies σ kind a φ S ↔ STLTableau.temporalSatisfies σ kind I φ S := by
  cases kind with
  | always =>
      constructor
      · intro h u hu
        exact h u (by simpa only [alwaysRegion, Scope.toMarkedInterval, ha, MarkedLT] using hu.1)
      · intro h u hu
        apply h u
        constructor
        · simpa only [alwaysRegion, Scope.toMarkedInterval, ha, MarkedLT] using hu
        · left
          have huτ := u.2.2
          change u.1 < S.right + I.upper
          linarith
  | eventually =>
      constructor
      · intro h t ht
        obtain ⟨u, hu, hφ⟩ := h t ht
        refine ⟨u, ?_, hφ⟩
        change I.lower ≤ u.1 - t ∧ u.1 - t ≤ I.upper
        refine ⟨ha.symm ▸ hu, ?_⟩
        have htleft : S.left ≤ t := MarkedInterval.left_le_of_mem ht
        have huτ := u.2.2
        linarith
      · intro h t ht
        obtain ⟨u, hu, hφ⟩ := h t ht
        exact ⟨u, by simpa only [ha] using hu.1, hφ⟩

/-- Clocked predicates with an unbounded timing interval. -/
inductive Predicate (Clock Var : Type*) where
  | upper (c : Clock) (b : Marker) (kind : TemporalKind) (a : NNReal) (φ : Formula Var)
  | bounded (c d : Clock) (b q : Marker) (kind : TemporalKind) (a : NNReal) (φ : Formula Var)

def scope (J : MarkedInterval) (α : ClockValuation Clock) : Predicate Clock Var → Scope
  | .upper c b _ _ _ => ⟨b, J.left - α c, J.right, J.rightBoundary⟩
  | .bounded c d b q _ _ _ => ⟨b, J.left - α c, J.left - α d, q⟩

def satisfies (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock) :
    Predicate Clock Var → Prop
  | p@(.upper _ _ kind a φ) | p@(.bounded _ _ _ _ kind a φ) =>
      temporalSatisfies σ kind a φ (scope J α p)

/-- A concrete cap that accounts for both clock distances and the absolute
declaring endpoint. Its validity does not require the scope to lie in the
signal domain. -/
def cap (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c d : Clock) (a : NNReal) : ℝ :=
  (a : ℝ) + σ.horizon + |J.left| + (α c : ℝ) + (α d : ℝ) + 1

def cappedInterval (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c d : Clock) (a : NNReal) : BoundedTimeInterval where
  lower := a
  upper := cap σ J α c d a
  lower_nonnegative := a.coe_nonneg
  nonSingular := by
    have := σ.horizon_pos
    have := abs_nonneg J.left
    have := (α c).coe_nonneg
    have := (α d).coe_nonneg
    dsimp [cap]
    linarith

/-- Arbitrary `↑↓` scope unbounded predicates reduce to finite timing
without imposing a current-suffix restriction on witnesses. -/
theorem bounded_iff_capped (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c d : Clock) (b q : Marker)
    (kind : TemporalKind) (a : NNReal) (φ : Formula Var) :
    satisfies σ J α (.bounded c d b q kind a φ) ↔
      STLTableau.predicateSatisfies σ J α
        (.bounded c d b q kind (cappedInterval σ J α c d a) φ) := by
  have hc := (α c).coe_nonneg
  have hd := (α d).coe_nonneg
  have ha := a.coe_nonneg
  have hJ : -J.left ≤ |J.left| := neg_le_abs J.left
  have he := temporal_iff_finite σ kind (cappedInterval σ J α c d a) a φ
    (scope J α (.bounded c d b q kind a φ)) rfl
    (by dsimp [scope, cappedInterval, cap]; linarith)
    (by dsimp [scope, cappedInterval, cap]; linarith)
  simpa only [satisfies, STLTableau.bounded_temporal, scope, IntervalPredicate.scope] using he

/-- The analogous cap bridge for `↑` scopes. Nonempty declaring pieces
have `left ≤ right`, as supplied by every interval partition. -/
theorem upper_iff_capped (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c : Clock) (b : Marker)
    (kind : TemporalKind) (a : NNReal) (φ : Formula Var) (hJorder : J.left ≤ J.right) :
    satisfies σ J α (.upper c b kind a φ) ↔
      STLTableau.predicateSatisfies σ J α
        (.upper c b kind (cappedInterval σ J α c c a) φ) := by
  have hc := (α c).coe_nonneg
  have ha := a.coe_nonneg
  have hJ : -J.left ≤ |J.left| := neg_le_abs J.left
  have he := temporal_iff_finite σ kind (cappedInterval σ J α c c a) a φ
    (scope J α (.upper c b kind a φ)) rfl
    (by dsimp [scope, cappedInterval, cap]; linarith)
    (by dsimp [scope, cappedInterval, cap]; linarith)
  simpa only [satisfies, STLTableau.upper_temporal, scope, IntervalPredicate.scope] using he

def formula (kind : TemporalKind) (a : NNReal) (φ : Formula Var) : Formula Var :=
  match kind with
  | .always => □[TimeInterval.unbounded a] φ
  | .eventually => ◇[TimeInterval.unbounded a] φ

/-- Unlike raw scopes, formula evaluation starts at a nonnegative signal
time, so a cap at least the horizon suffices. -/
theorem formula_iff_finite (σ : FiniteSignal Var) (kind : TemporalKind)
    (I : BoundedTimeInterval) (a : NNReal) (φ : Formula Var)
    (ha : I.lower = (a : ℝ)) (hB : σ.horizon ≤ I.upper) (t : σ.Time) :
    ((σ, t) ⊨ formula kind a φ) ↔
      ((σ, t) ⊨ (match kind with
        | .always => □[(I : TimeInterval)] φ
        | .eventually => ◇[(I : TimeInterval)] φ)) := by
  have htranslate : ∀ u : σ.Time,
      u.1 ∈ (TimeInterval.unbounded a).translate t.1 ↔
        u.1 ∈ (I : TimeInterval).translate t.1 := by
    intro u
    change (a : ℝ) ≤ u.1 - t.1 ↔ I.lower ≤ u.1 - t.1 ∧ u.1 - t.1 ≤ I.upper
    rw [ha]
    constructor
    · intro h
      exact ⟨h, by linarith [u.2.2, t.2.1]⟩
    · exact And.left
  cases kind with
  | always => simp only [formula, FiniteSignal.satisfies_always_iff, htranslate]
  | eventually => simp only [formula, FiniteSignal.satisfies_eventually_iff, htranslate]

/-- Exact unbounded opening schema for both temporal operators, with the
actual current marker. No clock-dependent cap remains in the conclusion. -/
theorem plain_iff_upper_zero (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c : Clock) (b : Marker) (kind : TemporalKind)
    (a : NNReal) (φ : Formula Var) (hne : J.carrier.Nonempty)
    (hD : J.carrier ⊆ σ.domain) (hc : (α c : ℝ) = 0) (hb : b = J.leftBoundary) :
    (∀ t : σ.Time, t.1 ∈ J → (σ, t) ⊨ formula kind a φ) ↔
      satisfies σ J α (.upper c b kind a φ) := by
  let I := cappedInterval σ J α c c a
  have hB : σ.horizon ≤ I.upper := by
    have := a.coe_nonneg
    have := (α c).coe_nonneg
    have := abs_nonneg J.left
    dsimp [I, cappedInterval, cap]
    linarith
  have hplain : (∀ t : σ.Time, t.1 ∈ J → (σ, t) ⊨ formula kind a φ) ↔
      STLTableau.predicateSatisfies σ J α (.plain (match kind with
        | .always => □[(I : TimeInterval)] φ
        | .eventually => ◇[(I : TimeInterval)] φ)) := by
    constructor
    · intro h t ht
      exact (formula_iff_finite σ kind I a φ rfl hB t).1 (h t ht)
    · intro h t ht
      exact (formula_iff_finite σ kind I a φ rfl hB t).2 (h t ht)
  have hopen : STLTableau.predicateSatisfies σ J α (.plain (match kind with
        | .always => □[(I : TimeInterval)] φ
        | .eventually => ◇[(I : TimeInterval)] φ)) ↔
      STLTableau.predicateSatisfies σ J α (.upper c b kind I φ) := by
    subst b
    cases kind with
    | always => exact STLTableau.plain_always_iff_upper_zero σ J α c I φ hc hne hD
    | eventually => exact STLTableau.plain_eventually_iff_upper_zero σ J α c I φ hc hD
  obtain ⟨x, hx⟩ := hne
  have horder := (MarkedInterval.left_le_of_mem hx).trans (MarkedInterval.le_right_of_mem hx)
  cases kind <;>
    exact hplain.trans (hopen.trans (upper_iff_capped σ J α c b _ a φ horder).symm)

/-- A harmless finite interval for reusing the past-cover definition,
which depends only on the lower endpoint. It does not cap any semantics. -/
def lowerInterval (a : NNReal) : BoundedTimeInterval :=
  ⟨a, (a : ℝ) + 1, a.coe_nonneg, by linarith⟩

def PastSeparated (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hk : k.1 < P.size) (c : Clock) (b : Marker) (a : NNReal) (φ : Formula Var) : Prop :=
  STLTableau.PastSeparated σ P α k hk c b (lowerInterval a) φ

/-- The printed invariant specialized to an infinite timing upper endpoint:
finite clocks are automatically below infinity, and infinite-width bounds
are automatic. The nonemptiness and clauses for no past satisfaction remain unchanged. -/
def Invariant (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hk : k.1 < P.size) : Predicate Clock Var → Prop
  | .upper c b .always a _ | .bounded c _ b _ .always a _ =>
      (α c : ℝ) <[Marker.imp b (P.interval ⟨k.1, hk⟩).leftBoundary] (a : ℝ)
  | .upper c b .eventually a φ =>
      ((0 : ℝ) <[Marker.conj b (P.interval ⟨k.1, hk⟩).rightBoundary]
        ((α c : ℝ) + (P.interval ⟨k.1, hk⟩).right - (P.interval ⟨k.1, hk⟩).left)) ∧
      PastSeparated σ P α k hk c b a φ
  | .bounded c d b q .eventually a φ =>
      ((α d : ℝ) <[Marker.conj b q] (α c : ℝ)) ∧
      PastSeparated σ P α k hk c b a φ

/-- A uniform current operand supplies an unbounded-eventuality witness
as soon as the lower witness endpoint meets the current interval. -/
theorem current_witness (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c : Clock) (b : Marker) (a : NNReal)
    (φ : Formula Var) (hne : J.carrier.Nonempty) (hD : J.carrier ⊆ σ.domain)
    (hφ : ∀ u : σ.Time, u.1 ∈ J → (σ, u) ⊨ φ) (t : ℝ)
    (ht : J.left - (α c : ℝ) <[b] t)
    (hcut : t + (a : ℝ) <[J.rightBoundary] J.right) :
    ∃ u : σ.Time, (a : ℝ) ≤ u.1 - t ∧ (σ, u) ⊨ φ := by
  let I := cappedInterval σ J α c c a
  have hreach : (α c : ℝ) <[Marker.imp b J.leftBoundary] I.upper := by
    left
    have := a.coe_nonneg
    have := (α c).coe_nonneg
    have := abs_nonneg J.left
    have := σ.horizon_pos
    dsimp [I, cappedInterval, cap]
    linarith
  obtain ⟨u, huJ, huI⟩ := IntervalPredicate.exists_current_point_of_marked_bounds
    J α c b I hne hreach t ht hcut
  exact eventually_witness_of_timingDifference σ J.carrier (.unbounded a) φ hD hφ t
    ⟨u, huJ, huI.1⟩

/-- On a stable partition, the condition for no past satisfaction places witnesses for
the unbounded timing bound in the current suffix. -/
theorem witness_in_suffix (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hk : k.1 < P.size) (c : Clock) (b : Marker) (a : NNReal) (φ : Formula Var)
    (hst : ∀ j, σ.Stable (P.interval j) φ)
    (hp : PastSeparated σ P α k hk c b a φ)
    (t : ℝ) (ht : (P.interval ⟨k.1, hk⟩).left - (α c : ℝ) <[b] t)
    (w : σ.Time) (hw : (a : ℝ) ≤ w.1 - t) (hwφ : (σ,w)⊨φ) :
    InCurrentSuffix (P.interval ⟨k.1, hk⟩) w.1 := by
  let J := P.interval ⟨k.1, hk⟩
  let I := cappedInterval σ J α c c a
  have hpI : STLTableau.PastSeparated σ P α k hk c b I φ := hp
  have hwI : w.1 ∈ (I : TimeInterval).translate t := by
    refine ⟨hw, ?_⟩
    have hl : J.left - (α c : ℝ) ≤ t := ht.elim le_of_lt (fun h => h.1.le)
    have := w.2.2
    have := a.coe_nonneg
    have := (α c).coe_nonneg
    have := neg_le_abs J.left
    change w.1 - t ≤ cap σ J α c c a
    dsimp [cap]
    linarith
  exact STLTableau.witness_in_suffix σ P α k hk c b I φ hst hpI t ht w hwI hwφ

/-- The finite-cap bridge also preserves the source invariant, including
the signal-dependent clause for no past satisfaction. -/
theorem upper_invariant_iff_capped (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hk : k.1 < P.size)
    (c : Clock) (b : Marker) (kind : TemporalKind) (a : NNReal) (φ : Formula Var) :
    Invariant σ P α k hk (.upper c b kind a φ) ↔
      STLTableau.Invariant σ P α k hk
        (.upper c b kind (cappedInterval σ (P.interval ⟨k.1, hk⟩) α c c a) φ) := by
  let J := P.interval ⟨k.1, hk⟩
  let I := cappedInterval σ J α c c a
  have htop : (α c : ℝ) <[Marker.imp b J.leftBoundary] I.upper := by
    left
    have := a.coe_nonneg
    have := (α c).coe_nonneg
    have := abs_nonneg J.left
    have := σ.horizon_pos
    dsimp [I, cappedInterval, cap]
    linarith
  cases kind with
  | always => rfl
  | eventually =>
      constructor
      · rintro ⟨hn, hp⟩
        exact ⟨htop, by simpa only [add_sub_assoc] using hn, hp⟩
      · intro h
        exact ⟨by simpa only [add_sub_assoc] using h.2.1, h.2.2⟩

theorem bounded_invariant_iff_capped (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hk : k.1 < P.size)
    (c d : Clock) (b q : Marker) (kind : TemporalKind) (a : NNReal) (φ : Formula Var) :
    Invariant σ P α k hk (.bounded c d b q kind a φ) ↔
      STLTableau.Invariant σ P α k hk
        (.bounded c d b q kind (cappedInterval σ (P.interval ⟨k.1, hk⟩) α c d a) φ) := by
  let J := P.interval ⟨k.1, hk⟩
  let I := cappedInterval σ J α c d a
  have htop : (α c : ℝ) <[Marker.imp b J.leftBoundary] I.upper := by
    left
    have := a.coe_nonneg
    have := (α d).coe_nonneg
    have := abs_nonneg J.left
    have := σ.horizon_pos
    dsimp [I, cappedInterval, cap]
    linarith
  have hwidth : (α d : ℝ) <[Marker.conj b q] ((α c : ℝ) + (I.upper - I.lower)) := by
    left
    have := (α c).coe_nonneg
    have := abs_nonneg J.left
    have := σ.horizon_pos
    dsimp [I, cappedInterval, cap]
    linarith
  cases kind with
  | always =>
      constructor
      · intro h; exact ⟨h, hwidth⟩
      · intro h; exact h.1
  | eventually =>
      constructor
      · rintro ⟨hn, hp⟩; exact ⟨htop, hn, hp⟩
      · intro h; exact ⟨h.2.1, h.2.2⟩

/-- The current true piece discharges an entire `↑↓` `◇` scope
once its rightmost lower-witness endpoint fits in the piece. -/
theorem bounded_finish (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c d : Clock) (b q : Marker)
    (a : NNReal) (φ : Formula Var) (hne : J.carrier.Nonempty)
    (hD : J.carrier ⊆ σ.domain)
    (hφ : ∀ u : σ.Time, u.1 ∈ J → (σ,u)⊨φ)
    (hg : (a : ℝ) <[Marker.imp q J.rightBoundary]
      ((α d : ℝ) + (J.right - J.left))) :
    satisfies σ J α (.bounded c d b q .eventually a φ) := by
  intro t ht
  exact current_witness σ J α c b a φ hne hD hφ t ht.1
    (IntervalPredicate.eventually_finish_cut J α d q a ht.2 hg)

end STLTableau.UnboundedClocked
