import STLTableaux.Finiteness.Derivation.Merging.AlwaysCheckingMerge
import STLTableaux.Finiteness.Bounds.OrderedIntervalPacking

/-! Geometric premises of the bounded-G packing argument, derived from the
actual invariant and reachable age shape. No horizon truncation is performed.
This file does not assert existence of a normalized whole tableau path. -/
namespace STLTableau.Section4.Finiteness.DirectTracking

open scoped STL
variable {Clock Var : Type*}

/-- The actual invariant, not a new semantic assumption, gives nonempty
untruncated checking regions contained numerically in the pending window. -/
theorem invariant_geometry (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (hk : k.1 < P.size)
    (c d : Clock) (l r : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hinv : STLTableau.Invariant σ P α k hk (.bounded c d l r .always I φ)) :
    let J := P.interval ⟨k.1, hk⟩
    let K := checking J α c d l r I
    J.left ≤ K.left ∧ K.right ≤ J.left + I.upper ∧ K.carrier.Nonempty := by
  dsimp only
  have hleft : (α c : ℝ) ≤ I.lower :=
    hinv.1.elim le_of_lt (fun h => h.1.le)
  refine ⟨?_, ?_, ?_⟩
  · dsimp [checking]
    linarith
  · dsimp [checking]
    have hnonneg := (α d).coe_nonneg
    linarith
  · apply (MarkedInterval.nonempty_iff _).2
    rcases hinv.2 with h | ⟨h, hm⟩
    · exact Or.inl (by dsimp [checking]; linarith)
    · exact Or.inr ⟨by dsimp [checking]; linarith, hm⟩

/-- Ordinary G regions have at least the timing width, before any finite
horizon restriction. -/
theorem ordinary_checking_width (J : MarkedInterval) (α : ClockValuation Clock)
    (c d : Clock) (l r : Marker) (I : BoundedTimeInterval)
    (hordinary : α d ≤ α c) :
    I.upper - I.lower ≤
      (checking J α c d l r I).right - (checking J α c d l r I).left := by
  have h : (α d : ℝ) ≤ (α c : ℝ) := by exact_mod_cast hordinary
  dsimp [checking]
  linarith

/-- The reachable shape yields a long region or the shared checked start.
The invariant alone would not yield this disjunction. -/
theorem shape_checking_geometry (J : MarkedInterval) (α : ClockValuation Clock)
    (c d : Clock) (l r : Marker) (I : BoundedTimeInterval)
    (hshape : AlwaysAgeShape.Holds J α c d l ⟨I.lower, I.lower_nonnegative⟩) :
    I.upper - I.lower ≤
        (checking J α c d l r I).right - (checking J α c d l r I).left ∨
      ((checking J α c d l r I).left = J.left ∧
        (checking J α c d l r I).leftBoundary = J.leftBoundary) := by
  rcases hshape with ho | ⟨hc, hl⟩
  · exact Or.inl (ordinary_checking_width J α c d l r I ho)
  · right
    refine ⟨?_, hl⟩
    have hc' := congrArg (fun x : NNReal => (x : ℝ)) hc
    change (α c : ℝ) = I.lower at hc'
    dsimp [checking]
    linarith

/-- A common left endpoint AND marker make nonempty marked intervals
intersect. Choosing the earlier of two contained points handles singletons. -/
theorem common_left_intersects (K M : MarkedInterval)
    (hleft : K.left = M.left) (hmarker : K.leftBoundary = M.leftBoundary)
    (hK : K.carrier.Nonempty) (hM : M.carrier.Nonempty) :
    (K.carrier ∩ M.carrier).Nonempty := by
  obtain ⟨x, hx⟩ := hK
  obtain ⟨y, hy⟩ := hM
  by_cases hxy : x ≤ y
  · refine ⟨x, hx, ?_, ?_⟩
    · simpa only [← hleft, ← hmarker] using hx.1
    · rcases hxy.lt_or_eq with hlt | heq
      · exact Or.inl (hlt.trans_le (MarkedInterval.le_right_of_mem hy))
      · exact heq ▸ hy.2
  · have hyx : y ≤ x := (lt_of_not_ge hxy).le
    refine ⟨y, ⟨?_, ?_⟩, hy⟩
    · simpa only [hleft, hmarker] using hy.1
    · rcases hyx.lt_or_eq with hlt | heq
      · exact Or.inl (hlt.trans_le (MarkedInterval.le_right_of_mem hx))
      · exact heq ▸ hx.2

/-- All nonempty checked G regions at this boundary meet, including the
closed singleton case. -/
theorem checked_checking_intersects (J : MarkedInterval) (α : ClockValuation Clock)
    (c₁ d₁ c₂ d₂ : Clock) (r₁ r₂ : Marker) (I : BoundedTimeInterval)
    (hc₁ : (α c₁ : ℝ) = I.lower) (hc₂ : (α c₂ : ℝ) = I.lower)
    (h₁ : (checking J α c₁ d₁ J.leftBoundary r₁ I).carrier.Nonempty)
    (h₂ : (checking J α c₂ d₂ J.leftBoundary r₂ I).carrier.Nonempty) :
    ((checking J α c₁ d₁ J.leftBoundary r₁ I).carrier ∩
      (checking J α c₂ d₂ J.leftBoundary r₂ I).carrier).Nonempty := by
  refine common_left_intersects (checking J α c₁ d₁ J.leftBoundary r₁ I)
    (checking J α c₂ d₂ J.leftBoundary r₂ I) ?_ rfl h₁ h₂
  dsimp [checking]
  rw [hc₁, hc₂]

/-- Direct specialization to actual separated ordinary G obligations.
Separation is an explicit normalization premise, not an invariant theorem. -/
theorem separated_ordinary_count (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (hk : k.1 < P.size)
    (n : ℕ) (c d : ℕ → Clock) (l r : ℕ → Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hinv : ∀ i, i < n → STLTableau.Invariant σ P α k hk
      (.bounded (c i) (d i) (l i) (r i) .always I φ))
    (hordinary : ∀ i, i < n → α (d i) ≤ α (c i))
    (hordered : ∀ i, i + 1 < n →
      (checking (P.interval ⟨k.1, hk⟩) α (c i) (d i) (l i) (r i) I).right ≤
      (checking (P.interval ⟨k.1, hk⟩) α (c (i + 1)) (d (i + 1)) (l (i + 1)) (r (i + 1)) I).left) :
    n ≤ ⌊I.upper / (I.upper - I.lower)⌋₊ := by
  apply OrderedIntervalPacking.le_floor_div_width n
    (fun i => (checking (P.interval ⟨k.1, hk⟩) α (c i) (d i) (l i) (r i) I).left)
    (fun i => (checking (P.interval ⟨k.1, hk⟩) α (c i) (d i) (l i) (r i) I).right)
    (P.interval ⟨k.1, hk⟩).left I.upper (I.upper - I.lower)
    (le_trans I.lower_nonnegative I.nonSingular.le) (sub_pos.mpr I.nonSingular)
  · intro i hi
    exact (invariant_geometry σ P α k hk _ _ _ _ I φ (hinv i hi)).1
  · intro i hi
    exact (invariant_geometry σ P α k hk _ _ _ _ I φ (hinv i hi)).2.1
  · intro i hi
    exact ordinary_checking_width _ α _ _ _ _ I (hordinary i hi)
  · exact hordered

#print axioms invariant_geometry
#print axioms ordinary_checking_width
#print axioms shape_checking_geometry
#print axioms common_left_intersects
#print axioms checked_checking_intersects
#print axioms separated_ordinary_count

end STLTableau.Section4.Finiteness.DirectTracking
