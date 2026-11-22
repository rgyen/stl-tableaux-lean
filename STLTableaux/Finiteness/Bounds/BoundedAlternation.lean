import STLTableaux.Syntax.Section3Judgements
import Mathlib.Algebra.Order.Floor.Semiring

/-! Quantitative alternation for closed temporal windows.
The witness predicate may be any subset of the real line; no regularity of
its truth set is assumed. The bound counts separated true regions of the
window formula, not changes of the underlying witness predicate. -/
namespace STLTableau.Section4.Finiteness.Alternation

/-- The origin may be any real number. A finite signal's domain restriction
can be encoded in W, exactly as in the eventuality semantics. -/
def EventuallyAt (W : ℝ → Prop) (a b t : ℝ) : Prop :=
  ∃ w, W w ∧ t + a ≤ w ∧ w ≤ t + b

/-- A false origin between two true origins separates their witnesses by
strictly more than the temporal window width. -/
theorem witness_gap (W : ℝ → Prop) (a b x y z w v : ℝ)
    (hxz : x < z) (hzy : z < y)
    (hw : W w) (hwhi : w ≤ x + b)
    (hv : W v) (hvlo : y + a ≤ v)
    (hz : ¬ EventuallyAt W a b z) : b - a < v - w := by
  have hwl : w < z + a := by
    by_contra hn
    have hle : z + a ≤ w := le_of_not_gt hn
    exact hz ⟨w, hw, hle, by linarith⟩
  have hvr : z + b < v := by
    by_contra hn
    have hle : v ≤ z + b := le_of_not_gt hn
    exact hz ⟨v, hv, by linarith, hle⟩
  linarith

/-- A finite sequence of uniformly spaced witnesses spans at least n widths. -/
theorem span_of_gaps (w : ℕ → ℝ) (d : ℝ) (n : ℕ)
    (hg : ∀ i < n, d ≤ w (i + 1) - w i) :
    (n : ℝ) * d ≤ w n - w 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := hg n (Nat.lt_succ_self n)
    have hprev := ih (fun i hi => hg i (Nat.lt_succ_of_lt hi))
    push_cast
    nlinarith

/-- If n+1 true samples in [u,v] have false separators between successive
samples, then their number is at most ceil((v-u)/(b-a))+2.
The additive boundary allowance avoids assuming whole witness windows lie
inside [u,v]. -/
theorem separated_true_samples_bound (W : ℝ → Prop) (a b u v : ℝ)
    (hab : a < b) (n : ℕ) (t z : ℕ → ℝ)
    (ht : ∀ i ≤ n, u ≤ t i ∧ t i ≤ v)
    (htrue : ∀ i ≤ n, EventuallyAt W a b (t i))
    (hbetween : ∀ i < n, t i < z i ∧ z i < t (i + 1))
    (hfalse : ∀ i < n, ¬ EventuallyAt W a b (z i)) :
    n + 1 ≤ ⌈(v - u) / (b - a)⌉₊ + 2 := by
  classical
  have hw : ∀ i, ∃ w, i ≤ n → W w ∧ t i + a ≤ w ∧ w ≤ t i + b := by
    intro i
    by_cases hi : i ≤ n
    · obtain ⟨w, hw⟩ := htrue i hi
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  choose w hw using hw
  have hg : ∀ i < n, b - a ≤ w (i + 1) - w i := by
    intro i hi
    have hwi := hw i (Nat.le_of_lt hi)
    have hws := hw (i + 1) (by omega)
    exact le_of_lt (witness_gap W a b (t i) (t (i + 1)) (z i) (w i) (w (i + 1))
      (hbetween i hi).1 (hbetween i hi).2 hwi.1 hwi.2.2
      hws.1 hws.2.1 (hfalse i hi))
  have hspan := span_of_gaps w (b - a) n hg
  have hw0 := hw 0 (Nat.zero_le n)
  have hwn := hw n (le_refl n)
  have ht0 := ht 0 (Nat.zero_le n)
  have htn := ht n (le_refl n)
  have hwidth : 0 < b - a := sub_pos.mpr hab
  have hdiv : (n : ℝ) ≤ (v - u) / (b - a) + 1 := by
    have hb : (n : ℝ) ≤ (v - u + (b - a)) / (b - a) := by
      apply (le_div_iff₀ hwidth).mpr
      nlinarith
    simpa only [add_div, div_self (ne_of_gt hwidth)] using hb
  have hceil : (v - u) / (b - a) ≤ (⌈(v - u) / (b - a)⌉₊ : ℝ) := Nat.le_ceil _
  have hn : n ≤ ⌈(v - u) / (b - a)⌉₊ + 1 := by
    have hcast : (n : ℝ) ≤ (⌈(v - u) / (b - a)⌉₊ : ℝ) + 1 := by linarith
    exact_mod_cast hcast
  omega

/-- Unbounded eventuality is monotone backwards in its origin. -/
def EventuallyUnboundedAt (W : ℝ → Prop) (a t : ℝ) : Prop :=
  ∃ w, W w ∧ t + a ≤ w

theorem unbounded_backward (W : ℝ → Prop) (a x y : ℝ)
    (hxy : x ≤ y) (hy : EventuallyUnboundedAt W a y) :
    EventuallyUnboundedAt W a x := by
  obtain ⟨w, hw, hle⟩ := hy
  exact ⟨w, hw, by linarith⟩

/-- A false origin cannot be followed by a true origin for unbounded F. -/
theorem unbounded_no_false_then_true (W : ℝ → Prop) (a x y : ℝ)
    (hxy : x ≤ y) (hx : ¬ EventuallyUnboundedAt W a x) :
    ¬ EventuallyUnboundedAt W a y := fun hy => hx (unbounded_backward W a x y hxy hy)

variable {Var : Type*}

/-- The finite signal's domain is part of witness truth, not a restriction
silently imposed on origin times. -/
def signalWitness (σ : FiniteSignal Var) (φ : Formula Var) (w : ℝ) : Prop :=
  ∃ t : σ.Time, t.1 = w ∧ σ.Satisfies φ t

/-- Exact bridge to the witness semantics used by interval predicates. -/
theorem eventuallyAt_iff_signal_witness (σ : FiniteSignal Var)
    (I : BoundedTimeInterval) (φ : Formula Var) (t : ℝ) :
    EventuallyAt (signalWitness σ φ) I.lower I.upper t ↔
      ∃ w : σ.Time, w.1 ∈ (TimeInterval.bounded I).translate t ∧ σ.Satisfies φ w := by
  constructor
  · rintro ⟨w, ⟨s, rfl, hs⟩, hlo, hhi⟩
    refine ⟨s, ?_, hs⟩
    change I.lower ≤ s.1 - t ∧ s.1 - t ≤ I.upper
    constructor <;> linarith
  · rintro ⟨w, htime, hw⟩
    have hb : I.lower ≤ w.1 - t ∧ w.1 - t ≤ I.upper := htime
    exact ⟨w.1, ⟨w, rfl, hw⟩, by linarith, by linarith⟩

theorem eventuallyAt_iff_satisfaction (σ : FiniteSignal Var)
    (I : BoundedTimeInterval) (φ : Formula Var) (t : σ.Time) :
    EventuallyAt (signalWitness σ φ) I.lower I.upper t.1 ↔
      σ.Satisfies (Formula.eventually (.bounded I) φ) t :=
  (eventuallyAt_iff_signal_witness σ I φ t.1).trans
    (σ.satisfies_eventually_iff (.bounded I) φ t).symm

/-- Negated witnesses give the finite-signal dual, including horizon effects. -/
theorem always_iff_no_neg_witness (σ : FiniteSignal Var)
    (I : BoundedTimeInterval) (φ : Formula Var) (t : σ.Time) :
    σ.Satisfies (Formula.always (.bounded I) φ) t ↔
      ¬ EventuallyAt (signalWitness σ (.neg φ)) I.lower I.upper t.1 := by
  change (¬ σ.Satisfies (Formula.eventually (.bounded I) (.neg φ)) t) ↔ _
  exact not_congr (eventuallyAt_iff_satisfaction σ I (.neg φ) t).symm

/-- Bounded F has at most ceil(length/width)+2 separated true samples.
For an observation interval of length I.upper this is the O(r(I)). -/
theorem eventually_separated_samples_bound (σ : FiniteSignal Var)
    (I : BoundedTimeInterval) (φ : Formula Var) (u v : ℝ)
    (n : ℕ) (t z : ℕ → σ.Time)
    (ht : ∀ i ≤ n, u ≤ (t i).1 ∧ (t i).1 ≤ v)
    (htrue : ∀ i ≤ n, σ.Satisfies (Formula.eventually (.bounded I) φ) (t i))
    (hbetween : ∀ i < n, (t i).1 < (z i).1 ∧ (z i).1 < (t (i + 1)).1)
    (hfalse : ∀ i < n, ¬ σ.Satisfies (Formula.eventually (.bounded I) φ) (z i)) :
    n + 1 ≤ ⌈(v - u) / (I.upper - I.lower)⌉₊ + 2 := by
  apply separated_true_samples_bound (signalWitness σ φ) I.lower I.upper u v
    I.nonSingular n (fun i => (t i).1) (fun i => (z i).1) ht
  · intro i hi
    exact (eventuallyAt_iff_satisfaction σ I φ (t i)).mpr (htrue i hi)
  · exact hbetween
  · intro i hi h
    exact hfalse i hi ((eventuallyAt_iff_satisfaction σ I φ (z i)).mp h)

/-- Bounded G has the same bound on separated false samples, by duality. -/
theorem always_separated_false_samples_bound (σ : FiniteSignal Var)
    (I : BoundedTimeInterval) (φ : Formula Var) (u v : ℝ)
    (n : ℕ) (t z : ℕ → σ.Time)
    (ht : ∀ i ≤ n, u ≤ (t i).1 ∧ (t i).1 ≤ v)
    (hfalse : ∀ i ≤ n, ¬ σ.Satisfies (Formula.always (.bounded I) φ) (t i))
    (hbetween : ∀ i < n, (t i).1 < (z i).1 ∧ (z i).1 < (t (i + 1)).1)
    (htrue : ∀ i < n, σ.Satisfies (Formula.always (.bounded I) φ) (z i)) :
    n + 1 ≤ ⌈(v - u) / (I.upper - I.lower)⌉₊ + 2 := by
  classical
  apply eventually_separated_samples_bound σ I (.neg φ) u v n t z ht
  · intro i hi
    by_contra hn
    exact hfalse i hi hn
  · exact hbetween
  · intro i hi
    exact htrue i hi

/-- A false origin between two true G origins forces the true origins
apart by more than the timing-window width. The same finite-domain negative
witness is used at all three origins, so horizon vacuity causes no exception. -/
theorem always_true_gap (σ : FiniteSignal Var)
    (I : BoundedTimeInterval) (φ : Formula Var) (x z y : σ.Time)
    (hxz : x.1 < z.1) (hzy : z.1 < y.1)
    (hx : σ.Satisfies (Formula.always (.bounded I) φ) x)
    (hz : ¬ σ.Satisfies (Formula.always (.bounded I) φ) z)
    (hy : σ.Satisfies (Formula.always (.bounded I) φ) y) :
    I.upper - I.lower < y.1 - x.1 := by
  have hw : EventuallyAt (signalWitness σ (.neg φ)) I.lower I.upper z.1 := by
    by_contra hn
    exact hz ((always_iff_no_neg_witness σ I φ z).mpr hn)
  obtain ⟨w, hw, hwlo, hwhi⟩ := hw
  have hnx := (always_iff_no_neg_witness σ I φ x).mp hx
  have hny := (always_iff_no_neg_witness σ I φ y).mp hy
  have hxw : x.1 + I.upper < w := by
    by_contra hn
    exact hnx ⟨w, hw, by linarith, le_of_not_gt hn⟩
  have hwy : w < y.1 + I.lower := by
    by_contra hn
    exact hny ⟨w, hw, le_of_not_gt hn, by linarith⟩
  linarith

/-- Each representative true origin lies in the observation window and
successive representatives have a false separator. This bounds true blocks,
not arbitrary labels or the number of changes of the operand formula. -/
theorem always_separated_true_samples_bound (σ : FiniteSignal Var)
    (I : BoundedTimeInterval) (φ : Formula Var) (u v : ℝ)
    (n : ℕ) (t z : ℕ → σ.Time)
    (ht : ∀ i ≤ n, u ≤ (t i).1 ∧ (t i).1 ≤ v)
    (htrue : ∀ i ≤ n, σ.Satisfies (Formula.always (.bounded I) φ) (t i))
    (hbetween : ∀ i < n, (t i).1 < (z i).1 ∧ (z i).1 < (t (i + 1)).1)
    (hfalse : ∀ i < n, ¬ σ.Satisfies (Formula.always (.bounded I) φ) (z i)) :
    n + 1 ≤ ⌈(v - u) / (I.upper - I.lower)⌉₊ + 1 := by
  have hg : ∀ i < n, I.upper - I.lower ≤ (t (i + 1)).1 - (t i).1 := by
    intro i hi
    exact (always_true_gap σ I φ (t i) (z i) (t (i + 1))
      (hbetween i hi).1 (hbetween i hi).2 (htrue i (by omega))
      (hfalse i hi) (htrue (i + 1) (by omega))).le
  have hspan := span_of_gaps (fun i => (t i).1) (I.upper - I.lower) n hg
  have hwidth : 0 < I.upper - I.lower := sub_pos.mpr I.nonSingular
  have hn : (n : ℝ) ≤ (v - u) / (I.upper - I.lower) := by
    apply (le_div_iff₀ hwidth).mpr
    linarith [(ht 0 (Nat.zero_le n)).1, (ht n (le_refl n)).2]
  have hceil := Nat.le_ceil ((v - u) / (I.upper - I.lower))
  have hnat : n ≤ ⌈(v - u) / (I.upper - I.lower)⌉₊ := by
    exact_mod_cast (le_trans hn hceil)
  omega

/-- Actual finite-signal unbounded F is monotone backwards. -/
theorem signal_unbounded_eventually_backward (σ : FiniteSignal Var)
    (a : NNReal) (φ : Formula Var) (x y : σ.Time) (hxy : x.1 ≤ y.1)
    (hy : σ.Satisfies (Formula.eventually (.unbounded a) φ) y) :
    σ.Satisfies (Formula.eventually (.unbounded a) φ) x := by
  obtain ⟨w, hw, hφ⟩ := (σ.satisfies_eventually_iff (.unbounded a) φ y).mp hy
  apply (σ.satisfies_eventually_iff (.unbounded a) φ x).mpr
  refine ⟨w, ?_, hφ⟩
  change (a : ℝ) ≤ w.1 - x.1
  have hwy : (a : ℝ) ≤ w.1 - y.1 := hw
  linarith

/-- Actual finite-signal unbounded G is monotone forwards, including vacuity
near the horizon. Together these monotonicities give at most one change. -/
theorem signal_unbounded_always_forward (σ : FiniteSignal Var)
    (a : NNReal) (φ : Formula Var) (x y : σ.Time) (hxy : x.1 ≤ y.1)
    (hx : σ.Satisfies (Formula.always (.unbounded a) φ) x) :
    σ.Satisfies (Formula.always (.unbounded a) φ) y := by
  change ¬ σ.Satisfies (Formula.eventually (.unbounded a) (.neg φ)) y
  intro hy
  exact hx (signal_unbounded_eventually_backward σ a (.neg φ) x y hxy hy)

end STLTableau.Section4.Finiteness.Alternation
