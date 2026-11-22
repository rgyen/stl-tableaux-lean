import STLTableaux.Finiteness.Derivation.BoundaryExtension
import STLTableaux.Rules.Unbounded.UnboundedClockedRules

/-! Boundary side conditions derived from adjacent partition pieces and actual
upper-rule successor reset/marker syntax. No bounded-path claim is made. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*}

/-- An elapsed inherited clock meets the boundary's unary comparison.
The only strict marker case forces positive duration of the preceding piece:
a nonempty piece with an excluded right endpoint cannot be a singleton. -/
theorem boundary_comparison_after_elapse (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (i : Fin P.size) (hn : i.1 + 1 < P.size) (c : Clock) (b : Marker) :
    (0 : ℝ) <[Marker.imp (P.interval ⟨i.1+1,hn⟩).leftBoundary b]
      (ClockResetSet.elapse α (STLTableau.Judgement.duration P i) c : ℝ) := by
  have hα := (α c).coe_nonneg
  have hδ := (STLTableau.Judgement.duration P i).coe_nonneg
  have hadj := P.adjacent_rightBoundary_eq_complement_leftBoundary i hn
  have hpositive : (P.interval ⟨i.1+1,hn⟩).leftBoundary = ● →
      0 < (STLTableau.Judgement.duration P i : ℝ) := by
    intro hclosed
    obtain ⟨t, ht⟩ := P.nonempty i
    have hleft := MarkedInterval.left_le_of_mem ht
    have hright := ht.2
    rw [hadj, hclosed] at hright
    have hstrict : t < (P.interval i).right := by
      simpa [Marker.complement, MarkedLT, Marker.Includes] using hright
    change 0 < (P.interval i).right - (P.interval i).left
    linarith
  generalize hℓ : (P.interval ⟨i.1+1,hn⟩).leftBoundary = ℓ
  cases ℓ <;> cases b <;>
    simp only [Marker.imp, markedLT_closed, markedLT_open, ClockResetSet.elapse,
      NNReal.coe_add]
  all_goals first | positivity | (have hp := hpositive hℓ; linarith)

/-- The literal defer reset sets its right endpoint to zero and leaves the
old left clock unchanged; the boundary comparison is derived, not supplied. -/
theorem defer_successor_numeric [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (i : Fin P.size) (hn : i.1 + 1 < P.size) (c d : Clock) (b : Marker)
    (hcd : c ≠ d) :
    let β := (ClockResetSet.singleton d 0).apply
      (ClockResetSet.elapse α (STLTableau.Judgement.duration P i))
    (β d : ℝ) = 0 ∧
      (0 : ℝ) <[Marker.imp (P.interval ⟨i.1+1,hn⟩).leftBoundary b] (β c : ℝ) := by
  dsimp only
  constructor
  · simp
  · rw [ClockResetSet.apply_singleton_of_ne 0 _ hcd]
    exact boundary_comparison_after_elapse σ P α i hn c b

/-- A check branch resets c to the lower endpoint and d to zero. Its retained
left marker is the successor marker itself, so no strict comparison remains. -/
theorem check_successor_numeric [DecidableEq Clock] (α : ClockValuation Clock)
    (c d : Clock) (a : NNReal) (m : Marker) (hcd : c ≠ d) :
    let β := ((ClockResetSet.singleton c a).union (ClockResetSet.singleton d 0)).apply α
    (β d : ℝ) = 0 ∧ (0 : ℝ) <[Marker.imp m m] (β c : ℝ) := by
  dsimp only
  have hdc : d ≠ c := Ne.symm hcd
  have hd : ((ClockResetSet.singleton c a).union (ClockResetSet.singleton d 0)).apply α d = 0 := by
    simp only [ClockResetSet.apply, ClockResetSet.union, ClockResetSet.singleton, hdc,
      if_false, if_true]
  have hc : ((ClockResetSet.singleton c a).union (ClockResetSet.singleton d 0)).apply α c = a := by
    simp only [ClockResetSet.apply, ClockResetSet.union, ClockResetSet.singleton, if_true]
  rw [hd, hc]
  cases m <;> simp [Marker.imp]

/-- The defer branches of the `↑` form share a next judgement. Its reset and
marker give the zero right clock, left marker, and clock comparison. -/
theorem defer_next_body_conditions [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (i : Fin P.size) (hn : i.1 + 1 < P.size) (c d : Clock) (b m : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) (hcd : c ≠ d)
    (h : Section3.Judgement.holds σ P α ⟨i.1,by omega⟩
      (.next (.reset (ClockResetSet.singleton d 0)
        (.conj (.predicate (.bounded c d b (¬ₘ m) kind I φ)) (.marker m))))) :
    let β := (ClockResetSet.singleton d 0).apply
      (ClockResetSet.elapse α (STLTableau.Judgement.duration P i))
    m = (P.interval ⟨i.1+1,hn⟩).leftBoundary ∧ (β d : ℝ) = 0 ∧
      (0 : ℝ) <[Marker.imp m b] (β c : ℝ) := by
  have hi : i.1 < P.size := i.isLt
  simp only [Section3.Judgement.holds, dif_pos hi, dif_pos hn] at h
  dsimp only
  refine ⟨h.2.symm, ?_⟩
  rw [← h.2]
  exact defer_successor_numeric σ P α i hn c d b hcd

/-- Defer branch conditions for the `↑` form of `□` with bounded timing. -/
theorem finite_upperAlways_defer_conditions [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (i : Fin P.size) (hn : i.1 + 1 < P.size) (c d : Clock) (b m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) (hcd : c ≠ d)
    (h : STLTableau.satisfies σ P α ⟨i.1,by omega⟩ (STLTableau.ExpansionRule.upperAlways_defer c d b m I φ)) :
    let β := (ClockResetSet.singleton d 0).apply
      (ClockResetSet.elapse α (STLTableau.Judgement.duration P i))
    m = (P.interval ⟨i.1+1,hn⟩).leftBoundary ∧ (β d : ℝ) = 0 ∧
      (0 : ℝ) <[Marker.imp m b] (β c : ℝ) := by
  apply defer_next_body_conditions σ P α i hn c d b m .always (.bounded I) φ hcd
  have hi := i.isLt
  simp only [Section3.Judgement.holds, dif_pos hi, dif_pos hn]
  simp only [STLTableau.ExpansionRule.upperAlways_defer, STLTableau.satisfies, dif_pos hi, dif_pos hn] at h
  exact h.2

/-- Defer branch conditions for the `↑` form of `□` with unbounded timing. -/
theorem unbounded_upperAlways_defer_conditions [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (i : Fin P.size) (hn : i.1 + 1 < P.size) (c d : Clock) (b m : Marker)
    (a : NNReal) (φ : Formula Var) (hcd : c ≠ d)
    (h : UnboundedClocked.Node.holds σ P α ⟨i.1,by omega⟩ (UnboundedClocked.upperAlwaysDefer c d b m a φ)) :
    let β := (ClockResetSet.singleton d 0).apply
      (ClockResetSet.elapse α (STLTableau.Judgement.duration P i))
    m = (P.interval ⟨i.1+1,hn⟩).leftBoundary ∧ (β d : ℝ) = 0 ∧
      (0 : ℝ) <[Marker.imp m b] (β c : ℝ) := by
  apply defer_next_body_conditions σ P α i hn c d b m .always (.unbounded a) φ hcd
  have hi := i.isLt
  simp only [Section3.Judgement.holds, dif_pos hi, dif_pos hn]
  simp only [UnboundedClocked.upperAlwaysDefer, UnboundedClocked.Node.holds, dif_pos hi, dif_pos hn] at h
  exact h.2

/-- Defer branch conditions for the `↑` form of `◇` with bounded timing. -/
theorem finite_upperEventually_defer_conditions [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (i : Fin P.size) (hn : i.1 + 1 < P.size) (c d : Clock) (b m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) (hcd : c ≠ d)
    (h : STLTableau.satisfies σ P α ⟨i.1,by omega⟩ (STLTableau.ExpansionRule.upperEventually_defer c d b m I φ)) :
    let β := (ClockResetSet.singleton d 0).apply
      (ClockResetSet.elapse α (STLTableau.Judgement.duration P i))
    m = (P.interval ⟨i.1+1,hn⟩).leftBoundary ∧ (β d : ℝ) = 0 ∧
      (0 : ℝ) <[Marker.imp m b] (β c : ℝ) := by
  apply defer_next_body_conditions σ P α i hn c d b m .eventually (.bounded I) φ hcd
  have hi := i.isLt
  simp only [Section3.Judgement.holds, dif_pos hi, dif_pos hn]
  simp only [STLTableau.ExpansionRule.upperEventually_defer, STLTableau.satisfies, dif_pos hi, dif_pos hn] at h
  exact h.2

/-- Defer branch conditions for the `↑` form of `◇` with unbounded timing. -/
theorem unbounded_upperEventually_defer_conditions [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (i : Fin P.size) (hn : i.1 + 1 < P.size) (c d : Clock) (b m : Marker)
    (a : NNReal) (φ : Formula Var) (hcd : c ≠ d)
    (h : UnboundedClocked.Node.holds σ P α ⟨i.1,by omega⟩ (UnboundedClocked.upperEventuallyDefer c d b m a φ)) :
    let β := (ClockResetSet.singleton d 0).apply
      (ClockResetSet.elapse α (STLTableau.Judgement.duration P i))
    m = (P.interval ⟨i.1+1,hn⟩).leftBoundary ∧ (β d : ℝ) = 0 ∧
      (0 : ℝ) <[Marker.imp m b] (β c : ℝ) := by
  apply defer_next_body_conditions σ P α i hn c d b m .eventually (.unbounded a) φ hcd
  have hi := i.isLt
  simp only [Section3.Judgement.holds, dif_pos hi, dif_pos hn]
  simp only [UnboundedClocked.upperEventuallyDefer, UnboundedClocked.Node.holds, dif_pos hi, dif_pos hn] at h
  exact h

/-- The check branch of the `↑` form of `□` with bounded timing gives
the next left marker. The two resets give the numeric conditions. -/
theorem finite_upperAlways_check_conditions [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (i : Fin P.size) (hn : i.1 + 1 < P.size) (c d : Clock) (b m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) (hcd : c ≠ d)
    (h : STLTableau.satisfies σ P α ⟨i.1,by omega⟩ (STLTableau.ExpansionRule.upperAlways_check c d b m I φ)) :
    let β := ((ClockResetSet.singleton c (⟨I.lower,I.lower_nonnegative⟩ : NNReal)).union
      (ClockResetSet.singleton d 0)).apply
        (ClockResetSet.elapse α (STLTableau.Judgement.duration P i))
    m = (P.interval ⟨i.1+1,hn⟩).leftBoundary ∧ (β d : ℝ) = 0 ∧
      (0 : ℝ) <[Marker.imp m m] (β c : ℝ) := by
  have hi := i.isLt
  simp only [STLTableau.ExpansionRule.upperAlways_check, STLTableau.satisfies, dif_pos hi, dif_pos hn] at h
  exact ⟨h.2.2.2.symm, check_successor_numeric _ c d (⟨I.lower,I.lower_nonnegative⟩ : NNReal) m hcd⟩

/-- The check branch of the `↑` form of `□` with unbounded timing gives
the next left marker. The two resets give the numeric conditions. -/
theorem unbounded_upperAlways_check_conditions [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (i : Fin P.size) (hn : i.1 + 1 < P.size) (c d : Clock) (b m : Marker)
    (a : NNReal) (φ : Formula Var) (hcd : c ≠ d)
    (h : UnboundedClocked.Node.holds σ P α ⟨i.1,by omega⟩ (UnboundedClocked.upperAlwaysCheck c d b m a φ)) :
    let β := ((ClockResetSet.singleton c a).union
      (ClockResetSet.singleton d 0)).apply
        (ClockResetSet.elapse α (STLTableau.Judgement.duration P i))
    m = (P.interval ⟨i.1+1,hn⟩).leftBoundary ∧ (β d : ℝ) = 0 ∧
      (0 : ℝ) <[Marker.imp m m] (β c : ℝ) := by
  have hi := i.isLt
  simp only [UnboundedClocked.upperAlwaysCheck, UnboundedClocked.Node.holds, dif_pos hi, dif_pos hn] at h
  exact ⟨h.2.2.2.symm, check_successor_numeric _ c d a m hcd⟩

/-- The check branch of the `↑` form of `◇` with bounded timing gives
the next left marker. The two resets give the numeric conditions. -/
theorem finite_upperEventually_check_conditions [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (i : Fin P.size) (hn : i.1 + 1 < P.size) (c d : Clock) (b m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) (hcd : c ≠ d)
    (h : STLTableau.satisfies σ P α ⟨i.1,by omega⟩ (STLTableau.ExpansionRule.upperEventually_check c d b m I φ)) :
    let β := ((ClockResetSet.singleton c (⟨I.lower,I.lower_nonnegative⟩ : NNReal)).union
      (ClockResetSet.singleton d 0)).apply
        (ClockResetSet.elapse α (STLTableau.Judgement.duration P i))
    m = (P.interval ⟨i.1+1,hn⟩).leftBoundary ∧ (β d : ℝ) = 0 ∧
      (0 : ℝ) <[Marker.imp m m] (β c : ℝ) := by
  have hi := i.isLt
  simp only [STLTableau.ExpansionRule.upperEventually_check, STLTableau.satisfies, dif_pos hi, dif_pos hn] at h
  exact ⟨h.2.2.2.symm, check_successor_numeric _ c d (⟨I.lower,I.lower_nonnegative⟩ : NNReal) m hcd⟩

/-- The check branch of the `↑` form of `◇` with unbounded timing gives
the next left marker. The two resets give the numeric conditions. -/
theorem unbounded_upperEventually_check_conditions [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (i : Fin P.size) (hn : i.1 + 1 < P.size) (c d : Clock) (b m : Marker)
    (a : NNReal) (φ : Formula Var) (hcd : c ≠ d)
    (h : UnboundedClocked.Node.holds σ P α ⟨i.1,by omega⟩ (UnboundedClocked.upperEventuallyCheck c d b m a φ)) :
    let β := ((ClockResetSet.singleton c a).union
      (ClockResetSet.singleton d 0)).apply
        (ClockResetSet.elapse α (STLTableau.Judgement.duration P i))
    m = (P.interval ⟨i.1+1,hn⟩).leftBoundary ∧ (β d : ℝ) = 0 ∧
      (0 : ℝ) <[Marker.imp m m] (β c : ℝ) := by
  have hi := i.isLt
  simp only [UnboundedClocked.upperEventuallyCheck, UnboundedClocked.Node.holds, dif_pos hi, dif_pos hn] at h
  exact ⟨h.2.2.2.symm, check_successor_numeric _ c d a m hcd⟩

/-- Apply the mixed boundary lemma at a literal defer successor without
supplying either numeric comparison: adjacency and the actual zero reset
establish them. The successor's type test supplies precisely this left marker
in each of the four concrete defer-schema lemmas above. -/
theorem defer_successor_boundary_merge [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (i : Fin P.size) (hn : i.1 + 1 < P.size) (c d : Clock) (b : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) (hcd : c ≠ d) :
    let ℓ := (P.interval ⟨i.1+1,hn⟩).leftBoundary
    let β := (ClockResetSet.singleton d 0).apply
      (ClockResetSet.elapse α (STLTableau.Judgement.duration P i))
    Section3.Judgement.holds σ P β ⟨i.1+1,by omega⟩
      (.conj (.predicate (.bounded c d b (¬ₘ ℓ) kind I φ))
        (.predicate (.plain (timedFormula kind I φ)))) ↔
    Section3.Judgement.holds σ P β ⟨i.1+1,by omega⟩
      (.predicate (.upper c b kind I φ)) := by
  have hnum := defer_successor_numeric σ P α i hn c d b hcd
  exact boundary_merge_at σ P _ _ c d b _ kind I φ hnum.1 (by intros; rfl) hnum.2

/-- The paired-reset check successor also admits the mixed merger with no
manually supplied numeric side conditions. The value a is the branch's original
lower-endpoint reset value; the proof requires only its actual NNReal type. -/
theorem check_successor_boundary_merge [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (i : Fin P.size) (hn : i.1 + 1 < P.size) (c d : Clock) (a : NNReal)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) (hcd : c ≠ d) :
    let ℓ := (P.interval ⟨i.1+1,hn⟩).leftBoundary
    let β := ((ClockResetSet.singleton c a).union (ClockResetSet.singleton d 0)).apply
      (ClockResetSet.elapse α (STLTableau.Judgement.duration P i))
    Section3.Judgement.holds σ P β ⟨i.1+1,by omega⟩
      (.conj (.predicate (.bounded c d ℓ (¬ₘ ℓ) kind I φ))
        (.predicate (.plain (timedFormula kind I φ)))) ↔
    Section3.Judgement.holds σ P β ⟨i.1+1,by omega⟩
      (.predicate (.upper c ℓ kind I φ)) := by
  have hnum := check_successor_numeric
    (ClockResetSet.elapse α (STLTableau.Judgement.duration P i))
    c d a (P.interval ⟨i.1+1,hn⟩).leftBoundary hcd
  exact boundary_merge_at σ P _ _ c d _ _ kind I φ hnum.1 (by intros; rfl) hnum.2

end STLTableau.Section4.Finiteness
