import STLTableaux.Semantics.Invariants.Invariants
import STLTableaux.Semantics.Counterexamples.Claims

/-! Counterexamples to the unqualified splitting statements in `Claims.lean`,
and regressions for interval-predicate satisfaction and residual satisfaction. -/
namespace STLTableau.Counterexamples
open scoped STL
open STLTableau.IntervalPredicate

private def signal : FiniteSignal Unit where
  horizon := 3
  horizon_pos := by norm_num
  value := fun t _ => t.val

private def positive : Formula Unit := .neg (.atom
  ⟨1, fun _ => (), fun x => -x 0, .ge⟩)
private def atLeastOne : Formula Unit := .atom
  ⟨1, fun _ => (), fun x => x 0 - 1, .ge⟩
private def zeroToOne : BoundedTimeInterval := ⟨0, 1, by norm_num, by norm_num⟩
private def closedPiece : MarkedInterval := ⟨0, 1, ●, ●⟩

/-- The `↑` predicate with an open stored marker omits time zero. -/
theorem open_upper_always_true :
    predicateSatisfies signal closedPiece (fun _ : Nat => 0)
      (.upper 0 ○ .always zeroToOne positive) := by
  intro t ht
  change ¬ -t.val ≥ 0
  have hleft : 0 < t.val := by
    have hl := ht.1
    change (0 : ℝ) - 0 + 0 < t.val ∨ (0 - 0 + 0 = t.val ∧ False) at hl
    simpa using hl
  linarith

/-- Plain always includes the closed left endpoint and therefore fails. -/
theorem plain_always_false :
    ¬ predicateSatisfies signal closedPiece (fun _ : Nat => 0)
      (.plain (□[(zeroToOne : TimeInterval)] positive)) := by
  intro h
  let t : signal.Time := ⟨0, by norm_num [signal]⟩
  have htJ : t.val ∈ closedPiece := by
    change (0 < (0 : ℝ) ∨ (0 = 0 ∧ True)) ∧ (0 < 1 ∨ (0 = 1 ∧ True))
    norm_num
  have htI : t.val ∈ (zeroToOne : TimeInterval).translate t.val := by
    norm_num [t, TimeInterval.translate, zeroToOne, TimeInterval.mem_bounded]
  have hf := (FiniteSignal.satisfies_always_iff signal
    (zeroToOne : TimeInterval) positive t).1 (h t htJ) t htI
  change ¬ -(0 : ℝ) ≥ 0 at hf
  linarith

/-- Without its current-interval containment convention, the split fails
for a zero source clock, open stored marker and closed declaring left endpoint.
Freshness of c and d does not repair this endpoint mismatch. -/
theorem printed_upper_split_fails :
    predicateSatisfies signal closedPiece (fun _ : Nat => 0)
      (.upper 0 ○ .always zeroToOne positive) ∧
    ¬ (predicateSatisfies signal closedPiece (fun _ : Nat => 0)
        (.bounded 0 1 ○ ○ .always zeroToOne positive) ∧
      predicateSatisfies signal closedPiece (fun _ : Nat => 0)
        (.plain (□[(zeroToOne : TimeInterval)] positive))) :=
  ⟨open_upper_always_true, fun h => plain_always_false h.2⟩

/-- Residual satisfaction can hold for an always predicate whose
untruncated manuscript interpretation is false. -/
theorem residual_always_is_strictly_weaker :
    let J : MarkedInterval := ⟨1, 2, ●, ●⟩
    let α : ClockValuation Nat := fun _ => 2
    IntervalPredicate.Satisfies signal J α (.upper 0 ● .always zeroToOne atLeastOne) ∧
    ¬ predicateSatisfies signal J α (.upper 0 ● .always zeroToOne atLeastOne) := by
  dsimp
  constructor
  · intro t _ hs
    change t.val - 1 ≥ 0
    rcases hs with hs | ⟨hs, _⟩ <;> dsimp at hs <;> linarith
  · intro h
    let t : signal.Time := ⟨0, by norm_num [signal]⟩
    have ht : t.val ∈ alwaysRegion
        (scope (⟨1, 2, ●, ●⟩ : MarkedInterval) (fun _ : Nat => 2)
          (.upper 0 ● .always zeroToOne atLeastOne)) zeroToOne := by
      change ((1 : ℝ) - 2 + 0 < 0 ∨ (1 - 2 + 0 = 0 ∧ True)) ∧
        (0 < 2 + 1 ∨ (0 = 2 + 1 ∧ True))
      norm_num
    have hf := h t ht
    change (0 : ℝ) - 1 ≥ 0 at hf
    linarith

private def twoPiece : IntervalPartition signal.domain where
  size := 2
  interval := fun i => if i.val = 0 then closedPiece else ⟨1, 3, ○, ○⟩
  nonempty := by
    intro i
    fin_cases i <;> norm_num [closedPiece, MarkedInterval.carrier_eq]
  pairwiseDisjoint := by
    intro i j hne
    fin_cases i <;> fin_cases j <;>
      simp_all [closedPiece, MarkedInterval.carrier_eq, Set.disjoint_left] <;>
      intro x hx hy <;> linarith
  covers := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      fin_cases i <;>
        simp [closedPiece, MarkedInterval.carrier_eq, FiniteSignal.domain, signal] at hi ⊢ <;>
        constructor <;> linarith
    · intro hx
      have hx' : 0 ≤ x ∧ x < 3 := hx
      apply Set.mem_iUnion.2
      by_cases hle : x ≤ 1
      · refine ⟨⟨0, by omega⟩, ?_⟩
        simpa [closedPiece, MarkedInterval.carrier_eq] using And.intro hx'.1 hle
      · refine ⟨⟨1, by omega⟩, ?_⟩
        simpa [MarkedInterval.carrier_eq] using And.intro (lt_of_not_ge hle) hx'.2
  ordered := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [closedPiece] at *

/-- A concrete partition and judgement refute the literal equivalence,
including its fresh reset clock and its actual left-marker test. -/
theorem printed_upper_split_judgement_fails :
    let lhs : Judgement Nat Unit := .predicate (.upper 0 ○ .always zeroToOne positive)
    let rhs : Judgement Nat Unit :=
      (⟦1 ↦ᶜ 0⟧ ·ⱼ (.predicate (.bounded 0 1 ○ ○ .always zeroToOne positive) ∧ⱼ lty[●])) ∧ⱼ
        .predicate (.plain (□[(zeroToOne : TimeInterval)] positive))
    satisfies signal twoPiece (fun _ => 0) ⟨0, by norm_num [twoPiece]⟩ lhs ∧
      ¬ satisfies signal twoPiece (fun _ => 0) ⟨0, by norm_num [twoPiece]⟩ rhs := by
  dsimp
  constructor
  · simpa only [satisfies, twoPiece, Fin.val_zero, ite_true, zero_lt_two, dite_true] using open_upper_always_true
  · intro h
    apply plain_always_false
    have hp := h.2
    simpa only [satisfies, twoPiece, Fin.val_zero, ite_true, zero_lt_two, dite_true] using hp

/-- Implication (4) also needs the reset clock to be fresh. Reusing c=d
forgets the tracked left endpoint and makes its literal unrestricted form false. -/
theorem next_reset_same_clock_fails :
    let premise : Judgement Nat Unit :=
      Xⱼ (⟦0 ↦ᶜ 0⟧ ·ⱼ
        (.predicate (.bounded 0 0 ● ● .always zeroToOne positive) ∧ⱼ lty[○]))
    let conclusion : Judgement Nat Unit := .predicate (.upper 0 ● .always zeroToOne positive)
    satisfies signal twoPiece (fun _ => 0) ⟨0, by norm_num [twoPiece]⟩ premise ∧
      ¬ satisfies signal twoPiece (fun _ => 0) ⟨0, by norm_num [twoPiece]⟩ conclusion := by
  dsimp
  constructor
  · change (predicateSatisfies signal (⟨1, 3, ○, ○⟩ : MarkedInterval)
      (⟦0 ↦ᶜ 0⟧.apply _) (.bounded 0 0 ● ● .always zeroToOne positive)) ∧ _
    refine ⟨?_, rfl⟩
    intro t ht
    change ¬ -t.val ≥ 0
    have hl : (1 : ℝ) - 0 + 0 < t.val ∨
        (1 - 0 + 0 = t.val ∧ True) := by
      simpa only [scope, alwaysRegion, Scope.toMarkedInterval, zeroToOne,
        ClockResetSet.apply_singleton_self, NNReal.coe_zero, Marker.Includes] using ht.1
    rcases hl with hl | ⟨hl, _⟩ <;> linarith
  · intro h
    let t : signal.Time := ⟨0, by norm_num [signal]⟩
    have hpred : predicateSatisfies signal closedPiece (fun _ : Nat => 0)
        (.upper 0 ● .always zeroToOne positive) := by
      simpa only [satisfies, twoPiece, Fin.val_zero, ite_true, zero_lt_two, dite_true] using h
    have ht : t.val ∈ alwaysRegion
        (scope closedPiece (fun _ : Nat => 0) (.upper 0 ● .always zeroToOne positive)) zeroToOne := by
      change (t.val ∈ (alwaysRegion
        (scope closedPiece (fun _ : Nat => 0)
          (.upper 0 ● .always zeroToOne positive)) zeroToOne).toMarkedInterval)
      norm_num [t, alwaysRegion, scope, Scope.toMarkedInterval, closedPiece,
        zeroToOne, MarkedInterval.mem_iff, Marker.Includes]
    have hf := hpred t ht
    change ¬ -(0 : ℝ) ≥ 0 at hf
    linarith

/-- Part (1) cannot be a fixed-marker judgement equivalence. The marker
schema/existential interpretation is a separate, valid statement. -/
theorem printed_opening_not_equivalent :
    ¬ Equivalent
      (.predicate (.plain (□[(zeroToOne : TimeInterval)] (.truth : Formula Unit))))
      (Claims.opening 0 ○ zeroToOne .truth) := by
  intro he
  have hl : satisfies signal twoPiece (fun _ : Nat => 0)
      ⟨0, by norm_num [twoPiece]⟩
      (.predicate (.plain (□[(zeroToOne : TimeInterval)] (.truth : Formula Unit)))) := by
    simp only [satisfies, twoPiece, Fin.val_zero, ite_true, zero_lt_two, dite_true,
      predicateSatisfies]
    intro t _
    exact (FiniteSignal.satisfies_always_iff _ _ _ _).2 (by
      intro u _
      trivial)
  have hr := (he signal twoPiece (fun _ => 0) ⟨0, by norm_num [twoPiece]⟩).1 hl
  have hm := hr.2
  change (● : Marker) = ○ at hm
  cases hm

theorem not_printed_opening_fixed_marker : ¬ Claims.PrintedOpeningFixedMarker := by
  intro h
  exact printed_opening_not_equivalent (h 0 ○ zeroToOne .truth)

/-- A judgement-level negation of the literal part (2) instance. -/
theorem printed_upper_split_not_equivalent :
    ¬ Equivalent (.predicate (.upper 0 ○ .always zeroToOne positive))
      (Claims.split 0 1 ○ ● zeroToOne positive) := by
  intro he
  obtain ⟨hl, hnr⟩ := printed_upper_split_judgement_fails
  exact hnr ((he signal twoPiece (fun _ => 0) ⟨0, by norm_num [twoPiece]⟩).1 hl)

theorem not_printed_split_fixed_marker : ¬ Claims.PrintedSplitFixedMarker := by
  intro h
  exact printed_upper_split_not_equivalent (h 0 1 ○ ● zeroToOne positive (by decide))

/-- Without current-interval containment, selecting the right marker cannot
repair the unrestricted split: its unclocked predicate adds a missing endpoint.
This is outside the intended containment convention of proposition (2). -/
theorem printed_upper_split_chosen_marker_fails :
    satisfies signal twoPiece (fun _ : Nat => 0) ⟨0, by norm_num [twoPiece]⟩
      (.predicate (.upper 0 ○ .always zeroToOne positive)) ∧
    ¬ ∃ m : Marker, satisfies signal twoPiece (fun _ : Nat => 0)
      ⟨0, by norm_num [twoPiece]⟩ (Claims.split 0 1 ○ m zeroToOne positive) := by
  refine ⟨printed_upper_split_judgement_fails.1, ?_⟩
  rintro ⟨m, hm⟩
  apply plain_always_false
  have hp := hm.2
  simpa only [satisfies, twoPiece, Fin.val_zero, ite_true, zero_lt_two, dite_true] using hp

theorem not_printed_split_chosen_marker : ¬ Claims.PrintedSplitChosenMarker := by
  intro h
  obtain ⟨hl, hnr⟩ := printed_upper_split_chosen_marker_fails
  exact hnr ((h 0 1 ○ zeroToOne positive (by decide) signal twoPiece
    (fun _ => 0) ⟨0, by norm_num [twoPiece]⟩).1 hl)

end STLTableau.Counterexamples
