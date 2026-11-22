import STLTableaux.Automata.Execution.ObservedFlowExecution
import STLTableaux.Semantics.Intervals.CommonTimeBoundaries

/-! Restrictions of actual observed flows to positive subintervals. Cutting
a flow preserves its closed endpoint states and half-open signal observation;
the cut itself is an idle connector, not an invented automaton jump. -/
namespace STLTableau.HybridAutomaton
variable {M L V : Type*} {H : HybridAutomaton M L V} {σ : FiniteSignal V}

namespace ObservedFlow
variable (f : ObservedFlow H σ)

noncomputable def slice (a b : NNReal) (ab : a < b) (br : b ≤ f.duration) :
    ObservedFlow H σ where
  start := f.step.stateAt ⟨a, by simp [ab.le.trans br]⟩
  finish := f.step.stateAt ⟨b, by simp [br]⟩
  beginTime := f.beginTime + a
  endTime := f.beginTime + b
  duration := b - a
  positive := by rw [NNReal.coe_sub ab.le]; exact sub_pos.mpr ab
  duration_eq := by rw [NNReal.coe_sub ab.le]; ring
  curve := fun t => f.curve ⟨a + t.val, by
    have bound := t.property.2
    simp only [NNReal.coe_sub ab.le] at bound
    constructor
    · exact add_nonneg a.coe_nonneg t.property.1
    · linarith [show (b : ℝ) ≤ f.duration from br]⟩
  step := by
    have ar := ab.le.trans br
    refine ⟨rfl, ?_, ?_, ?_⟩
    · apply congrArg f.curve
      exact Subtype.ext (by simp)
    · apply congrArg f.curve
      apply Subtype.ext
      dsimp
      rw [NNReal.coe_sub ab.le]
      ring
    · intro t
      let u : Set.Icc (0 : ℝ) (f.duration - a : NNReal) := ⟨t.val, by
        have bound := t.property.2
        simp only [NNReal.coe_sub ab.le] at bound
        constructor
        · exact t.property.1
        · simp only [NNReal.coe_sub ar]
          linarith [show (b : ℝ) ≤ f.duration from br]⟩
      have result := H.trajectory_closed.suffix f.step.evolves a ar u
      simpa only [HybridFlow.suffixCurve, ContinuousStep.stateAt, add_zero] using result
  observe := by
    intro t ht
    have before : t.val < f.endTime := by
      linarith [show (b : ℝ) ≤ f.duration from br, f.duration_eq]
    have observed := f.observe t ⟨by linarith [a.coe_nonneg], before⟩
    refine observed.trans ?_
    apply congrArg f.curve
    exact Subtype.ext (by dsimp; ring)

theorem slice_begin (a b : NNReal) (ab : a < b) (br : b ≤ f.duration) :
    (f.slice a b ab br).beginTime = f.beginTime + a := rfl

theorem slice_end (a b : NNReal) (ab : a < b) (br : b ≤ f.duration) :
    (f.slice a b ab br).endTime = f.beginTime + b := rfl

theorem slice_join (a b c : NNReal) (ab : a < b) (bc : b < c) (cr : c ≤ f.duration) :
    (f.slice a b ab (bc.le.trans cr)).finish = (f.slice b c bc cr).start := rfl

theorem slice_visits (a b : NNReal) (ab : a < b) (br : b ≤ f.duration)
    {s : H.State} (visit : (f.slice a b ab br).VisitsState s) : f.VisitsState s := by
  obtain ⟨t, ht⟩ := visit
  exact ⟨_, ht⟩

/-- Every original point in the chosen closed subinterval remains a visit. -/
theorem visits_slice (a b : NNReal) (ab : a < b) (br : b ≤ f.duration)
    (t : Set.Icc (0 : ℝ) f.duration) (inside : (a : ℝ) ≤ t.val ∧ t.val ≤ b) :
    (f.slice a b ab br).VisitsState (f.step.stateAt t) := by
  let u : Set.Icc (0 : ℝ) (b - a : NNReal) := ⟨t.val - a, by
    rw [NNReal.coe_sub ab.le]
    constructor <;> linarith [inside.1, inside.2]⟩
  refine ⟨u, Prod.ext rfl ?_⟩
  apply congrArg f.curve
  exact Subtype.ext (by dsimp [u]; ring)

/-- The same restriction, specified by absolute observation times. -/
noncomputable def sliceAt (a b : ℝ)
    (inside : f.beginTime ≤ a ∧ a < b ∧ b ≤ f.endTime) : ObservedFlow H σ :=
  f.slice ⟨a - f.beginTime, sub_nonneg.mpr inside.1⟩
    ⟨b - f.beginTime, by linarith [inside.1, inside.2.1]⟩
    (by change a - f.beginTime < b - f.beginTime; linarith [inside.2.1])
    (by change b - f.beginTime ≤ f.duration; linarith [inside.2.2, f.duration_eq])

theorem sliceAt_begin (a b : ℝ)
    (inside : f.beginTime ≤ a ∧ a < b ∧ b ≤ f.endTime) :
    (f.sliceAt a b inside).beginTime = a := by
  change f.beginTime + (a - f.beginTime) = a
  ring

theorem sliceAt_end (a b : ℝ)
    (inside : f.beginTime ≤ a ∧ a < b ∧ b ≤ f.endTime) :
    (f.sliceAt a b inside).endTime = b := by
  change f.beginTime + (b - f.beginTime) = b
  ring

theorem sliceAt_join (a b c : ℝ)
    (first : f.beginTime ≤ a ∧ a < b ∧ b ≤ f.endTime)
    (second : f.beginTime ≤ b ∧ b < c ∧ c ≤ f.endTime) :
    (f.sliceAt a b first).finish = (f.sliceAt b c second).start := rfl

theorem sliceAt_join_of_eq (g : ObservedFlow H σ) (same : g = f) (a b c : ℝ)
    (first : f.beginTime ≤ a ∧ a < b ∧ b ≤ f.endTime)
    (second : g.beginTime ≤ b ∧ b < c ∧ c ≤ g.endTime) :
    (f.sliceAt a b first).finish = (g.sliceAt b c second).start := by
  subst g
  rfl

theorem sliceAt_congr (g : ObservedFlow H σ) (same : f = g) (a b : ℝ)
    (first : f.beginTime ≤ a ∧ a < b ∧ b ≤ f.endTime)
    (second : g.beginTime ≤ a ∧ a < b ∧ b ≤ g.endTime) :
    f.sliceAt a b first = g.sliceAt a b second := by
  subst g
  rfl

theorem visits_sliceAt (a b : ℝ)
    (inside : f.beginTime ≤ a ∧ a < b ∧ b ≤ f.endTime)
    (t : Set.Icc (0 : ℝ) f.duration)
    (atTime : a ≤ f.beginTime + t.val ∧ f.beginTime + t.val ≤ b) :
    (f.sliceAt a b inside).VisitsState (f.step.stateAt t) := by
  apply f.visits_slice
  change a - f.beginTime ≤ t.val ∧ t.val ≤ b - f.beginTime
  constructor <;> linarith [atTime.1, atTime.2]

theorem sliceAt_start (a b : ℝ)
    (inside : f.beginTime ≤ a ∧ a < b ∧ b ≤ f.endTime) (atStart : a = f.beginTime) :
    (f.sliceAt a b inside).start = f.start := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  change f.curve _ = f.start.val.2
  convert f.step.2.1 using 1
  apply congrArg f.curve
  apply Subtype.ext
  change a - f.beginTime = 0
  linarith

theorem sliceAt_finish (a b : ℝ)
    (inside : f.beginTime ≤ a ∧ a < b ∧ b ≤ f.endTime) (atEnd : b = f.endTime) :
    (f.sliceAt a b inside).finish = f.finish := by
  apply Subtype.ext
  refine Prod.ext f.step.1 ?_
  change f.curve _ = f.finish.val.2
  convert f.step.2.2.1 using 1
  apply congrArg f.curve
  apply Subtype.ext
  change b - f.beginTime = (f.duration : ℝ)
  linarith [f.duration_eq]

run_elab do
  for name in #[``slice, ``slice_join, ``slice_visits, ``visits_slice,
      ``sliceAt, ``sliceAt_join, ``sliceAt_join_of_eq, ``sliceAt_congr,
      ``visits_sliceAt, ``sliceAt_start, ``sliceAt_finish] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name} uses unexpected axiom {ax}"

end ObservedFlow
end STLTableau.HybridAutomaton
