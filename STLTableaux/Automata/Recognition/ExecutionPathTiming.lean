import STLTableaux.Automata.Translation.TableauExecutionWitness
import STLTableaux.Automata.Recognition.TableauExecutionTime

/-! Residence times and real clock equations for the same execution path.
The durations are extracted, not supplied as an additional schedule premise.
They may be zero. This is not yet a partition or a marker assignment. -/
namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)

def ClockElapse (v w : T.HAVar → ℝ) (r : NNReal) : Prop :=
  (∀ c : T.clocks, w (.inr (.inl c)) = v (.inr (.inl c)) + r) ∧
    w T.globalClock = v T.globalClock + r

theorem ClockElapse.zero (v : T.HAVar → ℝ) : T.ClockElapse v v 0 := by
  constructor <;> simp

theorem ClockElapse.add {u v w : T.HAVar → ℝ} {r d : NNReal}
    (h₁ : T.ClockElapse u v r) (h₂ : T.ClockElapse v w d) :
    T.ClockElapse u w (r + d) := by
  constructor
  · intro c; rw [h₂.1 c, h₁.1 c]; simp [add_assoc]
  · rw [h₂.2, h₁.2]; simp [add_assoc]

/-- The starting valuation is after the first incoming reset. At every later
frame the guard is checked before that frame's reset, exactly. -/
inductive TimedPath : Path Clock State → (T.HAVar → ℝ) → (T.HAVar → ℝ) →
    List NNReal → Prop
  | last (incoming) (s) {v w r} (elapse : T.ClockElapse v w r) :
      TimedPath (.last incoming s) v w [r]
  | step (incoming) (s) {p v u w r ds}
      (elapse : T.ClockElapse v u r)
      (guard : T.guardsHold p.firstIncoming u)
      (tail : TimedPath p (T.reset p.firstIncoming.resets u) w ds) :
      TimedPath (.step incoming s p) v w (r :: ds)

/-- Additional flow in the first mode increases only its residence time;
it neither creates nor removes a tableau frame. -/
theorem TimedPath.prepend_elapse {p u v w r ds}
    (he : T.ClockElapse u v r) (ht : T.TimedPath p v w ds) :
    ∃ ds', T.TimedPath p u w ds' := by
  cases ht with
  | last incoming s hlast => exact ⟨_, .last incoming s (he.add T hlast)⟩
  | step incoming s hhead hg htail =>
      exact ⟨_, .step incoming s (he.add T hhead) hg htail⟩

theorem TimedPath.total_duration {p v w ds} (ht : T.TimedPath p v w ds) :
    w T.globalClock = v T.globalClock + (ds.sum : ℝ) := by
  induction ht with
  | last incoming s he => simpa using he.2
  | step incoming s he hg ht ih =>
      rw [T.reset_globalClock, he.2] at ih
      simpa [add_assoc] using ih

theorem TimedPath.frame_count {p v w ds} (ht : T.TimedPath p v w ds)
    (labels : State → Set (Section3.Local Clock Var)) (hf : ∀ s, (labels s).Finite) :
    ds.length = (p.trace labels hf).length := by
  induction ht with
  | last => rfl
  | step incoming s he hg ht ih => simpa [Path.trace, Trace.length] using congrArg Nat.succ ih

variable (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)

theorem continuousStep_clockElapse {s u : (T.toAutomaton h τ hτ).State}
    {r : NNReal} {γ : Set.Icc (0 : ℝ) r → T.HAVar → ℝ}
    (hc : (T.toAutomaton h τ hτ).ContinuousStep s u r γ) :
    T.ClockElapse s.val.2 u.val.2 r := by
  constructor
  · intro c
    have hv := (hc.2.2.2 ⟨r, by simp⟩).1.1 c
    rwa [hc.2.2.1] at hv
  · exact T.continuousStep_globalClock h τ hτ hc

/-- Extract durations and all sequential clock checks from actual flow/jump
evidence. No nonnegative valuation, marker, partition or satisfaction premise. -/
theorem ExecutionPathWitness.timing {s t p}
    (hw : T.ExecutionPathWitness h τ hτ s t p) :
    ∃ ds, T.TimedPath p s.val.2 t.val.2 ds := by
  induction hw with
  | stop s incoming => exact ⟨[0], .last incoming _ (ClockElapse.zero T _)⟩
  | flow r γ hc hw ih =>
      obtain ⟨ds, ht⟩ := ih
      exact ht.prepend_elapse T (T.continuousStep_clockElapse h τ hτ hc)
  | jump incoming he hg hr hj hw ih =>
      obtain ⟨ds, ht⟩ := ih
      exact ⟨0 :: ds, .step incoming _ (ClockElapse.zero T _) hg (hr ▸ ht)⟩

/-- Entry times obtained by accumulating the extracted residence times. -/
def residenceBoundary (ds : List NNReal) (i : ℕ) : ℝ := (ds.take i).sum

theorem residenceBoundary_zero (ds : List NNReal) : residenceBoundary ds 0 = 0 := by
  simp [residenceBoundary]

theorem residenceBoundary_last (ds : List NNReal) :
    residenceBoundary ds ds.length = (ds.sum : ℝ) := by simp [residenceBoundary]

theorem residenceBoundary_step (ds : List NNReal) (i : ℕ) (hi : i < ds.length) :
    residenceBoundary ds (i + 1) - residenceBoundary ds i = (ds[i] : ℝ) := by
  simp [residenceBoundary, List.sum_take_succ ds i hi]

theorem residenceBoundary_monotone (ds : List NNReal) : Monotone (residenceBoundary ds) := by
  apply monotone_nat_of_le_succ
  intro i
  by_cases hi : i < ds.length
  · have hd := residenceBoundary_step ds i hi
    have hn := (ds[i]).coe_nonneg
    linarith
  · have hle : ds.length ≤ i := by omega
    simp [residenceBoundary, List.take_of_length_le hle,
      List.take_of_length_le (show ds.length ≤ i + 1 by omega)]

/-- The accepting path, residence times and stopping-time equation all come
from the same execution. This retains `stop ≤ horizon`, not equality. -/
theorem execution_accepting_timed_path {σ : FiniteSignal T.HAVar}
    (e : (T.toAutomaton h τ hτ).Execution σ)
    (goal : e.finalState.val.1 ∈ T.goalModes) :
    ∃ p ds, p.run T ∧ p.accepting T ∧
      T.ExecutionPathWitness h τ hτ e.initialState e.finalState p ∧
      T.TimedPath p e.initialState.val.2 e.finalState.val.2 ds ∧
      (ds.sum : ℝ) = e.boundary ⟨e.count, by omega⟩ ∧
      (ds.sum : ℝ) ≤ σ.horizon ∧
      ∃ v : T.HAVar → ℝ, T.guardsHold p.firstIncoming v ∧
        e.initialState.val.2 = T.initialReset p.firstIncoming.resets v := by
  obtain ⟨p, hr, ha, hw, hv⟩ := T.execution_accepting_path_witness h τ hτ e goal
  obtain ⟨ds, ht⟩ := hw.timing T h τ hτ
  have hsum := ht.total_duration T
  rw [T.initial_globalClock_zero h τ hτ e.initial_mem,
    T.execution_final_clock h τ hτ e, zero_add] at hsum
  exact ⟨p, ds, hr, ha, hw, ht, hsum.symm, hsum ▸ e.last_le_horizon, hv⟩

end STLTableau.Section4.Tableau
