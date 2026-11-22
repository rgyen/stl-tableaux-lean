import STLTableaux.Automata.Recognition.RealClockTrace
import STLTableaux.Automata.Recognition.TableauDiscreteCorrespondence

/-! Extract a full real-clock schedule from actual declared coordinates.
Undeclared clocks are extended recursively, not silently set to zero after
each flow. No nonnegative-coordinate hypothesis is needed. -/
namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)

/-- Extend initial declared coordinates only. Subsequent values are computed
by the very same reset/elapse recurrence on every clock. -/
noncomputable def realClockSchedule (incoming : ℕ → EdgeLabel Clock)
    (duration : ℕ → NNReal) (v : T.HAVar → ℝ) : ℕ → Clock → ℝ := by
  classical
  exact Nat.rec (fun c => if hc : c ∈ T.clocks then v (.inr (.inl ⟨c, hc⟩)) else 0)
    (fun i ν c => Trace.realReset (incoming i).resets ν c + duration i)

theorem realClockSchedule_zero (incoming : ℕ → EdgeLabel Clock)
    (duration : ℕ → NNReal) (v : T.HAVar → ℝ) (c : T.clocks) :
    T.realClockSchedule incoming duration v 0 c.val = v (.inr (.inl c)) := by
  simp [realClockSchedule, c.property]

theorem realClockSchedule_succ (incoming : ℕ → EdgeLabel Clock)
    (duration : ℕ → NNReal) (v : T.HAVar → ℝ) (i : ℕ) :
    T.realClockSchedule incoming duration v (i + 1) = fun c =>
      Trace.realReset (incoming i).resets (T.realClockSchedule incoming duration v i) c +
        duration i := rfl

/-- Actual reset and flow equations imply agreement at every declared clock.
The recurrence is required only before the last frame. -/
theorem realClockSchedule_agrees (n : ℕ) (incoming : ℕ → EdgeLabel Clock)
    (duration : ℕ → NNReal) (v : ℕ → T.HAVar → ℝ)
    (hstep : ∀ i < n, ∀ c : T.clocks,
      v (i + 1) (.inr (.inl c)) =
        T.reset (incoming i).resets (v i) (.inr (.inl c)) + duration i)
    (i : ℕ) (hi : i ≤ n) (c : T.clocks) :
    T.realClockSchedule incoming duration (v 0) i c.val = v i (.inr (.inl c)) := by
  induction i with
  | zero => exact T.realClockSchedule_zero incoming duration (v 0) c
  | succ i ih =>
    rw [T.realClockSchedule_succ, hstep i (by omega) c]
    change Trace.realReset (incoming i).resets
      (T.realClockSchedule incoming duration (v 0) i) c.val + _ = _
    cases hr : (incoming i).resets.value c.val with
    | none => simp only [Trace.realReset, reset, hr]; rw [ih (by omega)]
    | some a => simp only [Trace.realReset, reset, hr]

/-- Guard checks use the same actual incoming coordinates as the recurrence.
In particular, this result does not choose a new valuation for each guard. -/
theorem realClockSchedule_guards (n : ℕ) (incoming : ℕ → EdgeLabel Clock)
    (duration : ℕ → NNReal) (v : ℕ → T.HAVar → ℝ)
    (hstep : ∀ i < n, ∀ c : T.clocks,
      v (i + 1) (.inr (.inl c)) =
        T.reset (incoming i).resets (v i) (.inr (.inl c)) + duration i)
    (hg : ∀ i ≤ n, T.guardsHold (incoming i) (v i))
    (i : ℕ) (hi : i ≤ n) :
    ∀ g ∈ (incoming i).guards, realComparison g.relation
      (T.realClockSchedule incoming duration (v 0) i g.clock) g.bound := by
  intro g hmem
  obtain ⟨hc, hcmp⟩ := hg i hi g hmem
  rw [T.realClockSchedule_agrees n incoming duration v hstep i hi ⟨g.clock, hc⟩]
  exact hcmp

variable (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)

/-- Initial entry has the same old-clock reset equation; only the separate
global clock is initialized specially. This covers the first flow. -/
theorem initial_continuousStep_realClocks
    {a b : (T.toAutomaton h τ hτ).State} {r : NNReal}
    {γ : Set.Icc (0 : ℝ) r → T.HAVar → ℝ}
    (ha : a.val ∈ (T.toAutomaton h τ hτ).initial)
    (hc : (T.toAutomaton h τ hτ).ContinuousStep a b r γ) :
    ∃ (l : EdgeLabel Clock) (v : T.HAVar → ℝ),
      (l, a.val.1.val) ∈ T.initial ∧ T.guardsHold l v ∧
      ∀ c : T.clocks, b.val.2 (.inr (.inl c)) =
        T.reset l.resets v (.inr (.inl c)) + r := by
  obtain ⟨l, hi, v, hg, hr⟩ := ha
  refine ⟨l, v, hi, hg, ?_⟩
  intro c
  have hf := ((hc.2.2.2 ⟨r, by simp⟩).1).1 c
  rw [hc.2.2.1, hr] at hf
  exact hf

/-- A real jump followed by a flow supplies one reset/elapse equation, with
the actual incoming edge label. No compatibility with NNReal is assumed. -/
theorem discreteStep_continuousStep_realClocks
    {s a b : (T.toAutomaton h τ hτ).State} {r : NNReal}
    {γ : Set.Icc (0 : ℝ) r → T.HAVar → ℝ}
    (hj : (T.toAutomaton h τ hτ).DiscreteStep s a)
    (hc : (T.toAutomaton h τ hτ).ContinuousStep a b r γ) :
    ∃ l : EdgeLabel Clock, (s.val.1.val, l, a.val.1.val) ∈ T.edges ∧
      T.guardsHold l s.val.2 ∧ ∀ c : T.clocks,
        b.val.2 (.inr (.inl c)) = T.reset l.resets s.val.2 (.inr (.inl c)) + r := by
  obtain ⟨l, he, hg, hr, _⟩ := (T.discreteStep_iff h τ hτ).mp hj
  refine ⟨l, he, hg, ?_⟩
  intro c
  have hf := ((hc.2.2.2 ⟨r, by simp⟩).1).1 c
  rw [hc.2.2.1, hr] at hf
  exact hf

end STLTableau.Section4.Tableau
