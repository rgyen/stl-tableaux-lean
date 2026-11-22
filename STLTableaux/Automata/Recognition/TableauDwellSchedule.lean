import STLTableaux.Automata.Recognition.TableauRealClockSchedule

/-! Guard/reset schedules for selected positive or singleton dwell states.
A singleton is a stationary observation, not an extra continuous evolution.
Every edge below is a supplied actual jump; no transitive shortcut is added. -/
namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
variable (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)

def DwellStep (s t : (T.toAutomaton h τ hτ).State) (d : NNReal) : Prop :=
  (d = 0 ∧ t = s) ∨ ∃ γ, (T.toAutomaton h τ hτ).ContinuousStep s t d γ

theorem DwellStep.mode_eq {s t : (T.toAutomaton h τ hτ).State} {d : NNReal}
    (hd : T.DwellStep h τ hτ s t d) : s.val.1 = t.val.1 := by
  rcases hd with ⟨_, rfl⟩ | ⟨_, hc⟩
  · rfl
  · exact hc.1

theorem DwellStep.clock_eq {s t : (T.toAutomaton h τ hτ).State} {d : NNReal}
    (hd : T.DwellStep h τ hτ s t d) (c : T.clocks) :
    t.val.2 (.inr (.inl c)) = s.val.2 (.inr (.inl c)) + d := by
  rcases hd with ⟨rfl, rfl⟩ | ⟨_, hc⟩
  · simp
  · have hf := (hc.2.2.2 ⟨d, by simp⟩).1.1 c
    rwa [hc.2.2.1] at hf

/-- Actual initialization and jumps supply all guards and resets, including
across singleton frames. Clock values need not be nonnegative. -/
theorem exists_dwell_schedule (n : ℕ)
    (entry finish : ℕ → (T.toAutomaton h τ hτ).State) (d : ℕ → NNReal)
    (hinit : (entry 0).val ∈ (T.toAutomaton h τ hτ).initial)
    (hd : ∀ i < n, T.DwellStep h τ hτ (entry i) (finish i) (d i))
    (hj : ∀ i < n, (T.toAutomaton h τ hτ).DiscreteStep (finish i) (entry (i + 1))) :
    ∃ incoming : ℕ → EdgeLabel Clock, ∃ v : ℕ → T.HAVar → ℝ,
      (incoming 0, (entry 0).val.1.val) ∈ T.initial ∧
      (∀ i < n, ((entry i).val.1.val, incoming (i + 1), (entry (i + 1)).val.1.val) ∈ T.edges) ∧
      (∀ i ≤ n, T.guardsHold (incoming i) (v i)) ∧
      (∀ i < n, ∀ c : T.clocks,
        v (i + 1) (.inr (.inl c)) = T.reset (incoming i).resets (v i) (.inr (.inl c)) + d i) := by
  classical
  obtain ⟨l₀, hi₀, v₀, hg₀, hr₀⟩ := hinit
  choose edge hedge hguard hreset hbound using
    fun (i : Fin n) => (T.discreteStep_iff h τ hτ).mp (hj i.val i.isLt)
  let incoming : ℕ → EdgeLabel Clock
    | 0 => l₀
    | j + 1 => if hj : j < n then edge ⟨j, hj⟩ else l₀
  let v : ℕ → T.HAVar → ℝ
    | 0 => v₀
    | j + 1 => if hj : j < n then (finish j).val.2 else v₀
  have hin (j : ℕ) (hj : j < n) : incoming (j + 1) = edge ⟨j, hj⟩ := dif_pos hj
  have hv (j : ℕ) (hj : j < n) : v (j + 1) = (finish j).val.2 := dif_pos hj
  have hentry (j : ℕ) (hj : j ≤ n) (c : T.clocks) :
      (entry j).val.2 (.inr (.inl c)) = T.reset (incoming j).resets (v j) (.inr (.inl c)) := by
    cases j with
    | zero => rw [hr₀]; rfl
    | succ j =>
      have hj' : j < n := by omega
      rw [hreset ⟨j, hj'⟩, hin j hj', hv j hj']
  refine ⟨incoming, v, hi₀, ?_, ?_, ?_⟩
  · intro i hi
    rw [hin i hi, congrArg Subtype.val ((hd i hi).mode_eq T h τ hτ)]
    exact hedge ⟨i, hi⟩
  · intro i hi
    cases i with
    | zero => exact hg₀
    | succ i =>
      have hi' : i < n := by omega
      rw [hin i hi', hv i hi']
      exact hguard ⟨i, hi'⟩
  · intro i hi c
    rw [hv i hi, (hd i hi).clock_eq T h τ hτ c, hentry i (by omega) c]

theorem DwellStep.globalClock_eq {s t : (T.toAutomaton h τ hτ).State} {d : NNReal}
    (hd : T.DwellStep h τ hτ s t d) :
    t.val.2 T.globalClock = s.val.2 T.globalClock + d := by
  rcases hd with ⟨rfl, rfl⟩ | ⟨_, hc⟩
  · simp
  · exact T.continuousStep_globalClock h τ hτ hc

/-- The global clock recovers the chosen absolute boundary times, even when
some dwell times are zero. No semantic trace premise is used. -/
theorem dwell_entry_globalClock (n : ℕ)
    (entry finish : ℕ → (T.toAutomaton h τ hτ).State) (d : ℕ → NNReal)
    (hinit : (entry 0).val ∈ (T.toAutomaton h τ hτ).initial)
    (hd : ∀ i < n, T.DwellStep h τ hτ (entry i) (finish i) (d i))
    (hj : ∀ i < n, (T.toAutomaton h τ hτ).DiscreteStep (finish i) (entry (i + 1)))
    (b : Fin (n + 1) → ℝ) (hstart : b ⟨0, by omega⟩ = 0)
    (hduration : ∀ i : Fin n, (d i.val : ℝ) =
      b ⟨i.val + 1, by omega⟩ - b ⟨i.val, by omega⟩) :
    ∀ (i : ℕ) (hi : i ≤ n), (entry i).val.2 T.globalClock = b ⟨i, by omega⟩ := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [hstart]
    exact T.initial_globalClock_zero h τ hτ hinit
  | succ i ih =>
    intro hi
    have hip : i < n := by omega
    rw [T.jump_globalClock_preserved h τ hτ (hj i hip),
      (hd i hip).globalClock_eq T h τ hτ, ih (by omega), hduration ⟨i, hip⟩]
    ring

/-- Below the horizon an actually entered mode is nonterminal. The initial
case uses the separate initial-mode property, not a fictitious incoming jump. -/
theorem dwell_entry_nonterminal (n : ℕ)
    (entry finish : ℕ → (T.toAutomaton h τ hτ).State) (d : ℕ → NNReal)
    (hinit : (entry 0).val ∈ (T.toAutomaton h τ hτ).initial)
    (hninitial : (entry 0).val.1 ∉ T.terminalModes)
    (hd : ∀ i < n, T.DwellStep h τ hτ (entry i) (finish i) (d i))
    (hj : ∀ i < n, (T.toAutomaton h τ hτ).DiscreteStep (finish i) (entry (i + 1)))
    (b : Fin (n + 1) → ℝ) (hstart : b ⟨0, by omega⟩ = 0)
    (hduration : ∀ i : Fin n, (d i.val : ℝ) =
      b ⟨i.val + 1, by omega⟩ - b ⟨i.val, by omega⟩)
    (i : ℕ) (hi : i ≤ n) (htime : b ⟨i, by omega⟩ < τ) :
    (entry i).val.1 ∉ T.terminalModes := by
  cases i with
  | zero => exact hninitial
  | succ i =>
    intro ht
    obtain ⟨edge, _, _, hguard⟩ := hj i (by omega)
    have hge := hguard.2.1 ht
    rw [T.dwell_entry_globalClock h τ hτ n entry finish d hinit hd hj b hstart hduration
      (i + 1) hi] at hge
    exact (not_lt_of_ge hge) htime

end STLTableau.Section4.Tableau
