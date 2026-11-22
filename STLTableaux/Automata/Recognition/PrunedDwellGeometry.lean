import STLTableaux.Automata.Execution.TerminalPruning
import STLTableaux.Automata.Recognition.TableauDwellSchedule

/-! Geometric facts from actual jumps of the pruned translation. No partition
or label-satisfaction premise is used to establish these boundary facts. -/
namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)

theorem pruned_no_jump_from_terminal {s t : (T.toPrunedAutomaton h τ hτ).State}
    (ht : Section3.Local.terminal ∈ T.label s.val.1.val) :
    ¬ (T.toPrunedAutomaton h τ hτ).DiscreteStep s t := by
  intro hj
  obtain ⟨l, he, _⟩ := (T.pruneTerminal.discreteStep_iff
    (T.pruneTerminal_translationReady h) τ hτ).mp hj
  exact he.2.2.2 ht

theorem pruned_discreteSteps_from_terminal_eq
    {s t : (T.toPrunedAutomaton h τ hτ).State}
    (hj : Relation.ReflTransGen (T.toPrunedAutomaton h τ hτ).DiscreteStep s t)
    (ht : Section3.Local.terminal ∈ T.label s.val.1.val) : s = t := by
  induction hj using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hstep _ _ => exact (T.pruned_no_jump_from_terminal h τ hτ ht hstep).elim

/-- At the horizon a discrete tail contains at most one actual jump. This
retains the genuine edge; it does not replace a chain by an invented shortcut. -/
theorem pruned_discreteSteps_at_horizon
    {s t : (T.toPrunedAutomaton h τ hτ).State}
    (hj : Relation.ReflTransGen (T.toPrunedAutomaton h τ hτ).DiscreteStep s t)
    (hc : s.val.2 T.globalClock = τ) :
    s = t ∨ (T.toPrunedAutomaton h τ hτ).DiscreteStep s t := by
  induction hj using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl rfl
  | @head a b hab hbt _ =>
      have hb : b.val.2 T.globalClock = τ :=
        (T.pruneTerminal.jump_globalClock_preserved
          (T.pruneTerminal_translationReady h) τ hτ hab).trans hc
      have ht : Section3.Local.terminal ∈ T.label b.val.1.val := by
        by_contra hn
        have hlt := T.pruneTerminal.nonterminal_entry_lt_horizon
          (T.pruneTerminal_translationReady h) τ hτ hab hn
        change b.val.2 T.globalClock < τ at hlt
        rw [hb] at hlt
        exact lt_irrefl _ hlt
      have he := T.pruned_discreteSteps_from_terminal_eq h τ hτ hbt ht
      exact Or.inr (he ▸ hab)

theorem pruned_dwell_boundaries_lt_horizon (n : ℕ)
    (entry finish : ℕ → (T.toPrunedAutomaton h τ hτ).State) (d : ℕ → NNReal)
    (hinit : (entry 0).val ∈ (T.toPrunedAutomaton h τ hτ).initial)
    (hd : ∀ i < n, T.pruneTerminal.DwellStep (T.pruneTerminal_translationReady h)
      τ hτ (entry i) (finish i) (d i))
    (hj : ∀ i < n, (T.toPrunedAutomaton h τ hτ).DiscreteStep
      (finish i) (entry (i + 1)))
    (b : Fin (n + 1) → ℝ) (hstart : b ⟨0, by omega⟩ = 0)
    (hduration : ∀ i : Fin n, (d i.val : ℝ) =
      b ⟨i.val + 1, by omega⟩ - b ⟨i.val, by omega⟩) :
    ∀ i : Fin n, b ⟨i.val, by omega⟩ < τ := by
  intro i
  have hn : Section3.Local.terminal ∉ T.label (entry i.val).val.1.val := by
    obtain ⟨l, he, _⟩ := (T.pruneTerminal.discreteStep_iff
      (T.pruneTerminal_translationReady h) τ hτ).mp (hj i.val i.isLt)
    have hm := (hd i.val i.isLt).mode_eq T.pruneTerminal
      (T.pruneTerminal_translationReady h) τ hτ
    simpa only [congrArg Subtype.val hm] using he.2.2.2
  have hc := T.pruneTerminal.dwell_entry_globalClock
    (T.pruneTerminal_translationReady h) τ hτ n entry finish d hinit hd hj
    b hstart hduration i.val (by omega)
  by_cases hz : i.val = 0
  · have hi : (⟨i.val, by omega⟩ : Fin (n + 1)) = ⟨0, by omega⟩ := Fin.ext hz
    rw [hi, hstart]
    exact hτ
  · have hp : i.val - 1 < n := by omega
    have he : i.val - 1 + 1 = i.val := by omega
    have hjprev := hj (i.val - 1) hp
    rw [he] at hjprev
    have hlt := T.pruneTerminal.nonterminal_entry_lt_horizon
      (T.pruneTerminal_translationReady h) τ hτ hjprev hn
    rwa [hc] at hlt

/-- Durations alone give monotone absolute boundaries, including zero dwells. -/
theorem dwell_boundaries_monotone {n : ℕ} (b : Fin (n + 1) → ℝ) (d : ℕ → NNReal)
    (hduration : ∀ i : Fin n, (d i.val : ℝ) =
      b ⟨i.val + 1, by omega⟩ - b ⟨i.val, by omega⟩) : Monotone b := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  have hd := hduration i
  have hn := (d i.val).property
  change b ⟨i.val, by omega⟩ ≤ b ⟨i.val + 1, by omega⟩
  linarith

end STLTableau.Section4.Tableau
