import STLTableaux.Automata.Translation.PrelimStateGoal

namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
variable (h : T.TranslationReady) (τ : ℝ)
local notation "H" => T.prelimAutomaton h τ

private theorem goal_chain
    (closed : ∀ (a b : T.states) l, a ∈ T.goalModes →
      (a.val, l, b.val) ∈ T.edges → b ∈ T.goalModes)
    {a b : (H).State} (steps : Relation.ReflTransGen (H).DiscreteStep a b)
    (goal : a.val.1 ∈ T.goalModes) : b.val.1 ∈ T.goalModes := by
  induction steps with
  | refl => exact goal
  | @tail b c _ step ih =>
    obtain ⟨e, hs, ht, _⟩ := step
    have he : (e.val.1.val, e.val.2.1, e.val.2.2.val) ∈ T.edges := e.property
    rw [hs, ht] at he
    exact closed _ _ _ ih he

/-- Every actual goal visit yields one of the appendix's cuts. This also
covers initial and intermediate singleton goals; no cut-existence premise
is added to reachability. -/
theorem prelim_goal_visit_cases
    (closed : ∀ (a b : T.states) l, a ∈ T.goalModes →
      (a.val, l, b.val) ∈ T.edges → b ∈ T.goalModes)
    {σ : FiniteSignal T.TypedVar} (e : (H).PrelimExecution σ) (hh : σ.horizon = τ)
    (s : (H).State) (goal : s ∈ T.prelimGoal h τ) (visit : e.VisitsState s) :
    (∃ i, (e.start i).val.1 ∈ T.goalModes) ∨
      (e.boundary ⟨e.count, by omega⟩ = τ ∧
        ∃ (l : EdgeLabel Clock) (q : T.states),
          (e.finalState.val.1.val, l, q.val) ∈ T.edges ∧
          T.guardsHold l (T.old e.finalState.val.2) ∧ T.EndGoal q) := by
  rcases visit with ⟨i, u, hs⟩ | ⟨_, post⟩ | ⟨i, hi, _, post⟩
  · rcases goal with ordinary | ⟨lower, cert⟩
    · exact Or.inl ⟨i, (congrArg Prod.fst hs) ▸ ordinary⟩
    · have flow := (e.continuousStep i).2.2.2 u
      have cg : s.val.2 (.inl T.globalClock) = e.boundary i.castSucc + u.val := by
        rw [hs]
        exact flow.1.2.1.trans (congrArg (· + u.val) (T.prelim_entry_time h τ e i))
      have hd := e.duration_eq i
      change (e.duration i : ℝ) = e.boundary i.succ - e.boundary i.castSucc at hd
      have upper := e.increasing.monotone (Fin.le_last i.succ)
      change e.boundary i.succ ≤ e.boundary ⟨e.count, by omega⟩ at upper
      have stop := e.last_le_horizon.trans_eq hh
      have endTime : e.boundary ⟨e.count, by omega⟩ = τ := by
        linarith [u.property.2]
      have atEnd : e.boundary i.succ = e.boundary ⟨e.count, by omega⟩ := by
        linarith [u.property.2]
      have index := e.increasing.injective atEnd
      have ilast : i = e.lastIndex := by
        apply Fin.ext
        have idx : i.val + 1 = e.count := congrArg Fin.val index
        change i.val = e.count - 1
        omega
      have hu : u = (⟨e.duration i, by simp⟩ : Set.Icc (0 : ℝ) (e.duration i)) := by
        apply Subtype.ext
        linarith [u.property.2]
      have state : s = e.finalState := by
        apply Subtype.ext
        rw [hs, hu, (e.continuousStep i).2.2.1]
        change ((e.start i).val.1, (e.finish i).val.2) = (e.finish e.lastIndex).val
        rw [← ilast]
        exact Prod.ext (e.continuousStep i).1 rfl
      exact Or.inr ⟨endTime, state ▸ cert⟩
  · have early : s.val.2 (.inl T.globalClock) < τ := by
      rw [← T.prelim_chain_global h τ post, T.prelim_entry_time h τ e]
      exact (e.entry_lt_horizon _).trans_eq hh
    rcases goal with ordinary | ⟨lower, _⟩
    · exact Or.inl ⟨⟨0, e.nonempty⟩, T.goal_chain h τ closed post ordinary⟩
    · exact (early.not_ge lower).elim
  · have early : s.val.2 (.inl T.globalClock) < τ := by
      rw [← T.prelim_chain_global h τ post, T.prelim_entry_time h τ e]
      exact (e.entry_lt_horizon _).trans_eq hh
    rcases goal with ordinary | ⟨lower, _⟩
    · exact Or.inl ⟨⟨i.val + 1, hi⟩, T.goal_chain h τ closed post ordinary⟩
    · exact (early.not_ge lower).elim

end STLTableau.Section4.Tableau
