import STLTableaux.Automata.Execution.ZeroTimeShortcut
import STLTableaux.Automata.Recognition.PrunedDwellGeometry

/-! Existing-edge zero-time bypass for the pruned translation. This does not
assert arbitrary path selection: next-generator equality and guard/reset
agreement remain explicit. No transitive edge is inserted into the tableau. -/
namespace STLTableau.Section4.Finiteness
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

theorem finiteRootTableau_pruned_shortcut_overwritten_block
    (X : Set Var) (root : Formula Var)
    (h : (finiteRootTableau (Clock := Clock) X root).TranslationReady)
    (τ : ℝ) (hτ : 0 < τ)
    {s m t : ((finiteRootTableau X root).toPrunedAutomaton h τ hτ).State}
    (hprefix : Relation.ReflTransGen
      ((finiteRootTableau X root).toPrunedAutomaton h τ hτ).DiscreteStep s m)
    (hj : ((finiteRootTableau X root).toPrunedAutomaton h τ hτ).DiscreteStep m t)
    (hn : s.val.1.val.nextPart = m.val.1.val.nextPart)
    (hguards : ∀ l, (m.val.1.val, l, t.val.1.val) ∈
      (finiteRootTableau X root).pruneTerminal.edges →
      ∀ g ∈ l.guards, ∀ hc : g.clock ∈ (finiteRootTableau (Clock := Clock) X root).clocks,
        s.val.2 (.inr (.inl ⟨g.clock, hc⟩)) = m.val.2 (.inr (.inl ⟨g.clock, hc⟩)))
    (hkeep : ∀ l, (m.val.1.val, l, t.val.1.val) ∈
      (finiteRootTableau X root).pruneTerminal.edges →
      ∀ c : (finiteRootTableau (Clock := Clock) X root).clocks, l.resets.value c.val = none →
        s.val.2 (.inr (.inl c)) = m.val.2 (.inr (.inl c))) :
    ((finiteRootTableau X root).toPrunedAutomaton h τ hτ).DiscreteStep s t := by
  let T := finiteRootTableau (Clock := Clock) X root
  let hp := T.pruneTerminal_translationReady h
  obtain ⟨l, he, hg, hr, hb⟩ := (T.pruneTerminal.discreteStep_iff hp τ hτ).mp hj
  have hnon : Section3.Local.terminal ∉ T.label s.val.1.val := by
    intro ht
    have heq := T.pruned_discreteSteps_from_terminal_eq h τ hτ hprefix ht
    subst m
    exact T.pruned_no_jump_from_terminal h τ hτ ht hj
  have hedge : (s.val.1.val, l, t.val.1.val) ∈ T.pruneTerminal.edges :=
    ⟨finiteRootTableau_same_next_edge X root s.val.1.property.1 he.1 hn,
      s.val.1.property.2, t.val.1.property.2, hnon⟩
  have hreset : T.pruneTerminal.reset l.resets s.val.2 =
      T.pruneTerminal.reset l.resets m.val.2 :=
    T.pruneTerminal.reset_eq_of_agree_off_resets l.resets s.val.2 m.val.2
      (fun x => (T.pruneTerminal.discreteSteps_realVariable_preserved hp τ hτ hprefix x).symm)
      (T.pruneTerminal.discreteSteps_globalClock_preserved hp τ hτ hprefix).symm (hkeep l he)
  apply (T.pruneTerminal.discreteStep_iff hp τ hτ).mpr
  exact ⟨l, hedge, T.pruneTerminal.guardsHold_of_agree l s.val.2 m.val.2 hg
    (hguards l he), hr.trans hreset.symm, hb⟩

/-- In a value-preserving block the guard/reset agreement obligations are
automatic; the literal next-generator condition is still needed. -/
theorem finiteRootTableau_pruned_shortcut_stationary_block
    (X : Set Var) (root : Formula Var)
    (h : (finiteRootTableau (Clock := Clock) X root).TranslationReady)
    (τ : ℝ) (hτ : 0 < τ)
    {s m t : ((finiteRootTableau X root).toPrunedAutomaton h τ hτ).State}
    (hprefix : Relation.ReflTransGen
      (fun a b : ((finiteRootTableau X root).toPrunedAutomaton h τ hτ).State =>
        ((finiteRootTableau X root).toPrunedAutomaton h τ hτ).DiscreteStep a b ∧ a.val.2 = b.val.2)
      s m)
    (hj : ((finiteRootTableau X root).toPrunedAutomaton h τ hτ).DiscreteStep m t)
    (hn : s.val.1.val.nextPart = m.val.1.val.nextPart) :
    ((finiteRootTableau X root).toPrunedAutomaton h τ hτ).DiscreteStep s t := by
  have hv : s.val.2 = m.val.2 := by
    clear hj hn
    induction hprefix with
    | refl => rfl
    | tail _ he ih => exact ih.trans he.2
  have hp : Relation.ReflTransGen
      ((finiteRootTableau X root).toPrunedAutomaton h τ hτ).DiscreteStep s m := by
    clear hj hn hv
    induction hprefix with
    | refl => exact .refl
    | tail _ he ih => exact ih.tail he.1
  exact finiteRootTableau_pruned_shortcut_overwritten_block X root h τ hτ hp hj hn
    (fun _ _ _ _ _ => congrFun hv _) (fun _ _ _ _ => congrFun hv _)

end STLTableau.Section4.Finiteness
