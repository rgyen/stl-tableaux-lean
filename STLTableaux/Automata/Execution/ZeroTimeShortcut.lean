import STLTableaux.Finiteness.Correctness.FiniteRootTableau
import STLTableaux.Automata.Execution.IdentityJumpElimination
import STLTableaux.Automata.Recognition.ResetAgreement

/-! Existing-edge shortcuts for equal literal next generators. This is not
closure of the automaton edge set under arbitrary zero-time composition. -/
namespace STLTableau.Section4.Finiteness
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

theorem finiteRootTableau_same_next_edge (X : Set Var) (root : Formula Var)
    {F M G : Section3.TransitionForm Clock Var} {l : EdgeLabel Clock}
    (hF : F ∈ (finiteRootTableau X root).states)
    (he : (M, l, G) ∈ (finiteRootTableau X root).edges)
    (hn : F.nextPart = M.nextPart) :
    (F, l, G) ∈ (finiteRootTableau X root).edges := by
  obtain ⟨_, hG, N, hN, hd, hl⟩ := he.1
  change M.nextPart = some N at hN
  exact ⟨⟨hF.1, hG, N, hn.trans hN, hd, hl⟩, hF, he.2.2⟩

/-- The actual last jump can be taken from an earlier mode with the same next
generator and valuation. Its guard, reset, target invariant and horizon guard
are retained, and the direct edge already belongs to the finite tableau. -/
theorem finiteRootTableau_shortcut_jump (X : Set Var) (root : Formula Var)
    (h : (finiteRootTableau (Clock := Clock) X root).TranslationReady)
    (τ : ℝ) (hτ : 0 < τ)
    {s m t : ((finiteRootTableau X root).toAutomaton h τ hτ).State}
    (hj : ((finiteRootTableau X root).toAutomaton h τ hτ).DiscreteStep m t)
    (hn : s.val.1.val.nextPart = m.val.1.val.nextPart)
    (hv : s.val.2 = m.val.2) :
    ((finiteRootTableau X root).toAutomaton h τ hτ).DiscreteStep s t := by
  obtain ⟨l, he, hg, hr, hb⟩ :=
    (Tableau.discreteStep_iff (finiteRootTableau X root) h τ hτ).mp hj
  apply (Tableau.discreteStep_iff (finiteRootTableau X root) h τ hτ).mpr
  refine ⟨l, finiteRootTableau_same_next_edge X root s.val.1.property he hn, ?_, ?_, hb⟩
  · simpa only [hv] using hg
  · simpa only [hv] using hr

/-- A whole value-preserving zero-time prefix can be bypassed, not just one
jump. The last jump may have a nontrivial reset, which is retained exactly. -/
theorem finiteRootTableau_shortcut_stationary_block (X : Set Var) (root : Formula Var)
    (h : (finiteRootTableau (Clock := Clock) X root).TranslationReady)
    (τ : ℝ) (hτ : 0 < τ)
    {s m t : ((finiteRootTableau X root).toAutomaton h τ hτ).State}
    (hprefix : Relation.ReflTransGen
      (fun a b : ((finiteRootTableau X root).toAutomaton h τ hτ).State =>
        ((finiteRootTableau X root).toAutomaton h τ hτ).DiscreteStep a b ∧ a.val.2 = b.val.2)
      s m)
    (hj : ((finiteRootTableau X root).toAutomaton h τ hτ).DiscreteStep m t)
    (hn : s.val.1.val.nextPart = m.val.1.val.nextPart) :
    ((finiteRootTableau X root).toAutomaton h τ hτ).DiscreteStep s t := by
  have hv : s.val.2 = m.val.2 := by
    clear hj hn
    induction hprefix with
    | refl => rfl
    | tail _ he ih => exact ih.trans he.2
  exact finiteRootTableau_shortcut_jump X root h τ hτ hj hn hv

/-- The prefix may change clocks. Bypass it when the last jump's guard clocks
still agree and all remaining differences are overwritten by its reset.
Real variables and the global clock agree automatically along the prefix.
The same target state, reset, invariant and horizon test are retained. -/
theorem finiteRootTableau_shortcut_overwritten_block (X : Set Var) (root : Formula Var)
    (h : (finiteRootTableau (Clock := Clock) X root).TranslationReady)
    (τ : ℝ) (hτ : 0 < τ)
    {s m t : ((finiteRootTableau X root).toAutomaton h τ hτ).State}
    (hprefix : Relation.ReflTransGen
      ((finiteRootTableau X root).toAutomaton h τ hτ).DiscreteStep s m)
    (hj : ((finiteRootTableau X root).toAutomaton h τ hτ).DiscreteStep m t)
    (hn : s.val.1.val.nextPart = m.val.1.val.nextPart)
    (hguards : ∀ l, (m.val.1.val, l, t.val.1.val) ∈ (finiteRootTableau X root).edges →
      ∀ g ∈ l.guards, ∀ hc : g.clock ∈ (finiteRootTableau (Clock := Clock) X root).clocks,
        s.val.2 (.inr (.inl ⟨g.clock, hc⟩)) = m.val.2 (.inr (.inl ⟨g.clock, hc⟩)))
    (hkeep : ∀ l, (m.val.1.val, l, t.val.1.val) ∈ (finiteRootTableau X root).edges →
      ∀ c : (finiteRootTableau (Clock := Clock) X root).clocks, l.resets.value c.val = none →
        s.val.2 (.inr (.inl c)) = m.val.2 (.inr (.inl c))) :
    ((finiteRootTableau X root).toAutomaton h τ hτ).DiscreteStep s t := by
  let T := finiteRootTableau (Clock := Clock) X root
  obtain ⟨l, he, hg, hr, hb⟩ := (T.discreteStep_iff h τ hτ).mp hj
  have hreset : T.reset l.resets s.val.2 = T.reset l.resets m.val.2 :=
    T.reset_eq_of_agree_off_resets l.resets s.val.2 m.val.2
      (fun x => (T.discreteSteps_realVariable_preserved h τ hτ hprefix x).symm)
      (T.discreteSteps_globalClock_preserved h τ hτ hprefix).symm (hkeep l he)
  apply (T.discreteStep_iff h τ hτ).mpr
  exact ⟨l, finiteRootTableau_same_next_edge X root s.val.1.property he hn,
    T.guardsHold_of_agree l s.val.2 m.val.2 hg (hguards l he), hr.trans hreset.symm, hb⟩

/-- Unlike duplicate-mode elimination, the middle mode may be different.
Same-next admission supplies the shortcut edge, and a stationary intervening
reset supplies the same guard valuation to the final incoming label. -/
theorem finiteRootTableau_drop_middle_guarded
    (X : Set Var) (root : Formula Var)
    (incoming middle : EdgeLabel Clock) (F M : Section3.TransitionForm Clock Var)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (α β : ClockValuation Clock)
    (hr : (Path.step incoming F (.step middle M p)).run (finiteRootTableau X root))
    (ha : (Path.step incoming F (.step middle M p)).accepting (finiteRootTableau X root))
    (hn : F.nextPart = M.nextPart)
    (hfix : middle.resets.apply α = α)
    (hg : (Path.step incoming F (.step middle M p)).JumpGuardsHold α β) :
    (Path.step incoming F p).run (finiteRootTableau X root) ∧
    (Path.step incoming F p).accepting (finiteRootTableau X root) ∧
    (Path.step incoming F p).JumpGuardsHold α β := by
  have hv : (Path.step incoming F p).valid (finiteRootTableau X root) :=
    ⟨hr.1.1, hr.1.2.1.2.1,
      finiteRootTableau_same_next_edge X root hr.1.1 hr.1.2.1.2.2 hn⟩
  refine ⟨⟨hv, hr.2⟩, ⟨hv, ha.2⟩, ?_⟩
  have htail := hg.2
  change (Path.step middle M p).JumpGuardsHold (middle.resets.apply α) β at htail
  rw [hfix] at htail
  exact htail

end STLTableau.Section4.Finiteness
