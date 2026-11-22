import STLTableaux.Automata.Recognition.ExecutionObservedPath
import STLTableaux.Automata.Recognition.ExecutionObservedJumpBlock
import STLTableaux.Automata.Recognition.PrunedDwellGeometry

/-! Observe the actual final discrete tail when stopping inside the signal
domain. Full-semantic-state reflexive jumps may be omitted, as in the other
discrete blocks. Every retained jump keeps its own edge, guard and reset. -/
namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {σ : FiniteSignal T.HAVar} (e : (T.toAutomaton h τ hτ).Execution σ)

theorem observed_early_final_steps
    (hearly : e.boundary ⟨e.count, by omega⟩ < σ.horizon)
    {s : (T.toAutomaton h τ hτ).State}
    (steps : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep s e.finalState)
    (incoming : EdgeLabel Clock) :
    ∃ p ds,
      T.ExecutionPathWitness h τ hτ s e.finalState p ∧
      T.TimedPath p s.val.2 e.finalState.val.2 (0 :: ds) ∧
      T.ObservedPath h τ hτ e p
        (e.boundary ⟨e.count, by omega⟩) (e.boundary ⟨e.count, by omega⟩) (0 :: ds) ∧
      p.firstIncoming = incoming := by
  classical
  induction steps using Relation.ReflTransGen.head_induction_on generalizing incoming with
  | refl =>
      refine ⟨.last incoming _, [], .stop _ _, .last incoming _ (ClockElapse.zero T _),
        .last (Or.inl (.atFinal _ .refl hearly)) ?_, rfl⟩
      simp
  | @head a b hab rest ih =>
      by_cases heq : a = b
      · subst b
        exact ih incoming
      obtain ⟨l, hedge, hg, hr, _⟩ := (T.discreteStep_iff h τ hτ).mp hab
      obtain ⟨p, ds, hw, ht, hp, hin⟩ := ih l
      refine ⟨.step incoming a.val.1.val p, 0 :: ds,
        .jump incoming (hin ▸ hedge) (hin ▸ hg) (hin ▸ hr) hab hw,
        .step incoming _ (ClockElapse.zero T _) (hin ▸ hg) ?_,
        .step (.atFinal a ((Relation.ReflTransGen.single hab).trans rest) hearly) ?_ hp, rfl⟩
      · rw [hin]
        exact hr ▸ ht
      · simp

variable {σ' : FiniteSignal T.HAVar}

/-- The last positive flow and its actual final jump block form an observed
suffix, including early stopping and a zero-width horizon endpoint. -/
theorem pruned_last_flow_observed
    (e : (T.toPrunedAutomaton h σ'.horizon σ'.horizon_pos).Execution σ')
    (incoming : EdgeLabel Clock) :
    let i : Fin e.count := ⟨e.count - 1, by have := e.nonempty; omega⟩
    ∃ p ds,
      T.pruneTerminal.ExecutionPathWitness (T.pruneTerminal_translationReady h)
        σ'.horizon σ'.horizon_pos (e.start i) e.finalState p ∧
      T.pruneTerminal.TimedPath p (e.start i).val.2 e.finalState.val.2 ds ∧
      T.pruneTerminal.ObservedPath (T.pruneTerminal_translationReady h)
        σ'.horizon σ'.horizon_pos e p
        (e.boundary ⟨i.val, by omega⟩) (e.boundary ⟨e.count, by omega⟩) ds ∧
      p.firstIncoming = incoming := by
  intro i
  let U := T.pruneTerminal
  let hU := T.pruneTerminal_translationReady h
  have hi : i.val + 1 = e.count := by dsimp [i]; have := e.nonempty; omega
  have hidx : (⟨i.val + 1, by omega⟩ : Fin (e.count + 1)) = ⟨e.count, by omega⟩ := Fin.ext hi
  rcases lt_or_eq_of_le e.last_le_horizon with hearly | hend
  · obtain ⟨p, ds, hw, ht, hp, hin⟩ :=
      U.observed_early_final_steps hU σ'.horizon σ'.horizon_pos e hearly e.finalSteps incoming
    have hp' : U.ObservedPath hU σ'.horizon σ'.horizon_pos e p
        (e.boundary ⟨i.val + 1, by omega⟩) (e.boundary ⟨e.count, by omega⟩) (0 :: ds) := by
      simpa only [hidx] using hp
    obtain ⟨hw', ht', hp''⟩ := hp'.prepend_flow_with_witness U hU _ _ e i e.finalState hw ht
    exact ⟨p, e.duration i :: ds, hw', ht', hp'', hin⟩
  · have hc := U.continuousStep_clockElapse hU σ'.horizon σ'.horizon_pos (e.continuousStep i)
    have hd : e.boundary ⟨e.count, by omega⟩ =
        e.boundary ⟨i.val, by omega⟩ + (e.duration i : ℝ) := by
      have hh := e.duration_eq i
      rw [hidx] at hh
      linarith
    have ho : U.ExecutionObservedPiece hU σ'.horizon σ'.horizon_pos e
        (e.start i).val.1.val (e.boundary ⟨i.val, by omega⟩) (e.boundary ⟨e.count, by omega⟩) := by
      simpa only [hidx] using (ExecutionObservedPiece.flow (T := U) (h := hU)
        (τ := σ'.horizon) (hτ := σ'.horizon_pos) (e := e) i)
    have hm := congrArg Subtype.val (e.continuousStep i).1
    have hcend : (e.finish i).val.2 T.globalClock = σ'.horizon := by
      change (e.finish i).val.2 U.globalClock = σ'.horizon
      rw [U.execution_finish_clock hU σ'.horizon σ'.horizon_pos e i, hidx, hend]
    rcases T.pruned_discreteSteps_at_horizon h σ'.horizon σ'.horizon_pos e.finalSteps hcend with heq | hj
    · have hw : U.ExecutionPathWitness hU σ'.horizon σ'.horizon_pos
          (e.finish i) e.finalState (.last incoming (e.finish i).val.1.val) := by
        rw [← heq]
        exact .stop _ _
      refine ⟨.last incoming (e.finish i).val.1.val, [e.duration i],
        .flow _ _ (e.continuousStep i) hw, ?_, .last (Or.inl ?_) hd, rfl⟩
      · rw [← heq]
        exact .last incoming _ hc
      · rwa [← hm]
    · have hterminal : Section3.Local.terminal ∈ U.label e.finalState.val.1.val := by
        by_contra hn
        have hlt := U.nonterminal_entry_lt_horizon hU σ'.horizon σ'.horizon_pos hj hn
        have hclock := U.execution_final_clock hU σ'.horizon σ'.horizon_pos e
        have hclock' : e.finalState.val.2 U.globalClock = σ'.horizon := hclock.trans hend
        rw [hclock'] at hlt
        exact (lt_irrefl _ hlt)
      obtain ⟨l, hedge, hg, hr, _⟩ := (U.discreteStep_iff hU σ'.horizon σ'.horizon_pos).mp hj
      let tail : Path Clock State := .last l e.finalState.val.1.val
      have hw : U.ExecutionPathWitness hU σ'.horizon σ'.horizon_pos
          (e.finish i) e.finalState (.step incoming (e.finish i).val.1.val tail) :=
        .jump incoming hedge hg hr hj (.stop _ _)
      refine ⟨.step incoming (e.finish i).val.1.val tail, [e.duration i, 0],
        .flow _ _ (e.continuousStep i) hw, ?_, ?_, rfl⟩
      · refine TimedPath.step incoming _ (p := tail) hc hg ?_
        change U.TimedPath tail (U.reset l.resets (e.finish i).val.2) e.finalState.val.2 [0]
        have hr' : e.finalState.val.2 = U.reset l.resets (e.finish i).val.2 := hr
        rw [← hr']
        exact .last l _ (ClockElapse.zero U _)
      · apply ObservedPath.step (d := e.duration i) (hm ▸ ho) hd
        exact .last (Or.inr ⟨hend, hend, hterminal⟩) (by simp)

end STLTableau.Section4.Tableau
