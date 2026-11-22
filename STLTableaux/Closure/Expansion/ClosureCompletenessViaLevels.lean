import STLTableaux.Closure.Expansion.FaithfulExpansionRank

/-! An auxiliary proof of closure completeness by complete expansion rounds.
Choose a satisfied form at rank zero, then a minimal closed extension below it. -/
namespace STLTableau.Section3.ConcreteContextual
variable {Clock Var : Type*}

theorem satisfied_closure_via_expansion_levels [DecidableEq Clock] [Infinite Clock]
    (F : TransitionForm Clock Var) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : F.holds σ P α k) (hi : F.EvaluatedInvariant σ P α k)
    (hst : F.UnderlyingStable σ P) :
    ∃ (i : ℕ) (G Fa U : TransitionForm Clock Var),
      G ∈ alphaExpansionLevel F i ∧ alphaLevelRank F i = 0 ∧
      NextAlphaPath F Fa ∧ catalogue.IsClosure Fa U ∧ SyntacticallySubsumed U G ∧
      U.holds σ P α k ∧ U.EvaluatedInvariant σ P α k ∧ U.UnderlyingStable σ P := by
  obtain ⟨i, hizero⟩ := alpha_level_rank_eventually_zero F
  have hz := hizero i le_rfl
  obtain ⟨G, hm, hsat, hInv, hStable⟩ := alpha_level_satisfied F σ P α k hs hi hst i
  have hclosed : catalogue.IsClosed G :=
    (ExpansionFamily.familyRank_zero_iff_closed
      (alpha_expansionLevel_bounded F i)).1 hz G hm
  obtain ⟨Fa, hp, hFaG⟩ := alpha_level_source F i hm
  obtain ⟨U, hc, hUG⟩ := catalogue.exists_minimal_closed_extension_below hFaG hclosed
  exact ⟨i, G, Fa, U, hm, hz, hp, hc, hUG, hUG.sound σ P α k hsat,
    hUG.evaluatedInvariant σ P α k hInv, hUG.underlyingStable σ P hStable⟩

theorem satisfied_closure_exists_via_rounds [DecidableEq Clock] [Infinite Clock]
    (F : TransitionForm Clock Var) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : F.holds σ P α k) (hi : F.EvaluatedInvariant σ P α k)
    (hst : F.UnderlyingStable σ P) :
    ∃ Fa U, TransitionForm.AlphaEquivalent Fa F ∧ Fa.current = F.current ∧
      catalogue.IsClosure Fa U ∧ U.holds σ P α k ∧
      U.EvaluatedInvariant σ P α k ∧ U.UnderlyingStable σ P := by
  obtain ⟨i, G, Fa, U, hm, hz, hp, hc, hUG, hsat, hInv, hStable⟩ :=
    satisfied_closure_via_expansion_levels F σ P α k hs hi hst
  exact ⟨Fa, U, hp.alphaEquivalent, hp.current, hc, hsat, hInv, hStable⟩

end STLTableau.Section3.ConcreteContextual
