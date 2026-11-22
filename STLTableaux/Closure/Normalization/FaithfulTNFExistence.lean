import STLTableaux.Closure.Catalogue.FaithfulContextualFreshBranch

/-! Transition form of an expansion branch under the source resets. -/
namespace STLTableau.Section3.TransitionForm
variable {Clock Var : Type*}

/-- Lemma 4.13 (transition-form existence) for fixed compatible representatives. -/
theorem tnf_exists_of_compatible (Φ F : TransitionForm Clock Var)
    (hg : F.current.guards = ∅)
    (hc : Φ.UnionCompatible (F.underReset Φ.current.resets)) :
    ∃ U : TransitionForm Clock Var,
      SyntacticallySubsumed Φ U ∧
      SyntacticallySubsumed (F.underReset Φ.current.resets) U ∧
      ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
        (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P),
        U.holds σ P α k ↔
          Φ.holds σ P α k ∧ F.holds σ P (Φ.current.resets.apply α) k := by
  refine ⟨Φ.union (F.underReset Φ.current.resets), hc.left, hc.right, ?_⟩
  intro σ P α k
  exact (hc.holds σ P α k).trans
    (and_congr Iff.rfl (F.underReset_holds Φ.current.resets hg σ P α k))

/-- Lemma 4.13 with compatible representatives chosen by renaming bound clocks. -/
theorem tnf_exists_up_to_alpha [Infinite Clock] (Φ F : TransitionForm Clock Var)
    (hg : F.current.guards = ∅) :
    ∃ (Φa Fa U : TransitionForm Clock Var),
      AlphaEquivalent Φa Φ ∧ AlphaEquivalent Fa F ∧
      Φa.current = Φ.current ∧
      SyntacticallySubsumed Φa U ∧
      SyntacticallySubsumed (Fa.underReset Φ.current.resets) U ∧
      ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
        (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P),
        U.holds σ P α k ↔
          Φ.holds σ P α k ∧ F.holds σ P (Φ.current.resets.apply α) k := by
  obtain ⟨e, Fa, hfix, ha, hc⟩ := contextual_compatible_branch Φ F
  have hΦ : AlphaEquivalent (Φ.alphaNext e) Φ := .next Φ e hfix
  have hgFa : Fa.current.guards = ∅ := ha.current_guards.trans hg
  obtain ⟨U, hleft, hright, he⟩ :=
    tnf_exists_of_compatible (Φ.alphaNext e) Fa hgFa hc
  refine ⟨Φ.alphaNext e, Fa, U, hΦ, ha, rfl, hleft, hright, ?_⟩
  intro σ P α k
  exact (he σ P α k).trans
    (and_congr (hΦ.holds σ P α k) (ha.holds σ P (Φ.current.resets.apply α) k))

end STLTableau.Section3.TransitionForm
