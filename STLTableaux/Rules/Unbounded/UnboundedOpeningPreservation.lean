import STLTableaux.Rules.Unbounded.UnboundedPreservation

namespace STLTableau.UnboundedClocked
open scoped STL
variable {Clock Var : Type*}

/-- Opening establishes the full printed invariant, including past-cover
separation, for its actual marker and reset valuation. -/
theorem opening_preserves [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c : Clock) (m : Marker) (kind : TemporalKind)
    (a : NNReal) (φ : Formula Var)
    (hs : Node.holds σ P α k (opening c m kind a φ)) :
    EvaluatedInvariant σ P α k (opening c m kind a φ) := by
  change (∀ hk : k.1 < P.size,
    Invariant σ P ((ClockResetSet.singleton c 0).apply α) k hk
      (.upper c m kind a φ)) ∧ True
  refine ⟨?_, trivial⟩
  intro hk
  have hm : (P.interval ⟨k.1, hk⟩).leftBoundary = m := by
    simpa only [opening, Node.holds, dif_pos hk] using hs.2
  have hc : (ClockResetSet.singleton c 0).apply α c = 0 :=
    ClockResetSet.apply_singleton_self c 0 α
  cases kind with
  | always =>
      change (_ : ℝ) <[Marker.imp m (P.interval ⟨k.1, hk⟩).leftBoundary] (a : ℝ)
      rw [hc, hm]
      rcases a.coe_nonneg.eq_or_lt with hz | hp
      · exact Or.inr ⟨hz, (Marker.includes_imp _ _).2 id⟩
      · exact Or.inl hp
  | eventually =>
      refine ⟨?_, pastSeparated_of_clock_zero σ P _ k hk c m a φ hc hm⟩
      have hne := (MarkedInterval.nonempty_iff _).1 (P.nonempty ⟨k.1, hk⟩)
      rw [hc]
      simp only [NNReal.coe_zero, zero_add]
      rw [← hm]
      rcases hne with hlt | ⟨heq, hm⟩
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, hm⟩

end STLTableau.UnboundedClocked
