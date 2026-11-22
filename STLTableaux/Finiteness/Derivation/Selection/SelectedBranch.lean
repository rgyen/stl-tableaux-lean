import STLTableaux.Finiteness.Derivation.Branches.RawBranchCompleteness
import STLTableaux.Finiteness.Derivation.Branches.RawBranchNormalization
import STLTableaux.Closure.Normalization.NormalizedStability

/-! Actual fresh branch selection followed by safe normalization. This is one
local expansion, not existence of a whole resolution tree or bounded path. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

/-- A ready satisfied non-atomic predicate admits a concrete fresh branch whose
constructed safe normal form preserves truth, the FULL invariant and stability.
No branch-choice or normalization-existence premise is supplied. -/
theorem exists_selected_branch
    (p : Predicate Clock Var) (hp : p.Ready) (hn : ¬ p.IsAtomic) (Γ : MixedJ Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.val < P.size, p.Invariant σ P α k hk)
    (hst : σ.StablePartition p.formula P)
    (hs : Section3.Judgement.holds σ P α k (.predicate p)) :
    ∃ (B : MixedJ Clock Var) (F : Section3.TransitionForm Clock Var),
      RawBranch p B ∧ FreshFor p B Γ ∧ SafeNormalization B F ∧ F.current.guards = ∅ ∧
      F.holds σ P α k ∧ F.EvaluatedInvariant σ P α k ∧ F.UnderlyingStable σ P := by
  obtain ⟨B,hB,hfresh,htrue,hfull,hstable⟩ :=
    RawBranch.exists_preserving_fresh p hp hn Γ σ P α k hi hst hs
  obtain ⟨F,hsafe,hguards⟩ := hB.safe_normalization
  exact ⟨B,F,hB,hfresh,hsafe,hguards,(hsafe.holds σ P α k).2 htrue,
    (hB.invariant_normalization hsafe.normalizes σ P α k).2 hfull,
    (Section3.TransitionForm.normalize_underlyingStable B hsafe.normalizes σ P).2 hstable⟩

end STLTableau.Section4.Finiteness
