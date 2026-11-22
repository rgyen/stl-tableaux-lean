import STLTableaux.Tableau.Construction.GeneratorPath

/-! Recursive conjunct inclusion for traces, with reset scopes preserved. -/
namespace STLTableau.Section4
open Section3
variable {Clock Var : Type*}
namespace Trace

def FrameIncluded (S T : Section3.StateForm Clock Var) : Prop :=
  S.guards ⊆ T.guards ∧ S.resets = T.resets ∧ S.locals ⊆ T.locals

inductive ScopePreservingSubsumed : Trace Clock Var → Trace Clock Var → Prop
  | last {S T} : FrameIncluded S T → ScopePreservingSubsumed (.last S) (.last T)
  | step {S T u v} : FrameIncluded S T → ScopePreservingSubsumed u v →
      ScopePreservingSubsumed (.step S u) (.step T v)

theorem FrameIncluded.sound {S T : Section3.StateForm Clock Var}
    (h : FrameIncluded S T) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : T.holds σ P α k) : S.holds σ P α k := by
  refine ⟨fun g hg => hs.1 g (h.1 hg), ?_⟩
  intro l hl
  rw [h.2.1]
  exact hs.2 l (h.2.2 hl)

theorem ScopePreservingSubsumed.sound {u v : Trace Clock Var}
    (h : ScopePreservingSubsumed u v)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : v.holds σ P α k) : u.holds σ P α k := by
  induction h generalizing α k with
  | last h => exact h.sound σ P α k hs
  | @step S T u v h ht ih =>
      change T.holds σ P α k ∧ _ at hs
      change S.holds σ P α k ∧ _
      refine ⟨h.sound σ P α k hs.1, ?_⟩
      by_cases hk : k.1 < P.size
      · simp only [dif_pos hk] at hs ⊢
        rw [h.2.1]
        exact ih _ _ hs.2
      · simpa only [dif_neg hk] using hs.2
end Trace

namespace Generated
theorem atomic_trace_subsumed_fullTrace (p : Path Clock (ClosureState Clock Var)) :
    Trace.ScopePreservingSubsumed (p.trace labels labels_finite) p.fullTrace := by
  induction p with
  | last e s => exact .last ⟨fun _ h => h, rfl, fun _ h => h.1⟩
  | step e s t ih => exact .step ⟨fun _ h => h, rfl, fun _ h => h.1⟩ ih
end Generated
end STLTableau.Section4
