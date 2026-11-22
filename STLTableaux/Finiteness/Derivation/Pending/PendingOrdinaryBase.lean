import STLTableaux.Finiteness.Derivation.Pending.PendingResetProjection
import STLTableaux.Finiteness.Derivation.CurrentGuardProjection
import STLTableaux.Finiteness.Derivation.Pending.PendingCompletionBase
import STLTableaux.Finiteness.Derivation.CompletionInvariantTransport
import STLTableaux.Finiteness.Derivation.Branches.RawBranchPrivacy
import STLTableaux.Finiteness.Derivation.NextStatePrivacy
import STLTableaux.Finiteness.Derivation.Pending.PendingNextPrivacy

/-! The zero-current-weight case of ordinary pending completion. Its output
uses the proved canonical presentation, rather than retaining irrelevant raw
input reset binders. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

/-- The intended result of ordinary completion. This is an output proposition,
not a field of pending ownership or a premise admitting a completed derivation. -/
def OrdinaryCompletion [DecidableEq Clock] (J : MixedJ Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (A : Set Clock) : Prop :=
  ∃ (H E : MixedJ Clock Var) (F : Section3.TransitionForm Clock Var),
    Nonempty (Resolve J H E) ∧ SafeNormalization H F ∧
    SafeNormalization E F.atomicProjection ∧ F.holds σ P α k ∧
    F.EvaluatedInvariant σ P α k ∧ F.UnderlyingStable σ P ∧ F.Ready ∧
    NextPrivate H ∧ NextPrivate E ∧ F.current.guards = currentGuards J ∧
    Disjoint F.current.resets.clocks A ∧ nextCurrentPrivate F

/-- The actual zero case supplies all recursion promises, including full
invariants for no past satisfaction, guards and current-reset protection. -/
theorem ordinary_completion_zero [DecidableEq Clock]
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (A : Set Clock)
    (hR : Disjoint R.clocks A) (hz : pendingWeight owned.canonical = 0)
    (hNext : NextPrivate J) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hReady : J.Ready) (hHolds : Judgement.holds σ P α k J)
    (hInv : J.EvaluatedInvariant σ P α k) (hStable : J.UnderlyingStable σ P) :
    OrdinaryCompletion J σ P α k A := by
  obtain ⟨F,hsafe⟩ := owned.input_safe
  have hcReady := owned.regroup.ready_iff.1 hReady
  have hcHolds := (owned.regroup.holds_iff σ P α k).1 hHolds
  have hcInv := (owned.regroup.invariant_iff σ P α k).1 hInv
  have hcStable := (owned.regroup.stable_iff σ P).1 hStable
  have hcNext := owned.regroup.nextPrivate_iff.1 hNext
  refine ⟨owned.canonical,owned.canonical,F,
    ⟨.structural owned.regroup (PendingCompletionBase.resolve_zero _ hz)⟩,
    hsafe,PendingCompletionBase.erased_safe _ hz hsafe,
    (hsafe.holds σ P α k).2 hcHolds,(hsafe.fullInvariant σ P α k).2 hcInv,
    (hsafe.stable σ P).2 hcStable,hsafe.ready.2 hcReady,hcNext,hcNext,?_,
    canonical_safe_reset_protection owned.shape hsafe hR,?_⟩
  · exact hsafe.currentGuards_eq.trans owned.regroup.currentGuards_eq.symm
  · apply canonical_next_state_private owned.shape hsafe owned.next_private
    intro K hK
    exact ((canonical_nextPrivate_iff owned.shape).1 hcNext K hK).1

end STLTableau.Section4.Finiteness
