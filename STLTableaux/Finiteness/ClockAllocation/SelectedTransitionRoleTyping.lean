import STLTableaux.Finiteness.ClockAllocation.SelectedAnnotationRoleTyping
import STLTableaux.Finiteness.ClockAllocation.SelectedCurrentGuardTyping
import STLTableaux.Finiteness.ClockAllocation.SelectedNextPredicateTyping

/-! Actual whole selected-output typing, assembled from source, numeric and
 boundary provenance. No state-typing premise is assumed. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var Slot : Type*} [DecidableEq Clock] [Fintype Slot]
variable {N : Section3.StateForm Clock Var} {J : MixedJ Clock Var} {W : Set Clock}
    {owned : OwnedPending J N.resets W} {H Er : MixedJ Clock Var}
    {τ : Slot→FiniteInventory.Triple Clock Var} {incoming : Clock≃Clock}
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}

theorem SelectedTree.retrospective_transition_typed
    (O : InputOrigins σ P α k N)
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (root : Formula Var) (hBelow : ∀entry∈T.rawLedger,entry.source.formula≼root)
    (hInput : SafeNormalization J (.ofState N)) (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (hEmpty : owned.nextInputs=[])
    {A : Set Clock} {F : Section3.TransitionForm Clock Var}
    (hFacts : SelectedOutputFacts owned A O.strictClocks σ P α k H Er F)
    (frame : SlotFrame τ N incoming)
    (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot)
    (hFamily : ∀sig,SlotFrame.slotFamily τ (newSlot sig)=sig.val)
    (hnew : Function.Injective newSlot)
    (hfree : ∀sig,newSlot sig∉SlotFrame.occupied frame.role) :
    SlotFrame.TransitionTyped τ (retrospectiveRoleMap root T frame newSlot) F := by
  constructor
  · exact ⟨T.retrospective_current_predicates_typed O root hBelow hInput hLocal hFacts.1 frame newSlot hFamily,
      T.retrospective_current_guards_typed O root hInput hFacts frame newSlot,
      T.retrospective_current_resets_typed O root hBelow hInput hLocal frame newSlot hFamily hFacts.1⟩
  · intro M hn
    exact ⟨T.retrospective_next_predicates_typed O root hBelow hInput hLocal hEmpty hFacts.1
        frame newSlot hFamily hnew hfree M hn,
      T.retrospective_next_guards_typed O root hBelow hInput hLocal frame newSlot hFamily hEmpty hFacts.1 hn,
      T.retrospective_next_resets_typed O root hBelow hInput hLocal frame newSlot hFamily hEmpty hFacts.1 hn⟩

end STLTableau.Section4.Finiteness
