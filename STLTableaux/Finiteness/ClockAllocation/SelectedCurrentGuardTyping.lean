import STLTableaux.Finiteness.ClockAllocation.SelectedSourceRoleTyping
import STLTableaux.Finiteness.ClockAllocation.SelectedBoundaryRoleTyping

/-! Actual current guards of the same completed selection are typed: old
outside guards keep their input roles and strict additions use eligible lefts. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var Slot : Type*} [DecidableEq Clock] [Fintype Slot]
variable {N : Section3.StateForm Clock Var} {J : MixedJ Clock Var} {W : Set Clock}
    {owned : OwnedPending J N.resets W} {H Er : MixedJ Clock Var}
    {τ : Slot→FiniteInventory.Triple Clock Var} {incoming : Equiv.Perm Clock}
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}

theorem SelectedTree.retrospective_current_guards_typed
    (O : InputOrigins σ P α k N)
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (root : Formula Var) (hInput : SafeNormalization J (.ofState N))
    {A : Set Clock} {F : Section3.TransitionForm Clock Var}
    (hFacts : SelectedOutputFacts owned A O.strictClocks σ P α k H Er F)
    (frame : SlotFrame τ N incoming)
    (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot) :
    ∀g∈F.current.guards,
      SlotFrame.GuardTyped τ (retrospectiveRoleMap root T frame newSlot) g := by
  rcases hFacts with ⟨_,_,_,_,_,_,_,_,_,hGuards,_,_⟩
  have hInputGuards : N.guards=currentGuards J := hInput.currentGuards_eq
  have hext : ∀c s r,frame.role c=some (s,r) →
      retrospectiveRoleMap root T frame newSlot c=some (s,r) :=
    fun _ _ _ h=>retrospectiveRoleMap_input root T hInput frame newSlot h
  intro g hg
  rcases hGuards hg with hold | hstrict
  · have hN : g∈N.guards := by rw [hInputGuards];exact hold
    exact (frame.guards g hN).mono hext
  · exact O.strict_guard_typed_extended frame _ hext g hstrict

/-- Both complete current predicate annotations and actual current guards are
typed. Reset typing remains a separate actual reset-provenance obligation. -/
theorem SelectedTree.retrospective_current_predicates_guards_typed
    (O : InputOrigins σ P α k N)
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (root : Formula Var) (hBelow : ∀entry∈T.rawLedger,entry.source.formula≼root)
    (hInput : SafeNormalization J (.ofState N))
    (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    {A : Set Clock} {F : Section3.TransitionForm Clock Var}
    (hFacts : SelectedOutputFacts owned A O.strictClocks σ P α k H Er F)
    (frame : SlotFrame τ N incoming)
    (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot)
    (hFamily : ∀sig,SlotFrame.slotFamily τ (newSlot sig)=sig.val) :
    (∀p,Local.predicate p∈F.current.locals →
      SlotFrame.PredicateTyped τ (retrospectiveRoleMap root T frame newSlot) p) ∧
    (∀g∈F.current.guards,
      SlotFrame.GuardTyped τ (retrospectiveRoleMap root T frame newSlot) g) :=
  ⟨T.retrospective_current_predicates_typed O root hBelow hInput hLocal hFacts.1 frame newSlot hFamily,
    T.retrospective_current_guards_typed O root hInput hFacts frame newSlot⟩
end STLTableau.Section4.Finiteness
