import STLTableaux.Finiteness.ClockAllocation.SelectedSuccessorFrame
import STLTableaux.Finiteness.ClockAllocation.SelectedRolePermutation
import STLTableaux.Finiteness.Inventory.RoleTypedInventory
import STLTableaux.Finiteness.ClockAllocation.AllocatedSelectedPath

/-! Actual local sparse-inventory extension. Slot capacity is a concrete
 finite combinatorial input, while roles, permutation, typing and successor
 frames are all constructed from this same selected derivation. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var Slot : Type*} [DecidableEq Clock] [Fintype Slot]
variable {N : Section3.StateForm Clock Var} {J : MixedJ Clock Var} {W : Set Clock}
    {owned : OwnedPending J N.resets W} {H Er : MixedJ Clock Var}
    {τ : Slot→FiniteInventory.Triple Clock Var} {incoming : Clock≃Clock}
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}

theorem SelectedTree.exists_typed_slot_extension
    (O : InputOrigins σ P α k N)
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (root : Formula Var) (hN : Finiteness.StateFormulasBelow root N)
    (hInput : SafeNormalization J (.ofState N)) (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (hEmpty : owned.nextInputs=[])
    {A : Set Clock} {F : Section3.TransitionForm Clock Var}
    (hFacts : SelectedOutputFacts owned A O.strictClocks σ P α k H Er F)
    (frame : SlotFrame τ N incoming)
    (hτ : Function.Injective (fun p : Slot×Fin 3=>FiniteInventory.clockAt (τ p.1) p.2))
    (capacity : ∀sig∈Finiteness.rootTemporalSignatures root,
      4*(temporalOriginCap sig.2.1+2)≤(SlotFrame.familySlots τ sig.1 sig.2.1 sig.2.2).card) :
    ∃(_C : ResolvedCertificate N F) (e : Clock≃Clock),
      (∀c∈(Section3.TransitionForm.ofState N).allClocks,e c=incoming c) ∧
      F.holds σ P α k ∧
      FiniteInventory.TransitionWithin
        (FiniteInventory.locals (Finiteness.rootPlainFormulas root) τ)
        (FiniteInventory.guards τ) (FiniteInventory.resets τ) (renameTransition e F) ∧
      ∀M,F.nextPart=some M → Nonempty (SlotFrame τ M e) := by
  classical
  have hBelow := T.ledger_sources_below root hN hInput hFacts.1 hFacts.2.1
  obtain ⟨newSlot,hnew,hprops⟩ := frame.exists_opening_slots root capacity
  have hFamily := fun sig=>(hprops sig).1
  have hfree := fun sig=>(hprops sig).2
  obtain ⟨e,he,hagree⟩ := T.exists_role_permutation O root hBelow hInput hLocal frame newSlot hFamily hnew hfree hτ
  let C : ResolvedCertificate N F := ⟨J,H,Er,T.realize,hInput,hFacts.1,hFacts.2.1⟩
  have hFormulas := T.realize.normalized_formulas_below hInput hFacts.1 root hN
  have ht := T.retrospective_transition_typed O root hBelow hInput hLocal hEmpty hFacts frame newSlot hFamily hnew hfree
  refine ⟨C,e,hagree,hFacts.2.2.1,?_,?_⟩
  · apply ht.rename_within (Finiteness.rootPlainFormulas root) e he
    · intro φ hφ
      exact Finiteness.subformula_mem_rootPlainFormulas (hFormulas.1 (.predicate (.plain φ)) hφ)
    · intro M hn φ hφ
      exact Finiteness.subformula_mem_rootPlainFormulas (hFormulas.2 M hn (.predicate (.plain φ)) hφ)
  · intro M hn
    exact ⟨T.successorSlotFrame O root hBelow hInput hLocal hEmpty hFacts frame newSlot hFamily hnew hfree e he hn⟩

omit [Fintype Slot] in
/-- The actual fixed root palette supplies capacity and injectivity; there is
 no slot-allocation, representative, or cardinal premise in this corollary. -/
theorem SelectedTree.exists_root_typed_extension [Infinite Clock]
    (O : InputOrigins σ P α k N)
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (root : Formula Var) (hN : Finiteness.StateFormulasBelow root N)
    (hInput : SafeNormalization J (.ofState N)) (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (hEmpty : owned.nextInputs=[])
    {A : Set Clock} {F : Section3.TransitionForm Clock Var}
    (hFacts : SelectedOutputFacts owned A O.strictClocks σ P α k H Er F)
    (frame : SlotFrame (rootSlotTriples (Clock := Clock) root) N incoming) :
    ∃(_C : ResolvedCertificate N F) (e : Clock≃Clock),
      (∀c∈(Section3.TransitionForm.ofState N).allClocks,e c=incoming c) ∧
      F.holds σ P α k ∧
      FiniteInventory.TransitionWithin
        (FiniteInventory.locals (Finiteness.rootPlainFormulas root) (rootSlotTriples (Clock := Clock) root))
        (FiniteInventory.guards (rootSlotTriples (Clock := Clock) root))
        (FiniteInventory.resets (rootSlotTriples (Clock := Clock) root)) (renameTransition e F) ∧
      ∀M,F.nextPart=some M → Nonempty (SlotFrame (rootSlotTriples (Clock := Clock) root) M e) := by
  apply T.exists_typed_slot_extension O root hN hInput hLocal hEmpty hFacts frame (rootSlot_clockAt_injective root)
  intro sig hs
  rw [rootSlot_family_card root sig.1 sig.2.1 sig.2.2 hs]

end STLTableau.Section4.Finiteness
