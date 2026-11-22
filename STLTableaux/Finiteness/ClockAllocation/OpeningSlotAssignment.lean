import STLTableaux.Finiteness.Inventory.RootSlotPalette

/-! Chooses an unoccupied slot for each timed subformula of the root, including
subformulas that do not open in the current step. -/
namespace STLTableau.Section4.Finiteness
variable {Clock Var Slot : Type*} [Fintype Slot]

namespace SlotFrame

def slotFamily (τ : Slot→FiniteInventory.Triple Clock Var) (s : Slot) :
    TemporalKind×TimeInterval×Formula Var :=
  ((τ s).kind,(τ s).interval,(τ s).body)

/-- The frame's actual occupied-family bound leaves a vacant target slot in
each root family. Matching families automatically make these choices injective. -/
theorem exists_opening_slots
    {τ : Slot→FiniteInventory.Triple Clock Var} {N : Section3.StateForm Clock Var}
    {incoming : Equiv.Perm Clock} (frame : SlotFrame τ N incoming) (root : Formula Var)
    (capacity : ∀s∈Finiteness.rootTemporalSignatures root,
      4*(temporalOriginCap s.2.1+2)≤(familySlots τ s.1 s.2.1 s.2.2).card) :
    ∃newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot,
      Function.Injective newSlot ∧
      ∀s,slotFamily τ (newSlot s)=s.val ∧newSlot s∉occupied frame.role := by
  classical
  have hv : ∀s : ↥(Finiteness.rootTemporalSignatures root),
      ∃a,slotFamily τ a=s.val ∧a∉occupied frame.role := by
    intro s
    obtain ⟨a,hk,hI,hφ,ha⟩ := exists_vacant_family_slot_of_bound τ frame.role
      s.val.1 s.val.2.1 s.val.2.2 (temporalOriginCap s.val.2.1+2)
      (frame.occupied_bound _ _ _) (by have h:=capacity s.val s.property;omega)
    exact ⟨a,by simp [slotFamily,hk,hI,hφ],ha⟩
  choose newSlot hnew using hv
  refine ⟨newSlot,?_,hnew⟩
  intro s t he
  apply Subtype.ext
  exact (hnew s).1.symm.trans ((congrArg (slotFamily τ) he).trans (hnew t).1)

end SlotFrame

/-- The concrete root palette supplies the required capacity without any
nonempty-slot assumption or cardinal premise on a representative. -/
theorem rootPalette_exists_opening_slots [Infinite Clock]
    (root : Formula Var) {N : Section3.StateForm Clock Var} {incoming : Equiv.Perm Clock}
    (frame : SlotFrame (rootSlotTriples (Clock := Clock) root) N incoming) :
    ∃newSlot : ↥(Finiteness.rootTemporalSignatures root)→RootSlot root,
      Function.Injective newSlot ∧
      ∀s,SlotFrame.slotFamily (rootSlotTriples (Clock := Clock) root) (newSlot s)=s.val ∧
        newSlot s∉SlotFrame.occupied frame.role := by
  apply frame.exists_opening_slots root
  intro s hs
  rw [rootSlot_family_card root s.1 s.2.1 s.2.2 hs]

end STLTableau.Section4.Finiteness
