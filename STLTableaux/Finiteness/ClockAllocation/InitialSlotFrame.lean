import STLTableaux.Finiteness.ClockAllocation.SlotFrame
import STLTableaux.Finiteness.Derivation.Selection.SelectedClockSupport
import STLTableaux.Finiteness.Derivation.Selection.SelectedInitialCompletion

/-! The initial predicate `[φ]` has no clock roles. Timed openings allocate
roles to their new clocks. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var Slot : Type*} [Fintype Slot]

/-- The actual root has no supported clocks; every role is absent, even when
the target slot type is empty. -/
noncomputable def plain_initial_slot_frame
    (τ : Slot → FiniteInventory.Triple Clock Var) (root : Formula Var)
    (incoming : Equiv.Perm Clock) : SlotFrame τ (plainInitialState (Clock := Clock) root) incoming := by
  classical
  have hEmpty : (Section3.TransitionForm.ofState (plainInitialState (Clock := Clock) root)).allClocks=∅ :=
    (SafeNormalization.predicate (Predicate.plain root)).allClocks_eq_syntax
  refine ⟨⟨(fun _=>none),?_,?_⟩,?_,?_,?_,?_,?_,?_⟩
  · intro c
    rw [hEmpty]
    simp
  · intro c d s r h
    cases h
  · intro c s r h
    cases h
  · intro p hp
    have he : p=.plain root := by
      simpa only [plainInitialState,Section3.StateForm.ofLocal,Set.mem_singleton_iff,
        Local.predicate.injEq] using hp
    subst p
    trivial
  · intro g hg
    change g∈(∅ : Set (Guard Clock)) at hg
    exact hg.elim
  · intro c a hc
    change (none : Option NNReal)=some a at hc
    cases hc
  · intro s h
    obtain ⟨⟨c,hc⟩,_⟩ := h
    cases hc
  · intro kind I φ
    have he : SlotFrame.occupiedFamily τ (fun _ : Clock=>none) kind I φ=∅ := by
      ext s
      simp [SlotFrame.occupiedFamily,SlotFrame.occupied]
    rw [he,Finset.card_empty]
    omega
end STLTableau.Section4.Finiteness
