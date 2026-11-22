import STLTableaux.Finiteness.ClockAllocation.SelectedRoleAllocation
import STLTableaux.Finiteness.ClockAllocation.RoleAllocationPermutation

/-! Realization of the actually constructed retrospective role injection.
 The incoming interface is preserved on whole actual input support; absent
 ghost names and unused freshness witnesses impose no constraints. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var Slot : Type*} [DecidableEq Clock] [Fintype Slot]
variable {N : Section3.StateForm Clock Var} {J : MixedJ Clock Var} {W : Set Clock}
    {owned : OwnedPending J N.resets W} {H Er : MixedJ Clock Var}
    {τ : Slot→FiniteInventory.Triple Clock Var} {incoming : Clock≃Clock}
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}

private theorem allocation_domain_finite
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    (T : SelectedTree E U owned H Er) :
    ((Section3.TransitionForm.ofState N).allClocks ∪ {c|c∈T.usedFreshClocks}).Finite := by
  classical
  apply (Section3.TransitionForm.ofState N).allClocks_finite.union
  have he : {c|c∈T.usedFreshClocks}=(T.usedFreshClocks.toFinset : Set Clock) := by ext c; simp
  rw [he]
  exact Finset.finite_toSet _

/-- The role-map domain contains every clock of the normalized output. -/
theorem SelectedTree.role_domain_covers_output
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    (T : SelectedTree E U owned H Er) (hInput : SafeNormalization J (.ofState N))
    {F : Section3.TransitionForm Clock Var} (hFull : SafeNormalization H F) :
    F.allClocks⊆(Section3.TransitionForm.ofState N).allClocks ∪ {c|c∈T.usedFreshClocks} := by
  have hs := T.used_normalized_clock_support hFull
  rwa [input_clock_support_of_safe hInput] at hs

/-- Actual selected-tree roles extend to a global permutation that preserves
 the supplied incoming interface on all supported input clock names. -/
theorem SelectedTree.exists_role_permutation
    (O : InputOrigins σ P α k N)
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (root : Formula Var) (hBelow : ∀entry∈T.rawLedger,entry.source.formula≼root)
    (hInput : SafeNormalization J (.ofState N)) (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (frame : SlotFrame τ N incoming)
    (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot)
    (hFamily : ∀sig,SlotFrame.slotFamily τ (newSlot sig)=sig.val)
    (hnew : Function.Injective newSlot)
    (hfree : ∀sig,newSlot sig∉SlotFrame.occupied frame.role)
    (hτ : Function.Injective (fun p : Slot×Fin 3=>FiniteInventory.clockAt (τ p.1) p.2)) :
    ∃e : Clock≃Clock,
      (∀c s r,retrospectiveRoleMap root T frame newSlot c=some (s,r) →
        e c=FiniteInventory.clockAt (τ s) r) ∧
      ∀c∈(Section3.TransitionForm.ofState N).allClocks,e c=incoming c := by
  let roles := T.roleAllocation O root hBelow hInput hLocal frame newSlot hFamily hnew hfree
  apply roles.exists_permutation_agree (allocation_domain_finite T) τ hτ Set.subset_union_left incoming
  intro c hc s r hr
  obtain ⟨oldS,oldR,hOld⟩ := (frame.domain c).1 hc
  have hOldMap : roles.role c=some (oldS,oldR) :=
    retrospectiveRoleMap_input root T hInput frame newSlot hOld
  have hpair := Option.some.inj (hOldMap.symm.trans hr)
  exact (frame.realizes c oldS oldR hOld).trans
    (congrArg (fun p : Slot×Fin 3=>FiniteInventory.clockAt (τ p.1) p.2) hpair)

end STLTableau.Section4.Finiteness
