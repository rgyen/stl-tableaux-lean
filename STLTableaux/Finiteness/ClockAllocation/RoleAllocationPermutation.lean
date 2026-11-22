import STLTableaux.Finiteness.ClockAllocation.SlotFrame
import Mathlib.Logic.Equiv.Fintype

/-! Extends a clock assignment on a finite support to a permutation of clock
names. Only names in the support have prescribed images. -/
namespace STLTableau.Section4.Finiteness
variable {Clock Var Slot : Type*}

/-- An actual partial role injection determines a finite support injection into
an injective fixed slot palette, hence extends to a permutation of Clock. -/
theorem RoleAllocation.exists_permutation
    {A : Set Clock} (roles : RoleAllocation (Slot := Slot) A) (hA : A.Finite)
    (τ : Slot → FiniteInventory.Triple Clock Var)
    (hτ : Function.Injective (fun p : Slot × Fin 3=>FiniteInventory.clockAt (τ p.1) p.2)) :
    ∃e : Equiv.Perm Clock,∀c s r,roles.role c=some (s,r) →
      e c=FiniteInventory.clockAt (τ s) r := by
  classical
  letI := hA.fintype
  have hp (c : A) : ∃p : Slot × Fin 3,roles.role c.val=some p := by
    obtain ⟨s,r,hr⟩ := (roles.domain c.val).1 c.property
    exact ⟨(s,r),hr⟩
  choose p hp using hp
  let target : A → Clock := fun c=>FiniteInventory.clockAt (τ (p c).1) (p c).2
  have ht : Function.Injective target := by
    intro c d h
    have he : p c=p d := hτ h
    apply Subtype.ext
    rcases hx : p c with ⟨s,r⟩
    apply roles.injective c.val d.val s r
    · simpa only [hx] using hp c
    · simpa only [←he,hx] using hp d
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair (fun c : A=>c.val) target Subtype.val_injective ht
  refine ⟨e,?_⟩
  intro c s r hc
  have hca : c∈A := (roles.domain c).2 ⟨s,r,hc⟩
  have hpair : p ⟨c,hca⟩=(s,r) := Option.some.inj ((hp ⟨c,hca⟩).symm.trans hc)
  simpa only [target,hpair] using he ⟨c,hca⟩

/-- The same permutation automatically preserves an existing incoming
assignment on its ACTUAL supported interface. No condition is put on ghost names. -/
theorem RoleAllocation.exists_permutation_agree
    {A B : Set Clock} (roles : RoleAllocation (Slot := Slot) A) (hA : A.Finite)
    (τ : Slot → FiniteInventory.Triple Clock Var)
    (hτ : Function.Injective (fun p : Slot × Fin 3=>FiniteInventory.clockAt (τ p.1) p.2))
    (hBA : B⊆A) (e0 : Equiv.Perm Clock)
    (h0 : ∀c∈B,∀s r,roles.role c=some (s,r) → e0 c=FiniteInventory.clockAt (τ s) r) :
    ∃e : Equiv.Perm Clock,
      (∀c s r,roles.role c=some (s,r) → e c=FiniteInventory.clockAt (τ s) r) ∧
      ∀c∈B,e c=e0 c := by
  obtain ⟨e,he⟩ := roles.exists_permutation hA τ hτ
  refine ⟨e,he,?_⟩
  intro c hc
  obtain ⟨s,r,hr⟩ := (roles.domain c).1 (hBA hc)
  exact (he c s r hr).trans (h0 c hc s r hr).symm

namespace SlotFrame
variable [Fintype Slot]

noncomputable def familySlots (τ : Slot → FiniteInventory.Triple Clock Var)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) : Finset Slot := by
  classical
  exact Finset.univ.filter (fun s=>(τ s).kind=kind ∧ (τ s).interval=I ∧ (τ s).body=φ)

/-- Strictly fewer occupied owners than actual family slots yields an actual
vacant slot of that family. Equal capacity alone is deliberately insufficient. -/
theorem exists_vacant_family_slot
    (τ : Slot → FiniteInventory.Triple Clock Var) (role : ClockRoles Clock Slot)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (h : (occupiedFamily τ role kind I φ).card < (familySlots τ kind I φ).card) :
    ∃s,(τ s).kind=kind ∧ (τ s).interval=I ∧ (τ s).body=φ ∧ s∉occupied role := by
  classical
  by_contra hn
  have hsub : familySlots τ kind I φ ⊆ occupiedFamily τ role kind I φ := by
    intro s hs
    have hf : (τ s).kind=kind ∧ (τ s).interval=I ∧ (τ s).body=φ := (Finset.mem_filter.1 hs).2
    have ho : s∈occupied role := by
      by_contra ho
      exact hn ⟨s,hf.1,hf.2.1,hf.2.2,ho⟩
    exact Finset.mem_filter.2 ⟨ho,hf⟩
  exact (Nat.not_lt_of_ge (Finset.card_le_card hsub)) h

/-- A numeric occupied-owner bound suffices when the actual palette family has
strictly greater capacity. This is a local finite-set fact, not an owner bound. -/
theorem exists_vacant_family_slot_of_bound
    (τ : Slot → FiniteInventory.Triple Clock Var) (role : ClockRoles Clock Slot)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) (K : ℕ)
    (hb : (occupiedFamily τ role kind I φ).card ≤ K)
    (hc : K < (familySlots τ kind I φ).card) :
    ∃s,(τ s).kind=kind ∧ (τ s).interval=I ∧ (τ s).body=φ ∧ s∉occupied role :=
  exists_vacant_family_slot τ role kind I φ (hb.trans_lt hc)
/-- The fourfold family supply leaves strict vacancy even after
reserving both an old-owner budget and one full new-owner budget. -/
theorem exists_vacant_family_slot_fourfold
    (τ : Slot → FiniteInventory.Triple Clock Var) (role : ClockRoles Clock Slot)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hb : (occupiedFamily τ role kind I φ).card ≤ 2*(temporalOriginCap I+2))
    (hc : 4*(temporalOriginCap I+2) ≤ (familySlots τ kind I φ).card) :
    ∃s,(τ s).kind=kind ∧ (τ s).interval=I ∧ (τ s).body=φ ∧ s∉occupied role := by
  apply exists_vacant_family_slot τ role kind I φ
  omega

end SlotFrame
end STLTableau.Section4.Finiteness
