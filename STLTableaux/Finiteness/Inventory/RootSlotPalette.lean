import STLTableaux.Finiteness.ClockAllocation.RoleAllocationPermutation
import STLTableaux.Finiteness.Bounds.SelectedResolutionBudget
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators

/-! Reserves a finite collection of slots for each timed subformula of the
root, with three distinct clock names per slot. Used in the proof of
Theorem 4.37. -/
namespace STLTableau.Section4.Finiteness
open scoped BigOperators
variable {Clock Var : Type*}

abbrev RootSlot (root : Formula Var) :=
  Σs : ↥(Finiteness.rootTemporalSignatures root), Fin (4*(temporalOriginCap s.val.2.1+2))

noncomputable def rootSlotClock [Infinite Clock] (root : Formula Var) :
    (RootSlot root × Fin 3) ↪ Clock := by
  classical
  let a := Fintype.equivFin (RootSlot root × Fin 3)
  exact ⟨fun x=>Infinite.natEmbedding Clock (a x).val,
    (Infinite.natEmbedding Clock).injective.comp (Fin.val_injective.comp a.injective)⟩

noncomputable def rootSlotTriples [Infinite Clock] (root : Formula Var) :
    RootSlot root → FiniteInventory.Triple Clock Var := fun s=>
  ⟨rootSlotClock root (s,0),rootSlotClock root (s,1),rootSlotClock root (s,2),
    s.1.val.1,s.1.val.2.1,s.1.val.2.2⟩

theorem rootSlot_clockAt [Infinite Clock] (root : Formula Var) (s : RootSlot root) (r : Fin 3) :
    FiniteInventory.clockAt (rootSlotTriples (Clock := Clock) root s) r=rootSlotClock root (s,r) := by
  fin_cases r <;> simp [FiniteInventory.clockAt,rootSlotTriples]

theorem rootSlot_clockAt_injective [Infinite Clock] (root : Formula Var) :
    Function.Injective (fun p : RootSlot root × Fin 3=>
      FiniteInventory.clockAt (rootSlotTriples (Clock := Clock) root p.1) p.2) := by
  simpa only [rootSlot_clockAt] using (rootSlotClock (Clock := Clock) root).injective

/-- The slot count for a timed subformula is `4 * (K + 2)`, where `K`
bounds the number of tracked truth intervals. -/
theorem rootSlot_family_card [Infinite Clock] (root : Formula Var)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hs : (kind,I,φ)∈Finiteness.rootTemporalSignatures root) :
    (SlotFrame.familySlots (rootSlotTriples (Clock := Clock) root) kind I φ).card=
      4*(temporalOriginCap I+2) := by
  classical
  let s : ↥(Finiteness.rootTemporalSignatures root) := ⟨(kind,I,φ),hs⟩
  have he : (fun x : RootSlot root=>(rootSlotTriples (Clock := Clock) root x).kind=kind ∧
      (rootSlotTriples (Clock := Clock) root x).interval=I ∧ (rootSlotTriples (Clock := Clock) root x).body=φ) =
      (fun x=>x.1=s) := by
    funext x
    apply propext
    change x.1.val.1=kind ∧ x.1.val.2.1=I ∧ x.1.val.2.2=φ ↔ x.1=s
    rw [Subtype.ext_iff]
    dsimp [s]
    cases hx : x.1.val with
    | mk k tail => cases tail; simp
  unfold SlotFrame.familySlots
  have hf : Finset.univ.filter (fun x : RootSlot root=>
      (rootSlotTriples (Clock := Clock) root x).kind=kind ∧
      (rootSlotTriples (Clock := Clock) root x).interval=I ∧
      (rootSlotTriples (Clock := Clock) root x).body=φ) =
      Finset.univ.filter (fun x=>x.1=s) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact iff_of_eq (congrFun he x)
  rw [hf,←Fintype.card_subtype]
  rw [Fintype.card_congr (Equiv.sigmaSubtype s)]
  simp [s]

theorem rootSlot_card (root : Formula Var) :
    Fintype.card (RootSlot root)=
      4*∑s∈Finiteness.rootTemporalSignatures root,(temporalOriginCap s.2.1+2) := by
  classical
  change Fintype.card (Σs : ↥(Finiteness.rootTemporalSignatures root),
    Fin (4*(temporalOriginCap s.val.2.1+2))) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Finset.sum_coe_sort (Finiteness.rootTemporalSignatures root)
    (fun s=>4*(temporalOriginCap s.2.1+2))]
  exact (Finset.mul_sum _ _ _).symm

theorem rootSlot_card_budget (root : Formula Var) :
    Fintype.card (RootSlot root)=4*rootOriginBudget root+8*(Finiteness.rootTemporalSignatures root).card := by
  rw [rootSlot_card,Finset.sum_add_distrib]
  simp only [Finset.sum_const,smul_eq_mul]
  unfold rootOriginBudget
  ring

theorem rootSlot_card_le_resolution (root : Formula Var) :
    Fintype.card (RootSlot root)≤44*(Finiteness.rootPlainFormulas root).card*Finiteness.formulaResolution root := by
  have hb := root_origin_budget_le_nine_inventory_resolution root
  have hm := Finiteness.root_temporal_signatures_card_le_plain root
  have hr := Finiteness.formula_resolution_pos root
  have hn := Nat.mul_le_mul_left (Finiteness.rootPlainFormulas root).card hr
  rw [rootSlot_card_budget]
  nlinarith

theorem rootSlot_card_le_size_resolution (root : Formula Var) :
    Fintype.card (RootSlot root)≤44*literalFormulaSize root*Finiteness.formulaResolution root :=
  (rootSlot_card_le_resolution root).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 44 (root_inventory_card_le_literal_size root)))

theorem rootSlot_clocks_card_le_resolution [Infinite Clock] (root : Formula Var) :
    (FiniteInventory.clocks (rootSlotTriples (Clock := Clock) root)).card≤
      132*literalFormulaSize root*Finiteness.formulaResolution root := by
  have hc := FiniteInventory.clocks_card_le (rootSlotTriples (Clock := Clock) root)
  have hs := rootSlot_card_le_size_resolution root
  nlinarith

/-- Explicit sparse-state exponent arithmetic for this actual palette. -/
theorem rootSlot_sparse_exponent_le_resolution (root : Formula Var) :
    2*((Finiteness.rootPlainFormulas root).card+3+64*Fintype.card (RootSlot root))+1≤
      5634*literalFormulaSize root*Finiteness.formulaResolution root+7 := by
  have hs := rootSlot_card_le_size_resolution root
  have hn := root_inventory_card_le_literal_size root
  have hr := Finiteness.formula_resolution_pos root
  have hn' := Nat.mul_le_mul_left (literalFormulaSize root) hr
  nlinarith
end STLTableau.Section4.Finiteness
