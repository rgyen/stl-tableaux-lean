import STLTableaux.Finiteness.Bounds.SelectedRetainedCount
import STLTableaux.Finiteness.ClockAllocation.RoleAllocationPermutation

/-! Actual successor-owner counts from SAME-family clocked ledger events.
Guard-only next finishes are covered: no bounded-next-local premise is used. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var Slot : Type*} [DecidableEq Clock]

noncomputable def upperFamilyEvents (L : List (RawLedgerEntry (Clock := Clock) (Var := Var)))
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) : Finset (RawLedgerEntry (Clock := Clock) (Var := Var)) := by
  classical
  exact L.toFinset.filter (fun e=>∃c m,e.source=.upper c m kind I φ)

noncomputable def boundedFamilyEvents (L : List (RawLedgerEntry (Clock := Clock) (Var := Var)))
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) : Finset (RawLedgerEntry (Clock := Clock) (Var := Var)) := by
  classical
  exact L.toFinset.filter (fun e=>∃c d m r,e.source=.bounded c d m r kind I φ)

variable {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
  {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}
  {N : Section3.StateForm Clock Var} (O : InputOrigins σ P α k N)
  {J : MixedJ Clock Var} {W : Set Clock} {owned : OwnedPending J N.resets W}
  {H Er : MixedJ Clock Var}

theorem SelectedTree.upperFamilyEvents_card_le_one
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    (upperFamilyEvents T.rawLedger kind I φ).card≤1 := by
  classical
  apply Finset.card_le_one.mpr
  intro e he f hf
  obtain ⟨he,c,m,hs⟩ := Finset.mem_filter.mp he
  obtain ⟨hf,d,r,ht⟩ := Finset.mem_filter.mp hf
  apply LedgerList.filterMap_fiber_unique RawLedgerEntry.upperFormula T.rawLedger
    (T.upper_ledger_formulas_nodup (fun p hp q hq he=>O.eligible_unique_formula hp hq he)
      (fun c m kind I φ hm=>O.no_upper c m kind I φ ((hLocal _).1 hm)))
    (List.mem_toFinset.mp he) (List.mem_toFinset.mp hf) (v:=timedFormula kind I φ)
  · simp [RawLedgerEntry.upperFormula,hs]
  · simp [RawLedgerEntry.upperFormula,ht]

theorem SelectedTree.boundedFamilyEvents_card_le
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    (boundedFamilyEvents T.rawLedger kind I φ).card≤(boundedFamily N kind I φ).card := by
  classical
  let A := boundedFamilyEvents T.rawLedger kind I φ
  have hm (e : A) : ∃q : ↥(boundedFamily N kind I φ),q.val.val=e.val.source := by
    obtain ⟨he,c,d,m,r,hs⟩ := Finset.mem_filter.mp e.property
    have hb : IsBoundedPredicate e.val.source := by rw [hs];trivial
    have hp : Local.predicate e.val.source∈N.locals := (hLocal _).1 (T.bounded_ledger_origin (List.mem_toFinset.mp he) hb)
    exact ⟨⟨⟨e.val.source,hp,hb⟩,(mem_boundedFamily _ _ _ _ _).2 ⟨c,d,m,r,hs⟩⟩,rfl⟩
  choose f hf using hm
  have hi : Function.Injective f := by
    intro e g h
    apply Subtype.ext
    have hs : e.val.source=g.val.source := (hf e).symm.trans ((congrArg (fun q : ↥(boundedFamily N kind I φ)=>q.val.val) h).trans (hf g))
    obtain ⟨he,c,d,m,r,hsrc⟩ := Finset.mem_filter.mp e.property
    obtain ⟨hg,_,_,_,_,_⟩ := Finset.mem_filter.mp g.property
    apply LedgerList.filterMap_fiber_unique RawLedgerEntry.boundedSource T.rawLedger T.bounded_ledger_nodup
      (List.mem_toFinset.mp he) (List.mem_toFinset.mp hg) (v:=e.val.source)
    · simp [RawLedgerEntry.boundedSource,hsrc]
    · simp only [RawLedgerEntry.boundedSource]
      rw [←hs,hsrc]
  have hc := Fintype.card_le_of_injective f hi
  rw [Fintype.card_coe,Fintype.card_coe] at hc
  exact hc

/-- Every occupied successor slot is covered by one ACTUAL same-family clocked
ledger event; an event has one owner. This includes guard-only descendants.
The actual cover is a separate provenance proof, never an origin-count field. -/
theorem SelectedTree.successor_occupiedFamily_card_le [Fintype Slot]
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (τ : Slot→FiniteInventory.Triple Clock Var) (role : ClockRoles Clock Slot)
    (owner : RawLedgerEntry (Clock := Clock) (Var := Var)→Option Slot)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hcover : ∀s∈SlotFrame.occupiedFamily τ role kind I φ,
      ∃e∈T.rawLedger,owner e=some s ∧
        ((∃c m,e.source=.upper c m kind I φ) ∨
          (∃c d m r,e.source=.bounded c d m r kind I φ))) :
    (SlotFrame.occupiedFamily τ role kind I φ).card≤temporalOriginCap I+1 := by
  classical
  let A := upperFamilyEvents T.rawLedger kind I φ
  let B := boundedFamilyEvents T.rawLedger kind I φ
  have hsub : (SlotFrame.occupiedFamily τ role kind I φ).image some⊆(A∪B).image owner := by
    intro v hv
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨e,he,ho,hfam⟩ := hcover s hs
    refine Finset.mem_image.mpr ⟨e,?_,ho⟩
    rcases hfam with hu | hb
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr he,hu⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr he,hb⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_image_le)
  rw [Finset.card_image_of_injective _ (Option.some_injective Slot)] at hc
  have hu := T.upperFamilyEvents_card_le_one O hLocal kind I φ
  have hb := T.boundedFamilyEvents_card_le O hLocal kind I φ
  have hsum := Finset.card_union_le A B
  have hcap : (boundedFamily N kind I φ).card≤temporalOriginCap I := by
    cases I with
    | bounded I => exact O.boundedFamily_card_floor_bound kind I φ
    | unbounded a => exact O.unboundedFamily_card_le_one kind a φ
  change A.card≤1 at hu
  change B.card≤(boundedFamily N kind I φ).card at hb
  omega
end STLTableau.Section4.Finiteness
