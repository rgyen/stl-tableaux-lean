import STLTableaux.Finiteness.Bounds.SelectedRetainedCount
import STLTableaux.Finiteness.Bounds.SelectedRootBudget

/-! Actual per-family selected branch occurrences, for finite slot reservation.
These counts refer to the same raw ledger, not arbitrary retained witnesses. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

noncomputable def boundedFamilyLedger
    (L : List (RawLedgerEntry (Clock := Clock) (Var := Var)))
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) : List (Predicate Clock Var) := by
  classical
  exact (L.filterMap RawLedgerEntry.boundedSource).filter
    (fun p=>∃c d m r,p=.bounded c d m r kind I φ)

noncomputable def upperFamilyLedger
    (L : List (RawLedgerEntry (Clock := Clock) (Var := Var)))
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) : List (Formula Var) := by
  classical
  exact (L.filterMap RawLedgerEntry.upperFormula).filter (·=timedFormula kind I φ)

noncomputable def plainOpeningLedger
    (L : List (RawLedgerEntry (Clock := Clock) (Var := Var)))
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) : List (Formula Var) := by
  classical
  exact (L.filterMap RawLedgerEntry.plainFormula).filter (·=timedFormula kind I φ)

private theorem equal_filter_length_le_one {α : Type*} [DecidableEq α] (L : List α) (a : α) (hn : L.Nodup) :
    (L.filter (fun b=>decide (b=a))).length≤1 := by
  classical
  have hnd := hn.filter (fun b=>decide (b=a))
  have hs : (L.filter (fun b=>decide (b=a))).toFinset⊆{a} := by
    intro b hb
    have h := List.mem_filter.mp (List.mem_toFinset.mp hb)
    simpa using h.2
  have hc := Finset.card_le_card hs
  simpa only [List.toFinset_card_of_nodup hnd,Finset.card_singleton] using hc

variable {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}
    {N : Section3.StateForm Clock Var}

theorem SelectedTree.bounded_family_ledger_le_input
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    (boundedFamilyLedger T.rawLedger kind I φ).length≤(boundedFamily N kind I φ).card := by
  classical
  let L := boundedFamilyLedger T.rawLedger kind I φ
  have hn : L.Nodup := T.bounded_ledger_nodup.filter _
  have hm : ∀p∈L,∃q : BoundedLocal N,q.val=p ∧q∈boundedFamily N kind I φ := by
    intro p hp
    obtain ⟨hp,hs⟩ := List.mem_filter.mp hp
    obtain ⟨c,d,m,r,hs⟩ : ∃c d m r,p=.bounded c d m r kind I φ := by simpa using hs
    obtain ⟨e,he,hp⟩ := List.mem_filterMap.mp hp
    have heq : e.source=p := by
      cases ht : e.source with
      | plain | upper => simp [RawLedgerEntry.boundedSource,ht] at hp
      | bounded c' d' m' r' kind' I' φ' => simpa [RawLedgerEntry.boundedSource,ht] using hp
    have hb : IsBoundedPredicate e.source := by rw [heq,hs]; trivial
    let q : BoundedLocal N := ⟨p,(hLocal _).1 (heq ▸ T.bounded_ledger_origin he hb),by rw [hs];trivial⟩
    exact ⟨q,rfl,(mem_boundedFamily _ _ _ _ _).2 ⟨c,d,m,r,hs⟩⟩
  let f : {p : Predicate Clock Var // p∈L.toFinset}→{q : BoundedLocal N // q∈boundedFamily N kind I φ} :=
    fun p=>⟨(hm p.val (List.mem_toFinset.mp p.property)).choose,
      (hm p.val (List.mem_toFinset.mp p.property)).choose_spec.2⟩
  have hf : ∀p,(f p).val.val=p.val := fun p=>(hm p.val (List.mem_toFinset.mp p.property)).choose_spec.1
  have hi : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    exact (hf p).symm.trans ((congrArg (fun z=>z.val.val) he).trans (hf q))
  have hc := Fintype.card_le_of_injective f hi
  have hc' : L.toFinset.card≤(boundedFamily N kind I φ).card := by
    simpa only [Fintype.card_coe] using hc
  simpa only [List.toFinset_card_of_nodup hn] using hc'

theorem SelectedTree.upper_family_ledger_le_one
    (O : InputOrigins σ P α k N)
    {J : MixedJ Clock Var} {W : Set Clock} {owned : OwnedPending J N.resets W}
    {H Er : MixedJ Clock Var} (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    (upperFamilyLedger T.rawLedger kind I φ).length≤1 := by
  classical
  exact equal_filter_length_le_one _ _ (T.upper_ledger_formulas_nodup
    (fun p hp q hq he=>O.eligible_unique_formula hp hq he)
    (fun c m kind I φ hm=>O.no_upper c m kind I φ ((hLocal _).1 hm)))

theorem SelectedTree.plain_opening_ledger_le_one
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    (plainOpeningLedger T.rawLedger kind I φ).length≤1 := by
  classical
  exact equal_filter_length_le_one _ _ (T.plainConsumed_nodup.sublist T.plain_ledger_sublist)

theorem SelectedTree.family_ledger_bounds
    (O : InputOrigins σ P α k N)
    {J : MixedJ Clock Var} {W : Set Clock} {owned : OwnedPending J N.resets W}
    {H Er : MixedJ Clock Var} (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    (boundedFamilyLedger T.rawLedger kind I φ).length+
      (upperFamilyLedger T.rawLedger kind I φ).length≤temporalOriginCap I+1 ∧
    (boundedFamilyLedger T.rawLedger kind I φ).length+
      (upperFamilyLedger T.rawLedger kind I φ).length+
      (plainOpeningLedger T.rawLedger kind I φ).length≤temporalOriginCap I+2 := by
  have hb := T.bounded_family_ledger_le_input hLocal kind I φ
  have hu := T.upper_family_ledger_le_one O hLocal kind I φ
  have hp := T.plain_opening_ledger_le_one kind I φ
  have hc : (boundedFamily N kind I φ).card≤temporalOriginCap I := by
    cases I with
    | bounded I => exact O.boundedFamily_card_floor_bound kind I φ
    | unbounded a => exact O.unboundedFamily_card_le_one kind a φ
  omega

end STLTableau.Section4.Finiteness
