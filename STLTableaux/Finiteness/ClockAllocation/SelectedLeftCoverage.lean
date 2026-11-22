import STLTableaux.Finiteness.ClockAllocation.SelectedRoleMap
import STLTableaux.Finiteness.Derivation.ResolveSubformula

/-! Existence and family correctness of retrospective left owners, derived
from actual incoming predicates or actual opening producers of the SAME tree. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var Slot : Type*} [DecidableEq Clock] [Fintype Slot]
variable {E : Set (Predicate Clock Var)} {U : Set Clock}
    {N : Section3.StateForm Clock Var} {J : MixedJ Clock Var} {W : Set Clock}
    {owned : OwnedPending J N.resets W} {H Er : MixedJ Clock Var}

/-- Literal source confinement follows from this actual resolved output. -/
theorem SelectedTree.ledger_sources_below
    (T : SelectedTree E U owned H Er) (root : Formula Var)
    (hN : Finiteness.StateFormulasBelow root N)
    (hInput : SafeNormalization J (.ofState N))
    {F : Section3.TransitionForm Clock Var} (hFull : SafeNormalization H F)
    (_hErased : SafeNormalization Er F.atomicProjection) :
    ∀e∈T.rawLedger,e.source.formula≼root := by
  intro e he
  exact (T.realize.normalized_formulas_below hInput hFull root hN).1 (.predicate e.source)
    ((T.normalized_retained_nonatomic_iff hFull e.source e.actual.source_nonatomic).2 ⟨e,he,rfl⟩)

/-- An actual timed opening whose source is below the root has an actual root
signature; no ownership or representative premise is used. -/
theorem SelectedTree.opening_signature_mem
    (T : SelectedTree E U owned H Er) (root : Formula Var)
    (hBelow : ∀e∈T.rawLedger,e.source.formula≼root)
    {e : RawLedgerEntry (Clock := Clock) (Var := Var)} (he : e∈T.rawLedger)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hs : e.source=.plain (timedFormula kind I φ)) :
    (kind,I,φ)∈Finiteness.rootTemporalSignatures root := by
  have hf := hBelow e he
  rw [hs] at hf
  apply (Finiteness.mem_rootTemporalSignatures_iff root kind I φ).2
  cases kind <;> simpa [Predicate.formula,timedFormula,Finiteness.temporalSignatureFormula] using hf

/-- Construct a left-owner witness for an actual opening producer. -/
theorem SelectedTree.opening_left_coverage
    (T : SelectedTree E U owned H Er) (root : Formula Var)
    (hBelow : ∀e∈T.rawLedger,e.source.formula≼root)
    {τ : Slot→FiniteInventory.Triple Clock Var} {incoming : Equiv.Perm Clock}
    (frame : SlotFrame τ N incoming)
    (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot)
    (hFamily : ∀sig,SlotFrame.slotFamily τ (newSlot sig)=sig.val)
    (c : Clock) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hc : ledgerOpeningLeft T.rawLedger c kind I φ) :
    ∃s,RetrospectiveLeft root T frame newSlot c s ∧SlotFrame.slotFamily τ s=(kind,I,φ) := by
  obtain ⟨e,he,m,hs,hp⟩ := hc
  let sig : ↥(Finiteness.rootTemporalSignatures root) :=
    ⟨(kind,I,φ),T.opening_signature_mem root hBelow he kind I φ hs⟩
  obtain ⟨event,hev,heq,hx⟩ := T.opening_name_producer he c m kind I φ hp
  have hes : event.source=.plain (timedFormula sig.val.1 sig.val.2.1 sig.val.2.2) := by
    rw [heq]
    exact hs
  have hep : Predicate.upper event.x m sig.val.1 sig.val.2.1 sig.val.2.2∈event.body.currentPredicates := by
    have hb := congrArg RawLedgerEntry.body heq
    rw [hb,hx]
    exact hp
  refine ⟨newSlot sig,?_,hFamily sig⟩
  simpa only [hx] using (RetrospectiveLeft.opening (root:=root) (frame:=frame) (newSlot:=newSlot) event hev m sig hes hep)

/-- Every actual clocked ledger source has a retrospective left owner of its
exact temporal family, constructed from the actual input or actual opening. -/
theorem SelectedTree.ledger_clocked_left_coverage
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}
    (O : InputOrigins σ P α k N)
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (root : Formula Var) (hBelow : ∀e∈T.rawLedger,e.source.formula≼root)
    (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    {τ : Slot→FiniteInventory.Triple Clock Var} {incoming : Equiv.Perm Clock}
    (frame : SlotFrame τ N incoming)
    (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot)
    (hFamily : ∀sig,SlotFrame.slotFamily τ (newSlot sig)=sig.val)
    (e : RawLedgerEntry (Clock := Clock) (Var := Var)) (he : e∈T.rawLedger)
    (c : Clock) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hc : ClockedLeft e.source c kind I φ) :
    ∃s,RetrospectiveLeft root T frame newSlot c s ∧SlotFrame.slotFamily τ s=(kind,I,φ) := by
  rcases T.clocked_ledger_left_origin e he c kind I φ hc with hold | hopen
  · obtain ⟨p,hp,hleft⟩ := hold
    have hpN := (hLocal _).1 hp
    rcases hleft with ⟨m,rfl⟩ | ⟨d,m,r,rfl⟩
    · exact False.elim (O.no_upper c m kind I φ hpN)
    · obtain ⟨s,q,_,hcl,_,hk,hI,hφ⟩ := frame.predicates _ hpN
      refine ⟨s,.input c s hcl,?_⟩
      exact Prod.ext hk.symm (Prod.ext hI.symm hφ.symm)
  · exact T.opening_left_coverage root hBelow frame newSlot hFamily c kind I φ hopen

/-- Any left witness for this actual event has the same family. No separate
family-consistency assumption is imposed on retrospective witnesses. -/
theorem SelectedTree.ledger_clocked_left_family
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}
    (O : InputOrigins σ P α k N)
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (root : Formula Var) (hBelow : ∀e∈T.rawLedger,e.source.formula≼root)
    (hInput : SafeNormalization J (.ofState N))
    (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    {τ : Slot→FiniteInventory.Triple Clock Var} {incoming : Equiv.Perm Clock}
    (frame : SlotFrame τ N incoming)
    (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot)
    (hFamily : ∀sig,SlotFrame.slotFamily τ (newSlot sig)=sig.val)
    (e : RawLedgerEntry (Clock := Clock) (Var := Var)) (he : e∈T.rawLedger)
    (c : Clock) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hc : ClockedLeft e.source c kind I φ)
    (s : Slot) (hs : RetrospectiveLeft root T frame newSlot c s) :
    SlotFrame.slotFamily τ s=(kind,I,φ) := by
  obtain ⟨t,ht,hf⟩ := T.ledger_clocked_left_coverage O root hBelow hLocal frame newSlot hFamily e he c kind I φ hc
  have heq : t=s := RetrospectiveLeft.functional_of_eq hInput ht hs rfl
  exact heq ▸ hf
end STLTableau.Section4.Finiteness
