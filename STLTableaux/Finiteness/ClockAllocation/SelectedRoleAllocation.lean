import STLTableaux.Finiteness.ClockAllocation.SelectedLeftCoverage

/-! Construct a partial clock-role map from opening events and the origins
of retained predicates. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var Slot : Type*} [DecidableEq Clock] [Fintype Slot]
variable {E : Set (Predicate Clock Var)} {U : Set Clock}
    {N : Section3.StateForm Clock Var} {J : MixedJ Clock Var} {W : Set Clock}
    {owned : OwnedPending J N.resets W} {H Er : MixedJ Clock Var}
    {τ : Slot→FiniteInventory.Triple Clock Var} {incoming : Clock≃Clock}

noncomputable def retrospectiveRoleMap (root : Formula Var)
    (T : SelectedTree E U owned H Er) (frame : SlotFrame τ N incoming)
    (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot) : ClockRoles Clock Slot := by
  classical
  intro c
  exact if h : ∃tag : Slot×Fin 3,RetrospectiveRole root T frame newSlot c tag.1 tag.2 then
    some (Classical.choose h) else none

theorem retrospectiveRoleMap_iff
    (root : Formula Var) (T : SelectedTree E U owned H Er)
    (hInput : SafeNormalization J (.ofState N)) (frame : SlotFrame τ N incoming)
    (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot) (c : Clock) (s : Slot) (r : Fin 3) :
    retrospectiveRoleMap root T frame newSlot c=some (s,r) ↔
      RetrospectiveRole root T frame newSlot c s r := by
  classical
  by_cases hex : ∃tag : Slot×Fin 3,RetrospectiveRole root T frame newSlot c tag.1 tag.2
  · simp only [retrospectiveRoleMap,dif_pos hex]
    constructor
    · intro he
      have hp := Classical.choose_spec hex
      have ht := Option.some.inj he
      simpa only [ht] using hp
    · intro hr
      have hf := RetrospectiveRole.functional_of_eq hInput (Classical.choose_spec hex) hr rfl
      exact congrArg some (Prod.ext hf.1 hf.2)
  · simp only [retrospectiveRoleMap,dif_neg hex]
    constructor
    · intro he; cases he
    · intro hr
      exact False.elim (hex ⟨(s,r),hr⟩)

theorem retrospectiveRoleMap_input
    (root : Formula Var) (T : SelectedTree E U owned H Er)
    (hInput : SafeNormalization J (.ofState N)) (frame : SlotFrame τ N incoming)
    (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot)
    {c : Clock} {s : Slot} {r : Fin 3} (hr : frame.role c=some (s,r)) :
    retrospectiveRoleMap root T frame newSlot c=some (s,r) :=
  (retrospectiveRoleMap_iff root T hInput frame newSlot c s r).2 (.input c s r hr)

variable {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}

/-- Every actual generated name has a role: openings get their newly chosen
 family slot, while upper rights reuse the actual source-left owner. -/
theorem SelectedTree.retrospective_used_name_coverage
    (O : InputOrigins σ P α k N)
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (root : Formula Var) (hBelow : ∀entry∈T.rawLedger,entry.source.formula≼root)
    (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (frame : SlotFrame τ N incoming)
    (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot)
    (hFamily : ∀sig,SlotFrame.slotFamily τ (newSlot sig)=sig.val)
    {c : Clock} (hc : c∈T.usedFreshClocks) :
    ∃s r,RetrospectiveRole root T frame newSlot c s r := by
  rw [← T.usedNameEvents_names] at hc
  obtain ⟨event,he,rfl⟩ := List.mem_map.1 hc
  have hledger := T.usedNameEvents_ledger he
  rcases event.opening_or_upper with ⟨m,kind,I,φ,hs,hbody⟩ | ⟨d,m,kind,I,φ,hs⟩
  · have hsig := T.opening_signature_mem root hBelow hledger kind I φ hs
    have hp : Predicate.upper event.x m kind I φ∈event.body.currentPredicates := by
      rw [hbody]
      simp [Section3.Judgement.currentPredicates]
    exact ⟨newSlot ⟨(kind,I,φ),hsig⟩,0,
      .opening event he m ⟨(kind,I,φ),hsig⟩ hs hp⟩
  · obtain ⟨s,hleft,_⟩ := T.ledger_clocked_left_coverage O root hBelow hLocal frame newSlot hFamily
      event.toRawLedgerEntry hledger d kind I φ (Or.inl ⟨m,hs⟩)
    exact ⟨s,alternateRight frame.role s,.upper event he d m kind I φ hs s hleft⟩

theorem SelectedTree.retrospective_domain
    (O : InputOrigins σ P α k N)
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (root : Formula Var) (hBelow : ∀entry∈T.rawLedger,entry.source.formula≼root)
    (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (frame : SlotFrame τ N incoming)
    (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot)
    (hFamily : ∀sig,SlotFrame.slotFamily τ (newSlot sig)=sig.val) (c : Clock) :
    c∈(Section3.TransitionForm.ofState N).allClocks ∪ {c|c∈T.usedFreshClocks} ↔
      ∃s r,RetrospectiveRole root T frame newSlot c s r := by
  constructor
  · intro hc
    rcases hc with hc | hc
    · obtain ⟨s,r,hr⟩ := (frame.domain c).1 hc
      exact ⟨s,r,.input c s r hr⟩
    · exact T.retrospective_used_name_coverage O root hBelow hLocal frame newSlot hFamily hc
  · rintro ⟨s,r,hr⟩
    exact hr.support

/-- The injection extends the input assignment to the fresh clocks used by the
selected derivation. Its domain contains the support of the full output. -/
noncomputable def SelectedTree.roleAllocation
    (O : InputOrigins σ P α k N)
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (root : Formula Var) (hBelow : ∀entry∈T.rawLedger,entry.source.formula≼root)
    (hInput : SafeNormalization J (.ofState N)) (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (frame : SlotFrame τ N incoming)
    (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot)
    (hFamily : ∀sig,SlotFrame.slotFamily τ (newSlot sig)=sig.val)
    (hnew : Function.Injective newSlot)
    (hfree : ∀sig,newSlot sig∉SlotFrame.occupied frame.role) :
    RoleAllocation (Slot := Slot)
      ((Section3.TransitionForm.ofState N).allClocks ∪ {c|c∈T.usedFreshClocks}) where
  role := retrospectiveRoleMap root T frame newSlot
  domain c := by
    rw [T.retrospective_domain O root hBelow hLocal frame newSlot hFamily c]
    constructor <;> rintro ⟨s,r,hr⟩ <;> refine ⟨s,r,?_⟩
    · exact (retrospectiveRoleMap_iff root T hInput frame newSlot c s r).2 hr
    · exact (retrospectiveRoleMap_iff root T hInput frame newSlot c s r).1 hr
  injective c d s r hc hd := RetrospectiveRole.injective_of_eq hnew hfree
    ((retrospectiveRoleMap_iff root T hInput frame newSlot c s r).1 hc)
    ((retrospectiveRoleMap_iff root T hInput frame newSlot d s r).1 hd) rfl

end STLTableau.Section4.Finiteness
