import STLTableaux.Finiteness.ClockAllocation.SelectedRoleAllocation
import STLTableaux.Finiteness.Inventory.RoleTypedInventory

/-! Actual ledger sources and complete retained current predicates are typed
in the constructed retrospective map, without assuming source typing. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var Slot : Type*} [DecidableEq Clock] [Fintype Slot]

omit [DecidableEq Clock] [Fintype Slot] in
/-- Predicate typing is preserved by actual supported role-graph inclusion. -/
theorem SlotFrame.PredicateTyped.mono
    {τ : Slot→FiniteInventory.Triple Clock Var} {role role' : ClockRoles Clock Slot}
    {p : Predicate Clock Var} (hp : SlotFrame.PredicateTyped τ role p)
    (he : ∀c s r,role c=some (s,r) → role' c=some (s,r)) :
    SlotFrame.PredicateTyped τ role' p := by
  cases p with
  | plain => trivial
  | upper c m kind I φ =>
    obtain ⟨s,hc,hk,hI,hφ⟩ := hp
    exact ⟨s,he _ _ _ hc,hk,hI,hφ⟩
  | bounded c d m r kind I φ =>
    obtain ⟨s,q,hq,hc,hd,hk,hI,hφ⟩ := hp
    exact ⟨s,q,hq,he _ _ _ hc,he _ _ _ hd,hk,hI,hφ⟩

variable {E : Set (Predicate Clock Var)} {U : Set Clock}
    {N : Section3.StateForm Clock Var} {J : MixedJ Clock Var} {W : Set Clock}
    {owned : OwnedPending J N.resets W} {H Er : MixedJ Clock Var}
    {τ : Slot→FiniteInventory.Triple Clock Var} {incoming : Equiv.Perm Clock}

/-- Every actual left-owner witness is also a zero-role witness. -/
theorem RetrospectiveLeft.toRole
    {root : Formula Var} {T : SelectedTree E U owned H Er}
    {frame : SlotFrame τ N incoming}
    {newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot}
    {c : Clock} {s : Slot} (h : RetrospectiveLeft root T frame newSlot c s) :
    RetrospectiveRole root T frame newSlot c s 0 := by
  cases h with
  | input c s hr => exact .input c s 0 hr
  | opening e he m sig hs hp => exact .opening e he m sig hs hp

variable {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}

theorem SelectedTree.retrospective_ledger_source_typed
    (O : InputOrigins σ P α k N)
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (root : Formula Var) (hBelow : ∀entry∈T.rawLedger,entry.source.formula≼root)
    (hInput : SafeNormalization J (.ofState N))
    (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (frame : SlotFrame τ N incoming)
    (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot)
    (hFamily : ∀sig,SlotFrame.slotFamily τ (newSlot sig)=sig.val)
    (entry : RawLedgerEntry (Clock := Clock) (Var := Var)) (he : entry∈T.rawLedger) :
    SlotFrame.PredicateTyped τ (retrospectiveRoleMap root T frame newSlot) entry.source := by
  cases hs : entry.source with
  | plain φ => trivial
  | upper c m kind I φ =>
    obtain ⟨s,hleft,hf⟩ := T.ledger_clocked_left_coverage O root hBelow hLocal frame newSlot hFamily
      entry he c kind I φ (Or.inl ⟨m,hs⟩)
    have hr := (retrospectiveRoleMap_iff root T hInput frame newSlot c s 0).2 hleft.toRole
    have hk : (τ s).kind=kind := congrArg Prod.fst hf
    have hI : (τ s).interval=I := congrArg (fun t=>t.2.1) hf
    have hφ : (τ s).body=φ := congrArg (fun t=>t.2.2) hf
    exact ⟨s,hr,hk.symm,hI.symm,hφ.symm⟩
  | bounded c d m r kind I φ =>
    have hb : IsBoundedPredicate entry.source := by rw [hs];trivial
    have hp := (hLocal _).1 (T.bounded_ledger_origin he hb)
    have ht := frame.predicates entry.source hp
    have ht' := ht.mono (fun _ _ _ h=>retrospectiveRoleMap_input root T hInput frame newSlot h)
    simpa only [hs] using ht'

/-- All full-current predicates, including retained clocked annotations and
unexpanded atomic unclocked leaves, have actual retrospective slot typing. -/
theorem SelectedTree.retrospective_current_predicates_typed
    (O : InputOrigins σ P α k N)
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (root : Formula Var) (hBelow : ∀entry∈T.rawLedger,entry.source.formula≼root)
    (hInput : SafeNormalization J (.ofState N))
    (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    {F : Section3.TransitionForm Clock Var} (hFull : SafeNormalization H F)
    (frame : SlotFrame τ N incoming)
    (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot)
    (hFamily : ∀sig,SlotFrame.slotFamily τ (newSlot sig)=sig.val) :
    ∀p,Local.predicate p∈F.current.locals →
      SlotFrame.PredicateTyped τ (retrospectiveRoleMap root T frame newSlot) p := by
  intro p hp
  cases p with
  | plain => trivial
  | upper c m kind I φ =>
    obtain ⟨entry,he,hs⟩ := (T.normalized_retained_nonatomic_iff hFull _ (by simp [Predicate.IsAtomic])).1 hp
    simpa only [hs] using T.retrospective_ledger_source_typed O root hBelow hInput hLocal frame newSlot hFamily entry he
  | bounded c d m r kind I φ =>
    obtain ⟨entry,he,hs⟩ := (T.normalized_retained_nonatomic_iff hFull _ (by simp [Predicate.IsAtomic])).1 hp
    simpa only [hs] using T.retrospective_ledger_source_typed O root hBelow hInput hLocal frame newSlot hFamily entry he
end STLTableau.Section4.Finiteness
