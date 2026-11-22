import STLTableaux.Finiteness.ClockAllocation.SelectedClockedBodyRoles
import STLTableaux.Finiteness.ClockAllocation.SelectedNextClockOrigin
import STLTableaux.Finiteness.Bounds.SelectedSuccessorSlotCount

/-! Restricts the clock assignment to the support of the next state. The
proof uses clocked branches of the same derivation, including branches whose
next clocks occur only in guards or resets. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var Slot : Type*} [DecidableEq Clock] [Fintype Slot]
variable {E : Set (Predicate Clock Var)} {U : Set Clock}
    {N : Section3.StateForm Clock Var} {J : MixedJ Clock Var} {W : Set Clock}
    {owned : OwnedPending J N.resets W} {H Er : MixedJ Clock Var}
    {τ : Slot→FiniteInventory.Triple Clock Var} {incoming : Equiv.Perm Clock}

noncomputable def selectedNextRole (root : Formula Var) (T : SelectedTree E U owned H Er)
    (frame : SlotFrame τ N incoming) (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot)
    (M : Section3.StateForm Clock Var) : ClockRoles Clock Slot := by
  classical
  exact fun c=>if c∈(Section3.TransitionForm.ofState M).allClocks then
    retrospectiveRoleMap root T frame newSlot c else none

theorem selectedNextRole_iff
    (root : Formula Var) (T : SelectedTree E U owned H Er)
    (hInput : SafeNormalization J (.ofState N))
    (frame : SlotFrame τ N incoming) (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot)
    (M : Section3.StateForm Clock Var) (c : Clock) (s : Slot) (r : Fin 3) :
    selectedNextRole root T frame newSlot M c=some (s,r) ↔
      c∈(Section3.TransitionForm.ofState M).allClocks ∧ RetrospectiveRole root T frame newSlot c s r := by
  classical
  by_cases hc : c∈(Section3.TransitionForm.ofState M).allClocks
  · simpa only [selectedNextRole,hc,if_true,true_and] using
      retrospectiveRoleMap_iff root T hInput frame newSlot c s r
  · simp only [selectedNextRole,hc,if_false,false_and,reduceCtorEq]

noncomputable def selectedLedgerOwner (root : Formula Var) (T : SelectedTree E U owned H Er)
    (frame : SlotFrame τ N incoming) (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot)
    (e : RawLedgerEntry (Clock := Clock) (Var := Var)) : Option Slot :=
  e.leftClock.bind (fun c=>(retrospectiveRoleMap root T frame newSlot c).map Prod.fst)

omit [DecidableEq Clock] in
private theorem next_syntax_subset_body (J : MixedJ Clock Var) (c : Clock)
    (hc : c∈nextSyntaxClocks J) : c∈syntaxClocks J := by
  have hs : nextSyntaxClocks J⊆syntaxClocks J := by
    clear hc
    induction J with
    | terminal | clock | marker | predicate | next => simp [nextSyntaxClocks,syntaxClocks]
    | conj J K ih ik => exact Set.union_subset_union ih ik
    | reset R J ih => exact ih.trans Set.subset_union_right
  exact hs hc

private theorem leftClock_of_clocked (e : RawLedgerEntry (Clock := Clock) (Var := Var))
    (c : Clock) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hc : ClockedLeft e.source c kind I φ) : e.leftClock=some c := by
  rcases hc with ⟨m,hs⟩ | ⟨d,m,r,hs⟩ <;> simp [RawLedgerEntry.leftClock,hs]

theorem selectedLedgerOwner_of_left
    (root : Formula Var) (T : SelectedTree E U owned H Er)
    (hInput : SafeNormalization J (.ofState N))
    (frame : SlotFrame τ N incoming) (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot)
    (e : RawLedgerEntry (Clock := Clock) (Var := Var)) (c : Clock) (s : Slot)
    (hc : e.leftClock=some c) (left : RetrospectiveLeft root T frame newSlot c s) :
    selectedLedgerOwner root T frame newSlot e=some s := by
  have hr := (retrospectiveRoleMap_iff root T hInput frame newSlot c s 0).2 left.role_zero
  simp [selectedLedgerOwner,hc,hr]

variable {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}

/-- In the next state, at most one right clock of each slot is in use. -/
theorem SelectedTree.selectedNextRole_right_unique
    (O : InputOrigins σ P α k N) (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (root : Formula Var) (hBelow : ∀e∈T.rawLedger,e.source.formula≼root)
    (hInput : SafeNormalization J (.ofState N)) (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (frame : SlotFrame τ N incoming) (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot)
    (hFamily : ∀sig,SlotFrame.slotFamily τ (newSlot sig)=sig.val)
    (hnew : Function.Injective newSlot) (hfree : ∀sig,newSlot sig∉SlotFrame.occupied frame.role)
    (hEmpty : owned.nextInputs=[])
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization H F)
    {M : Section3.StateForm Clock Var} (hn : F.nextPart=some M) :
    ∀s,¬((∃a,selectedNextRole root T frame newSlot M a=some (s,1)) ∧
      (∃b,selectedNextRole root T frame newSlot M b=some (s,2))) := by
  intro s h
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := h
  obtain ⟨ha,rolea⟩ := (selectedNextRole_iff root T hInput frame newSlot M a s 1).1 ha
  obtain ⟨hb,roleb⟩ := (selectedNextRole_iff root T hInput frame newSlot M b s 2).1 hb
  obtain ⟨e,he,ha,hs⟩ := T.next_clock_clocked_ledger_origin hEmpty hSafe hn a ha
  obtain ⟨f,hf,hb,ht⟩ := T.next_clock_clocked_ledger_origin hEmpty hSafe hn b hb
  have hce : ∃c kind I φ,ClockedLeft e.source c kind I φ := by
    rcases hs with ⟨c,m,kind,I,φ,hs⟩ | ⟨c,d,m,q,kind,I,φ,hs⟩
    · exact ⟨c,kind,I,φ,Or.inl ⟨m,hs⟩⟩
    · exact ⟨c,kind,I,φ,Or.inr ⟨d,m,q,hs⟩⟩
  have hcf : ∃c kind I φ,ClockedLeft f.source c kind I φ := by
    rcases ht with ⟨c,m,kind,I,φ,hs⟩ | ⟨c,d,m,q,kind,I,φ,hs⟩
    · exact ⟨c,kind,I,φ,Or.inl ⟨m,hs⟩⟩
    · exact ⟨c,kind,I,φ,Or.inr ⟨d,m,q,hs⟩⟩
  obtain ⟨c,kind,I,φ,hc⟩ := hce
  obtain ⟨d,kind',I',φ',hd⟩ := hcf
  obtain ⟨u,lefta,_⟩ := T.ledger_clocked_left_coverage O root hBelow hLocal frame newSlot hFamily e he c kind I φ hc
  obtain ⟨v,leftb,_⟩ := T.ledger_clocked_left_coverage O root hBelow hLocal frame newSlot hFamily f hf d kind' I' φ' hd
  have habody := next_syntax_subset_body e.body a ha
  have hbbody := next_syntax_subset_body f.body b hb
  have hsu := T.clocked_body_role_owner hInput hLocal e he c kind I φ hc u lefta a habody s 1 rolea
  have hsv := T.clocked_body_role_owner hInput hLocal f hf d kind' I' φ' hd v leftb b hbbody s 2 roleb
  have hcd := RetrospectiveLeft.injective_of_eq hnew hfree lefta leftb (hsu.symm.trans hsv)
  have hef := T.rawLedger_same_left_unique e f c he hf
    (leftClock_of_clocked e c kind I φ hc) (by rw [hcd]; exact leftClock_of_clocked f d kind' I' φ' hd)
  subst f
  have hab := T.clocked_body_nonzero_unique hInput e he c kind I φ hc u lefta
    a b habody hbbody s s 1 2 rolea roleb (by decide) (by decide)
  have h12 := (RetrospectiveRole.functional_of_eq hInput rolea roleb hab).2
  exact (by decide : (1 : Fin 3)≠2) h12


/-- Each occupied slot of the next state is associated to a clocked branch for
the same timed subformula, including branches with only guards or resets
in the next judgement. -/
theorem SelectedTree.selectedNextRole_owner_cover
    (O : InputOrigins σ P α k N) (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (root : Formula Var) (hBelow : ∀e∈T.rawLedger,e.source.formula≼root)
    (hInput : SafeNormalization J (.ofState N)) (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (frame : SlotFrame τ N incoming) (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot)
    (hFamily : ∀sig,SlotFrame.slotFamily τ (newSlot sig)=sig.val)
    (hEmpty : owned.nextInputs=[])
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization H F)
    {M : Section3.StateForm Clock Var} (hn : F.nextPart=some M)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    ∀s∈SlotFrame.occupiedFamily τ (selectedNextRole root T frame newSlot M) kind I φ,
      ∃e∈T.rawLedger,selectedLedgerOwner root T frame newSlot e=some s ∧
        ((∃c m,e.source=.upper c m kind I φ) ∨
          (∃c d m r,e.source=.bounded c d m r kind I φ)) := by
  classical
  intro s hs
  obtain ⟨ho,hfam⟩ := Finset.mem_filter.mp hs
  simp only [SlotFrame.occupied,Finset.mem_filter,Finset.mem_univ,true_and] at ho
  obtain ⟨a,r,hr⟩ := ho
  obtain ⟨ha,role⟩ := (selectedNextRole_iff root T hInput frame newSlot M a s r).1 hr
  obtain ⟨e,he,ha,hsource⟩ := T.next_clock_clocked_ledger_origin hEmpty hSafe hn a ha
  have hce : ∃c kind I φ,ClockedLeft e.source c kind I φ := by
    rcases hsource with ⟨c,m,kind,I,φ,hs⟩ | ⟨c,d,m,q,kind,I,φ,hs⟩
    · exact ⟨c,kind,I,φ,Or.inl ⟨m,hs⟩⟩
    · exact ⟨c,kind,I,φ,Or.inr ⟨d,m,q,hs⟩⟩
  obtain ⟨c,kind',I',φ',hc⟩ := hce
  obtain ⟨u,left,hownerFamily⟩ := T.ledger_clocked_left_coverage O root hBelow hLocal frame newSlot hFamily e he c kind' I' φ' hc
  have hsu := T.clocked_body_role_owner hInput hLocal e he c kind' I' φ' hc u left a
    (next_syntax_subset_body e.body a ha) s r role
  have lefts : RetrospectiveLeft root T frame newSlot c s := hsu.symm ▸left
  have hsourceFamily : SlotFrame.slotFamily τ s=(kind',I',φ') := hsu.symm ▸hownerFamily
  have htargetFamily : SlotFrame.slotFamily τ s=(kind,I,φ) :=
    Prod.ext hfam.1 (Prod.ext hfam.2.1 hfam.2.2)
  have hsig : (kind',I',φ')=(kind,I,φ) := hsourceFamily.symm.trans htargetFamily
  refine ⟨e,he,selectedLedgerOwner_of_left root T hInput frame newSlot e c s
    (leftClock_of_clocked e c kind' I' φ' hc) lefts,?_⟩
  cases hsig
  rcases hc with ⟨m,hs⟩ | ⟨d,m,q,hs⟩
  · exact Or.inl ⟨c,m,hs⟩
  · exact Or.inr ⟨c,d,m,q,hs⟩

/-- Bounds the occupied successor slots for each timed subformula by counting
the corresponding clocked branches of the selected derivation. -/
theorem SelectedTree.selectedNextRole_occupied_bound
    (O : InputOrigins σ P α k N) (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (root : Formula Var) (hBelow : ∀e∈T.rawLedger,e.source.formula≼root)
    (hInput : SafeNormalization J (.ofState N)) (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (frame : SlotFrame τ N incoming) (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot)
    (hFamily : ∀sig,SlotFrame.slotFamily τ (newSlot sig)=sig.val)
    (hEmpty : owned.nextInputs=[])
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization H F)
    {M : Section3.StateForm Clock Var} (hn : F.nextPart=some M)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    (SlotFrame.occupiedFamily τ (selectedNextRole root T frame newSlot M) kind I φ).card≤temporalOriginCap I+1 :=
  T.successor_occupiedFamily_card_le O hLocal τ (selectedNextRole root T frame newSlot M)
    (selectedLedgerOwner root T frame newSlot) kind I φ
    (T.selectedNextRole_owner_cover O root hBelow hInput hLocal frame newSlot hFamily hEmpty hSafe hn kind I φ)
end STLTableau.Section4.Finiteness
