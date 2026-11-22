import STLTableaux.Finiteness.ClockAllocation.SelectedRolePermutation
import STLTableaux.Finiteness.ClockAllocation.SelectedClockedBodyRoles
import STLTableaux.Finiteness.ClockAllocation.SelectedNextAnnotations

/-! Actual formula-specific typing of surviving numeric annotations. Inherited
 assignments use their input role; introduced annotations use the SAME actual
 ledger source owner. No root-wide threshold multiplier is introduced. -/
namespace STLTableau.Section4.Finiteness
open Section3 Finiteness
open scoped STL
variable {Clock Var Slot : Type*} [DecidableEq Clock] [Fintype Slot]
variable {N : Section3.StateForm Clock Var} {J : MixedJ Clock Var} {W : Set Clock}
    {owned : OwnedPending J N.resets W} {H Er : MixedJ Clock Var}
    {τ : Slot→FiniteInventory.Triple Clock Var} {incoming : Clock≃Clock}
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}

omit [DecidableEq Clock] [Fintype Slot] in
theorem interval_constant_index {I : TimeInterval} {a : NNReal} (h : a∈intervalClockConstants I) :
    ∃j : Fin 3,a=FiniteInventory.endpoint I j := by
  classical
  cases I with
  | bounded I =>
      simp only [intervalClockConstants,Finset.mem_insert,Finset.mem_singleton] at h
      rcases h with h | h | h
      · exact ⟨0,h⟩
      · exact ⟨1,h⟩
      · exact ⟨2,h⟩
  | unbounded b =>
      simp only [intervalClockConstants,Finset.mem_insert,Finset.mem_singleton] at h
      rcases h with h | h
      · exact ⟨0,h⟩
      · exact ⟨1,h⟩

omit [DecidableEq Clock] [Fintype Slot] in
theorem SlotFrame.ResetTyped.mono {role role' : ClockRoles Clock Slot}
    (h : ∀c s r,role c=some (s,r) → role' c=some (s,r))
    {c : Clock} {a : NNReal} (ht : SlotFrame.ResetTyped τ role c a) : SlotFrame.ResetTyped τ role' c a := by
  obtain ⟨s,r,j,hr,ha⟩ := ht
  exact ⟨s,r,j,h c s r hr,ha⟩

theorem SelectedTree.retrospective_output_role
    (O : InputOrigins σ P α k N)
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (root : Formula Var) (hBelow : ∀entry∈T.rawLedger,entry.source.formula≼root)
    (hInput : SafeNormalization J (.ofState N)) (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (frame : SlotFrame τ N incoming)
    (newSlot : ↥(rootTemporalSignatures root)→Slot)
    (hFamily : ∀sig,SlotFrame.slotFamily τ (newSlot sig)=sig.val)
    {F : Section3.TransitionForm Clock Var} (hFull : SafeNormalization H F)
    {c : Clock} (hc : c∈F.allClocks) :
    ∃s r,retrospectiveRoleMap root T frame newSlot c=some (s,r) := by
  obtain ⟨s,r,hr⟩ := (T.retrospective_domain O root hBelow hLocal frame newSlot hFamily c).1
    (T.role_domain_covers_output hInput hFull hc)
  exact ⟨s,r,(retrospectiveRoleMap_iff root T hInput frame newSlot c s r).2 hr⟩

private theorem clocked_literal_constant
    (O : InputOrigins σ P α k N)
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (root : Formula Var) (hBelow : ∀entry∈T.rawLedger,entry.source.formula≼root)
    (hInput : SafeNormalization J (.ofState N)) (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (frame : SlotFrame τ N incoming) (newSlot : ↥(rootTemporalSignatures root)→Slot)
    (hFamily : ∀sig,SlotFrame.slotFamily τ (newSlot sig)=sig.val)
    (entry : RawLedgerEntry (Clock := Clock) (Var := Var)) (he : entry∈T.rawLedger)
    (left : Clock) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hclocked : ClockedLeft entry.source left kind I φ)
    {c : Clock} {a : NNReal} (hc : c∈syntaxClocks entry.body) (ha : a∈intervalClockConstants I)
    {t : Slot} {r : Fin 3} (hr : retrospectiveRoleMap root T frame newSlot c=some (t,r)) :
    SlotFrame.ResetTyped τ (retrospectiveRoleMap root T frame newSlot) c a := by
  obtain ⟨s,hs,hf⟩ := T.ledger_clocked_left_coverage O root hBelow hLocal frame newSlot hFamily
    entry he left kind I φ hclocked
  have ht := T.clocked_body_role_owner hInput hLocal entry he left kind I φ hclocked s hs c hc t r
    ((retrospectiveRoleMap_iff root T hInput frame newSlot c t r).1 hr)
  subst t
  obtain ⟨j,hj⟩ := interval_constant_index ha
  have hI : (τ s).interval=I := congrArg (fun family=>family.2.1) hf
  exact ⟨s,r,j,hr,by rw [hI]; exact hj⟩

/-- An annotation uses the interval of the actual owner of its clock. Plain
 branch zero annotations are valid in every owner slot. -/
theorem SelectedTree.retrospective_literal_constant_typed
    (O : InputOrigins σ P α k N)
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (root : Formula Var) (hBelow : ∀entry∈T.rawLedger,entry.source.formula≼root)
    (hInput : SafeNormalization J (.ofState N)) (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (frame : SlotFrame τ N incoming) (newSlot : ↥(rootTemporalSignatures root)→Slot)
    (hFamily : ∀sig,SlotFrame.slotFamily τ (newSlot sig)=sig.val)
    (entry : RawLedgerEntry (Clock := Clock) (Var := Var)) (he : entry∈T.rawLedger)
    {c : Clock} {a : NNReal} (hc : c∈syntaxClocks entry.body) (ha : a∈branchConstants entry.source)
    {t : Slot} {r : Fin 3} (hr : retrospectiveRoleMap root T frame newSlot c=some (t,r)) :
    SlotFrame.ResetTyped τ (retrospectiveRoleMap root T frame newSlot) c a := by
  classical
  cases hs : entry.source with
  | plain φ =>
      have hz : a=0 := by simpa only [hs,branchConstants,Finset.mem_singleton] using ha
      exact ⟨t,r,0,hr,by simp [hz,FiniteInventory.endpoint]⟩
  | upper left m kind I φ =>
      exact clocked_literal_constant O T root hBelow hInput hLocal frame newSlot hFamily entry he
        left kind I φ (Or.inl ⟨m,hs⟩) hc (by simpa only [hs,branchConstants] using ha) hr
  | bounded left d m q kind I φ =>
      exact clocked_literal_constant O T root hBelow hInput hLocal frame newSlot hFamily entry he
        left kind I φ (Or.inr ⟨d,m,q,hs⟩) hc (by simpa only [hs,branchConstants] using ha) hr

theorem SelectedTree.retrospective_current_resets_typed
    (O : InputOrigins σ P α k N)
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (root : Formula Var) (hBelow : ∀entry∈T.rawLedger,entry.source.formula≼root)
    (hInput : SafeNormalization J (.ofState N)) (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (frame : SlotFrame τ N incoming) (newSlot : ↥(rootTemporalSignatures root)→Slot)
    (hFamily : ∀sig,SlotFrame.slotFamily τ (newSlot sig)=sig.val)
    {F : Section3.TransitionForm Clock Var} (hFull : SafeNormalization H F)
    (c : Clock) (a : NNReal) (ha : F.current.resets.value c=some a) :
    SlotFrame.ResetTyped τ (retrospectiveRoleMap root T frame newSlot) c a := by
  rcases T.normalized_current_reset_provenance hFull ha with hold | ⟨entry,he,hraw,hval⟩
  · exact (frame.resets c a hold).mono (fun c s r hr=>retrospectiveRoleMap_input root T hInput frame newSlot hr)
  · have hc : c∈F.allClocks := by
      rw [hFull.allClocks_eq_syntax]
      exact (currentResetMap_value_literal (by rwa [← safe_reset_map hFull])).clock_support
    obtain ⟨s,r,hr⟩ := T.retrospective_output_role O root hBelow hInput hLocal frame newSlot hFamily hFull hc
    exact T.retrospective_literal_constant_typed O root hBelow hInput hLocal frame newSlot hFamily
      entry he hraw.clock_support hval hr

theorem SelectedTree.retrospective_next_guards_typed
    (O : InputOrigins σ P α k N)
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (root : Formula Var) (hBelow : ∀entry∈T.rawLedger,entry.source.formula≼root)
    (hInput : SafeNormalization J (.ofState N)) (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (frame : SlotFrame τ N incoming) (newSlot : ↥(rootTemporalSignatures root)→Slot)
    (hFamily : ∀sig,SlotFrame.slotFamily τ (newSlot sig)=sig.val)
    (hEmpty : owned.nextInputs=[])
    {F : Section3.TransitionForm Clock Var} (hFull : SafeNormalization H F)
    {M : Section3.StateForm Clock Var} (hn : F.nextPart=some M)
    (g : Section3.Guard Clock) (hg : g∈M.guards) :
    SlotFrame.GuardTyped τ (retrospectiveRoleMap root T frame newSlot) g := by
  obtain ⟨entry,he,hraw,hval⟩ := T.normalized_next_guard_provenance hEmpty hFull hn hg
  obtain ⟨K,hK,hgK⟩ := hFull.next_guard_payload_origin hn hg
  have hc : g.clock∈F.allClocks := by
    rw [hFull.allClocks_eq_syntax]
    exact (RawGuardAt.of_payload hK hgK).clock_support
  obtain ⟨s,r,hr⟩ := T.retrospective_output_role O root hBelow hInput hLocal frame newSlot hFamily hFull hc
  exact T.retrospective_literal_constant_typed O root hBelow hInput hLocal frame newSlot hFamily
    entry he hraw.clock_support hval hr

theorem SelectedTree.retrospective_next_resets_typed
    (O : InputOrigins σ P α k N)
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (root : Formula Var) (hBelow : ∀entry∈T.rawLedger,entry.source.formula≼root)
    (hInput : SafeNormalization J (.ofState N)) (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (frame : SlotFrame τ N incoming) (newSlot : ↥(rootTemporalSignatures root)→Slot)
    (hFamily : ∀sig,SlotFrame.slotFamily τ (newSlot sig)=sig.val)
    (hEmpty : owned.nextInputs=[])
    {F : Section3.TransitionForm Clock Var} (hFull : SafeNormalization H F)
    {M : Section3.StateForm Clock Var} (hn : F.nextPart=some M)
    (c : Clock) (a : NNReal) (ha : M.resets.value c=some a) :
    SlotFrame.ResetTyped τ (retrospectiveRoleMap root T frame newSlot) c a := by
  obtain ⟨entry,he,hraw,hval⟩ := T.normalized_next_reset_provenance hEmpty hFull hn ha
  obtain ⟨K,hK,hcK⟩ := hFull.next_reset_payload_origin hn ha
  have hc : c∈F.allClocks := by
    rw [hFull.allClocks_eq_syntax]
    exact (RawResetAt.of_payload hK hcK).clock_support
  obtain ⟨s,r,hr⟩ := T.retrospective_output_role O root hBelow hInput hLocal frame newSlot hFamily hFull hc
  exact T.retrospective_literal_constant_typed O root hBelow hInput hLocal frame newSlot hFamily
    entry he hraw.clock_support hval hr

end STLTableau.Section4.Finiteness
