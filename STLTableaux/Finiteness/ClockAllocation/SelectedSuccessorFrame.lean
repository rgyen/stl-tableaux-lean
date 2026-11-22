import STLTableaux.Finiteness.ClockAllocation.SelectedSuccessorRoles
import STLTableaux.Finiteness.ClockAllocation.SelectedTransitionRoleTyping
import STLTableaux.Finiteness.ClockAllocation.SelectedRolePermutation
import STLTableaux.Finiteness.Inventory.RoleTypedInventory
import STLTableaux.Finiteness.ClockAllocation.AllocatedSelectedPath

/-! Actual input-role restriction and successor frame assembly. Every role
retained here belongs to an actual supported next name. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var Slot : Type*} [DecidableEq Clock] [Fintype Slot]

omit [DecidableEq Clock] in
private theorem local_support (S : Section3.StateForm Clock Var) (l : Local Clock Var)
    (hl : l∈S.locals) (c : Clock) (hc : c∈l.freeClocks) :
    c∈(Section3.TransitionForm.ofState S).allClocks := by
  rw [ofState_support]
  exact Or.inl (Or.inr ⟨l,hl,hc⟩)

omit [DecidableEq Clock] [Fintype Slot] in
/-- Role typing observes only actual syntax support; absent names are irrelevant. -/
theorem SlotFrame.StateTyped.congr_on_support
    {τ : Slot→FiniteInventory.Triple Clock Var} {role role' : ClockRoles Clock Slot}
    {S : Section3.StateForm Clock Var} (typed : SlotFrame.StateTyped τ role S)
    (he : ∀c∈(Section3.TransitionForm.ofState S).allClocks,role' c=role c) :
    SlotFrame.StateTyped τ role' S := by
  constructor
  · intro p hp
    have ht := typed.predicates p hp
    cases p with
    | plain => trivial
    | upper c m kind I φ =>
      obtain ⟨s,hc,hk,hI,hφ⟩ := ht
      refine ⟨s,?_,hk,hI,hφ⟩
      rw [he c (local_support S _ hp c (by simp [Local.freeClocks,Local.toJudgement,Section3.Judgement.freeClocks]))]
      exact hc
    | bounded c d m q kind I φ =>
      obtain ⟨s,r,hr,hc,hd,hk,hI,hφ⟩ := ht
      refine ⟨s,r,hr,?_,?_,hk,hI,hφ⟩
      · rw [he c (local_support S _ hp c (by simp [Local.freeClocks,Local.toJudgement,Section3.Judgement.freeClocks]))]
        exact hc
      · rw [he d (local_support S _ hp d (by simp [Local.freeClocks,Local.toJudgement,Section3.Judgement.freeClocks]))]
        exact hd
  · intro g hg
    obtain ⟨s,r,j,hr,hj⟩ := typed.guards g hg
    refine ⟨s,r,j,?_,hj⟩
    rw [he g.clock (by rw [ofState_support];exact Or.inl (Or.inl ⟨g,hg,rfl⟩))]
    exact hr
  · intro c a hc
    obtain ⟨s,r,j,hr,hj⟩ := typed.resets c a hc
    refine ⟨s,r,j,?_,hj⟩
    rw [he c (by rw [ofState_support];exact Or.inr ⟨a,hc⟩)]
    exact hr

variable {N : Section3.StateForm Clock Var} {J : MixedJ Clock Var} {W : Set Clock}
    {owned : OwnedPending J N.resets W} {H Er : MixedJ Clock Var}
    {τ : Slot→FiniteInventory.Triple Clock Var} {incoming : Equiv.Perm Clock}
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}

/-- The restricted role map is an actual injection with exactly actual next
support as domain; coverage comes from the constructed global relation. -/
noncomputable def SelectedTree.successorRoleAllocation
    (O : InputOrigins σ P α k N) (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (root : Formula Var) (hBelow : ∀e∈T.rawLedger,e.source.formula≼root)
    (hInput : SafeNormalization J (.ofState N)) (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (frame : SlotFrame τ N incoming) (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot)
    (hFamily : ∀sig,SlotFrame.slotFamily τ (newSlot sig)=sig.val)
    (hnew : Function.Injective newSlot) (hfree : ∀sig,newSlot sig∉SlotFrame.occupied frame.role)
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization H F)
    {M : Section3.StateForm Clock Var} (hn : F.nextPart=some M) :
    RoleAllocation (Slot := Slot) (Section3.TransitionForm.ofState M).allClocks where
  role := selectedNextRole root T frame newSlot M
  domain c := by
    constructor
    · intro hc
      have hg := T.role_domain_covers_output hInput hSafe (next_whole_support hn hc)
      obtain ⟨s,r,hr⟩ := (T.retrospective_domain O root hBelow hLocal frame newSlot hFamily c).1 hg
      exact ⟨s,r,(selectedNextRole_iff root T hInput frame newSlot M c s r).2 ⟨hc,hr⟩⟩
    · rintro ⟨s,r,hr⟩
      exact ((selectedNextRole_iff root T hInput frame newSlot M c s r).1 hr).1
  injective c d s r hc hd := RetrospectiveRole.injective_of_eq hnew hfree
    ((selectedNextRole_iff root T hInput frame newSlot M c s r).1 hc).2
    ((selectedNextRole_iff root T hInput frame newSlot M d s r).1 hd).2 rfl

/-- The actual restriction leaves every supported next role unchanged. -/
theorem selectedNextRole_on_support
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    (root : Formula Var) (T : SelectedTree E U owned H Er)
    (frame : SlotFrame τ N incoming) (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot)
    (M : Section3.StateForm Clock Var) (c : Clock)
    (hc : c∈(Section3.TransitionForm.ofState M).allClocks) :
    selectedNextRole root T frame newSlot M c=retrospectiveRoleMap root T frame newSlot c := by
  classical
  simp only [selectedNextRole,hc,if_true]


/-- The complete actual successor frame: typing, support, uniqueness, and
occupied budgets all follow from this SAME selected tree. -/
noncomputable def SelectedTree.successorSlotFrame
    (O : InputOrigins σ P α k N) (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (root : Formula Var) (hBelow : ∀e∈T.rawLedger,e.source.formula≼root)
    (hInput : SafeNormalization J (.ofState N)) (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (hEmpty : owned.nextInputs=[])
    {A : Set Clock} {F : Section3.TransitionForm Clock Var}
    (hFacts : SelectedOutputFacts owned A O.strictClocks σ P α k H Er F)
    (frame : SlotFrame τ N incoming) (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot)
    (hFamily : ∀sig,SlotFrame.slotFamily τ (newSlot sig)=sig.val)
    (hnew : Function.Injective newSlot) (hfree : ∀sig,newSlot sig∉SlotFrame.occupied frame.role)
    (e : Equiv.Perm Clock)
    (he : ∀c s r,retrospectiveRoleMap root T frame newSlot c=some (s,r) →
      e c=FiniteInventory.clockAt (τ s) r)
    {M : Section3.StateForm Clock Var} (hn : F.nextPart=some M) : SlotFrame τ M e := by
  let alloc := T.successorRoleAllocation O root hBelow hInput hLocal frame newSlot hFamily hnew hfree hFacts.1 hn
  have ht := (T.retrospective_transition_typed O root hBelow hInput hLocal hEmpty hFacts
    frame newSlot hFamily hnew hfree).next M hn
  have ht' : SlotFrame.StateTyped τ (selectedNextRole root T frame newSlot M) M :=
    ht.congr_on_support (fun c hc=>selectedNextRole_on_support root T frame newSlot M c hc)
  refine ⟨alloc,?_,ht'.predicates,ht'.guards,ht'.resets,?_,?_⟩
  · intro c s r hr
    have hh := ((selectedNextRole_iff root T hInput frame newSlot M c s r).1 hr).2
    exact he c s r ((retrospectiveRoleMap_iff root T hInput frame newSlot c s r).2 hh)
  · exact T.selectedNextRole_right_unique O root hBelow hInput hLocal frame newSlot
      hFamily hnew hfree hEmpty hFacts.1 hn
  · intro kind I φ
    have hb := T.selectedNextRole_occupied_bound O root hBelow hInput hLocal frame newSlot
      hFamily hEmpty hFacts.1 hn kind I φ
    exact hb.trans (by omega)
end STLTableau.Section4.Finiteness
