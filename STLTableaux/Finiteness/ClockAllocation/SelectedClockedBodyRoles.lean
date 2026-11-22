import STLTableaux.Finiteness.ClockAllocation.SelectedRoleAllocation
import STLTableaux.Finiteness.ClockAllocation.SelectedBodyNameProducer

/-! Every actual clocked branch body has one retrospective owner and at most
one non-left supported name. This includes guard-only next payloads. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var Slot : Type*} [DecidableEq Clock] [Fintype Slot]
variable {E : Set (Predicate Clock Var)} {U : Set Clock}
    {N : Section3.StateForm Clock Var} {J : MixedJ Clock Var} {W : Set Clock}
    {owned : OwnedPending J N.resets W} {H Er : MixedJ Clock Var}
    {τ : Slot→FiniteInventory.Triple Clock Var} {incoming : Equiv.Perm Clock}
    {root : Formula Var} {T : SelectedTree E U owned H Er}
    {frame : SlotFrame τ N incoming}
    {newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot}

theorem RetrospectiveLeft.role_zero {c : Clock} {s : Slot}
    (h : RetrospectiveLeft root T frame newSlot c s) :
    RetrospectiveRole root T frame newSlot c s 0 := by
  cases h with
  | input c s hr => exact .input c s 0 hr
  | opening event he m sig hs hp => exact .opening event he m sig hs hp

/-- A nonzero role cannot be the actual source left. -/
theorem RetrospectiveLeft.nonzero_ne_left
    (hInput : SafeNormalization J (.ofState N))
    {c a : Clock} {s t : Slot} {r : Fin 3}
    (left : RetrospectiveLeft root T frame newSlot c s)
    (role : RetrospectiveRole root T frame newSlot a t r) (hr : r≠0) : a≠c := by
  intro he
  exact hr (RetrospectiveRole.functional_of_eq hInput role left.role_zero he).2

/-- Every body name's role belongs to its actual source-left owner. -/
theorem SelectedTree.clocked_body_role_owner
    (T : SelectedTree E U owned H Er)
    (hInput : SafeNormalization J (.ofState N))
    (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (e : RawLedgerEntry (Clock := Clock) (Var := Var)) (he : e∈T.rawLedger)
    (c : Clock) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hc : ClockedLeft e.source c kind I φ)
    (s : Slot) (left : RetrospectiveLeft root T frame newSlot c s)
    (a : Clock) (ha : a∈syntaxClocks e.body) (t : Slot) (r : Fin 3)
    (role : RetrospectiveRole root T frame newSlot a t r) : t=s := by
  by_cases hac : a=c
  · exact (RetrospectiveRole.functional_of_eq hInput role left.role_zero hac).1
  rcases hc with ⟨m,hs⟩ | ⟨d,m,q,hs⟩
  · have hnot : a∉syntaxClocks (.predicate e.source) := by simpa [hs,syntaxClocks] using hac
    obtain ⟨event,hev,heq,hx⟩ := T.ledger_body_name_producer he a ha hnot
    have hsource : event.source=.upper c m kind I φ := (congrArg RawLedgerEntry.source heq).trans hs
    have hcanon : RetrospectiveRole root T frame newSlot event.x s (alternateRight frame.role s) :=
      .upper event hev c m kind I φ hsource s left
    exact (RetrospectiveRole.functional_of_eq hInput role hcanon hx.symm).1
  · have had : a=d := by
      have hb := e.actual.bounded_whole_support c d m q kind I φ hs ha
      exact hb.resolve_left hac
    have hp : Local.predicate e.source∈N.locals :=
      (hLocal _).1 (T.bounded_ledger_origin he (by rw [hs];trivial))
    rw [hs] at hp
    obtain ⟨v,z,hz,hcl,hdr,hkind,hI,hφ⟩ := frame.predicates _ hp
    have hv : v=s := RetrospectiveLeft.functional_of_eq hInput (.input c v hcl) left rfl
    subst v
    have hcanon : RetrospectiveRole root T frame newSlot d s z := .input d s z hdr
    exact (RetrospectiveRole.functional_of_eq hInput role hcanon had).1

/-- One actual clocked event cannot contribute both right roles: bounded
bodies use their inherited right, upper bodies have at most one actual new name. -/
theorem SelectedTree.clocked_body_nonzero_unique
    (T : SelectedTree E U owned H Er)
    (hInput : SafeNormalization J (.ofState N))
    (e : RawLedgerEntry (Clock := Clock) (Var := Var)) (he : e∈T.rawLedger)
    (c : Clock) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hc : ClockedLeft e.source c kind I φ)
    (s : Slot) (left : RetrospectiveLeft root T frame newSlot c s)
    (a b : Clock) (ha : a∈syntaxClocks e.body) (hb : b∈syntaxClocks e.body)
    (t v : Slot) (r q : Fin 3)
    (rolea : RetrospectiveRole root T frame newSlot a t r)
    (roleb : RetrospectiveRole root T frame newSlot b v q)
    (hr : r≠0) (hq : q≠0) : a=b := by
  have hac := left.nonzero_ne_left hInput rolea hr
  have hbc := left.nonzero_ne_left hInput roleb hq
  rcases hc with ⟨m,hs⟩ | ⟨d,m,q,hs⟩
  · have hna : a∉syntaxClocks (.predicate e.source) := by simpa [hs,syntaxClocks] using hac
    have hnb : b∉syntaxClocks (.predicate e.source) := by simpa [hs,syntaxClocks] using hbc
    obtain ⟨ea,hea,heqa,hxa⟩ := T.ledger_body_name_producer he a ha hna
    obtain ⟨eb,heb,heqb,hxb⟩ := T.ledger_body_name_producer he b hb hnb
    exact hxa.symm.trans ((ea.same_entry_name eb (heqa.trans heqb.symm)).trans hxb)
  · have had := (e.actual.bounded_whole_support c d m q kind I φ hs ha).resolve_left hac
    have hbd := (e.actual.bounded_whole_support c d m q kind I φ hs hb).resolve_left hbc
    exact had.trans hbd.symm
end STLTableau.Section4.Finiteness
