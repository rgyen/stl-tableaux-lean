import STLTableaux.Finiteness.ClockAllocation.SelectedNameEvents
import STLTableaux.Finiteness.ClockAllocation.SelectedOpeningOwners
import STLTableaux.Finiteness.Derivation.Selection.SelectedLedgerPrivacy
import STLTableaux.Finiteness.ClockAllocation.SelectedEventClassification
import STLTableaux.Finiteness.ClockAllocation.OpeningSlotAssignment

/-! Clock assignments for a selected expansion. The relation records the
input roles and the clocks used by opening branches and expansions
of interval predicates in the `↑` form. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var Slot : Type*}

noncomputable def alternateRight (role : ClockRoles Clock Slot) (s : Slot) : Fin 3 := by
  classical
  exact if ∃c,role c=some (s,1) then 2 else 1

theorem alternateRight_ne_zero (role : ClockRoles Clock Slot) (s : Slot) :
    alternateRight role s≠0 := by
  classical
  by_cases h : ∃c,role c=some (s,1) <;> simp [alternateRight,h]

variable [Fintype Slot]

theorem SlotFrame.alternateRight_unused
    {τ : Slot→FiniteInventory.Triple Clock Var} {N : Section3.StateForm Clock Var}
    {incoming : Clock≃Clock} (frame : SlotFrame τ N incoming) (s : Slot) (c : Clock) :
    frame.role c≠some (s,alternateRight frame.role s) := by
  classical
  by_cases h : ∃d,frame.role d=some (s,1)
  · simp only [alternateRight,if_pos h]
    exact fun hc => frame.right_unique s ⟨h,⟨c,hc⟩⟩
  · simp only [alternateRight,if_neg h]
    exact fun hc => h ⟨c,hc⟩

variable [DecidableEq Clock]

variable {E : Set (Predicate Clock Var)} {U : Set Clock}
  {N : Section3.StateForm Clock Var} {J : MixedJ Clock Var} {W : Set Clock}
  {owned : OwnedPending J N.resets W} {H Er : MixedJ Clock Var}
  {τ : Slot→FiniteInventory.Triple Clock Var} {incoming : Clock≃Clock}

/-- A new left clock may reuse a historical name outside the input support.
The relation preserves the assignments of clocks in the input support. -/
inductive RetrospectiveLeft (root : Formula Var) (T : SelectedTree E U owned H Er)
    (frame : SlotFrame τ N incoming)
    (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot) : Clock→Slot→Prop
  | input (c : Clock) (s : Slot) (h : frame.role c=some (s,0)) : RetrospectiveLeft root T frame newSlot c s
  | opening (event : UsedNameEvent (Clock := Clock) (Var := Var)) (he : event∈T.usedNameEvents)
      (m : Marker) (sig : ↥(Finiteness.rootTemporalSignatures root))
      (hs : event.source=.plain (timedFormula sig.val.1 sig.val.2.1 sig.val.2.2))
      (hp : Predicate.upper event.x m sig.val.1 sig.val.2.1 sig.val.2.2∈event.body.currentPredicates) :
      RetrospectiveLeft root T frame newSlot event.x (newSlot sig)

inductive RetrospectiveRole (root : Formula Var) (T : SelectedTree E U owned H Er)
    (frame : SlotFrame τ N incoming)
    (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot) : Clock→Slot→Fin 3→Prop
  | input (c : Clock) (s : Slot) (r : Fin 3) (h : frame.role c=some (s,r)) :
      RetrospectiveRole root T frame newSlot c s r
  | opening (event : UsedNameEvent (Clock := Clock) (Var := Var)) (he : event∈T.usedNameEvents)
      (m : Marker) (sig : ↥(Finiteness.rootTemporalSignatures root))
      (hs : event.source=.plain (timedFormula sig.val.1 sig.val.2.1 sig.val.2.2))
      (hp : Predicate.upper event.x m sig.val.1 sig.val.2.1 sig.val.2.2∈event.body.currentPredicates) :
      RetrospectiveRole root T frame newSlot event.x (newSlot sig) 0
  | upper (event : UsedNameEvent (Clock := Clock) (Var := Var)) (he : event∈T.usedNameEvents)
      (c : Clock) (m : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
      (hs : event.source=.upper c m kind I φ) (s : Slot)
      (left : RetrospectiveLeft root T frame newSlot c s) :
      RetrospectiveRole root T frame newSlot event.x s (alternateRight frame.role s)

theorem SelectedTree.used_event_name_mem (T : SelectedTree E U owned H Er)
    {event : UsedNameEvent (Clock := Clock) (Var := Var)} (he : event∈T.usedNameEvents) :
    event.x∈T.usedFreshClocks := by
  rw [← T.usedNameEvents_names]
  exact List.mem_map.2 ⟨event,he,rfl⟩

theorem SelectedTree.used_event_outside_input (T : SelectedTree E U owned H Er)
    (hInput : SafeNormalization J (.ofState N))
    {event : UsedNameEvent (Clock := Clock) (Var := Var)} (he : event∈T.usedNameEvents) :
    event.x∉(Section3.TransitionForm.ofState N).allClocks := by
  intro hc
  have hw : event.x∈inputClockSupport J N.resets := by
    rwa [input_clock_support_of_safe hInput]
  have hw' : event.x∈W := by
    rcases hw with hw | hw
    · exact owned.covers_input (Or.inl (Or.inl hw))
    · exact owned.covers_input (Or.inr hw)
  exact T.usedFreshClocks_outside event.x (T.used_event_name_mem he) hw'

theorem RetrospectiveRole.support
    {root : Formula Var} {T : SelectedTree E U owned H Er}
    {frame : SlotFrame τ N incoming}
    {newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot}
    {c : Clock} {s : Slot} {r : Fin 3} (h : RetrospectiveRole root T frame newSlot c s r) :
    c∈(Section3.TransitionForm.ofState N).allClocks ∪ {c|c∈T.usedFreshClocks} := by
  cases h with
  | input c s r hr => exact Or.inl ((frame.domain c).2 ⟨s,r,hr⟩)
  | opening e he => exact Or.inr (T.used_event_name_mem he)
  | upper e he => exact Or.inr (T.used_event_name_mem he)

private theorem event_no_input_role
    {T : SelectedTree E U owned H Er} (hInput : SafeNormalization J (.ofState N))
    {frame : SlotFrame τ N incoming}
    {event : UsedNameEvent (Clock := Clock) (Var := Var)} (he : event∈T.usedNameEvents)
    {s : Slot} {r : Fin 3} (hr : frame.role event.x=some (s,r)) : False :=
  T.used_event_outside_input hInput he ((frame.domain event.x).2 ⟨s,r,hr⟩)

theorem RetrospectiveLeft.functional_of_eq
    {root : Formula Var} {T : SelectedTree E U owned H Er}
    (hInput : SafeNormalization J (.ofState N)) {frame : SlotFrame τ N incoming}
    {newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot}
    {c d : Clock} {s t : Slot}
    (h : RetrospectiveLeft root T frame newSlot c s)
    (g : RetrospectiveLeft root T frame newSlot d t) (hc : c=d) : s=t := by
  cases h with
  | input c s hr =>
      cases g with
      | input d t ht =>
          rw [← hc] at ht
          exact congrArg Prod.fst (Option.some.inj (hr.symm.trans ht))
      | opening event he m sig hs hp =>
          rw [hc] at hr
          exact False.elim (event_no_input_role hInput he hr)
  | opening event he m sig hs hp =>
      cases g with
      | input d t ht =>
          rw [← hc] at ht
          exact False.elim (event_no_input_role hInput he ht)
      | opening other ho n tag ht hq =>
          have hf : ledgerOpeningLeft T.rawLedger event.x tag.val.1 tag.val.2.1 tag.val.2.2 := by
            rw [hc]
            exact ⟨other.toRawLedgerEntry,T.usedNameEvents_ledger ho,n,ht,hq⟩
          have hg := T.opening_family_unique event.x sig.val.1 tag.val.1
            sig.val.2.1 tag.val.2.1 sig.val.2.2 tag.val.2.2
            ⟨event.toRawLedgerEntry,T.usedNameEvents_ledger he,m,hs,hp⟩ hf
          have heq : sig=tag := Subtype.ext (Prod.ext hg.1 (Prod.ext hg.2.1 hg.2.2))
          exact congrArg newSlot heq

theorem RetrospectiveLeft.injective_of_eq
    {root : Formula Var} {T : SelectedTree E U owned H Er}
    {frame : SlotFrame τ N incoming}
    {newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot}
    (hnew : Function.Injective newSlot)
    (hfree : ∀sig,newSlot sig∉SlotFrame.occupied frame.role)
    {c d : Clock} {s t : Slot}
    (h : RetrospectiveLeft root T frame newSlot c s)
    (g : RetrospectiveLeft root T frame newSlot d t) (hs : s=t) : c=d := by
  classical
  cases h with
  | input c s hr =>
      cases g with
      | input d t ht =>
          rw [← hs] at ht
          exact frame.injective c d s 0 hr ht
      | opening event he m sig ht hp =>
          rw [hs] at hr
          exact False.elim (hfree sig (by
            simp only [SlotFrame.occupied,Finset.mem_filter,Finset.mem_univ,true_and]
            exact ⟨c,0,hr⟩))
  | opening event he m sig ht hp =>
      cases g with
      | input d t hr =>
          rw [← hs] at hr
          exact False.elim (hfree sig (by
            simp only [SlotFrame.occupied,Finset.mem_filter,Finset.mem_univ,true_and]
            exact ⟨d,0,hr⟩))
      | opening other ho n tag hu hq =>
          have heq := hnew hs
          subst tag
          exact T.opening_left_unique event.x other.x sig.val.1 sig.val.2.1 sig.val.2.2
            ⟨event.toRawLedgerEntry,T.usedNameEvents_ledger he,m,ht,hp⟩
            ⟨other.toRawLedgerEntry,T.usedNameEvents_ledger ho,n,hu,hq⟩

theorem RetrospectiveRole.functional_of_eq
    {root : Formula Var} {T : SelectedTree E U owned H Er}
    (hInput : SafeNormalization J (.ofState N)) {frame : SlotFrame τ N incoming}
    {newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot}
    {c d : Clock} {s t : Slot} {r q : Fin 3}
    (h : RetrospectiveRole root T frame newSlot c s r)
    (g : RetrospectiveRole root T frame newSlot d t q) (hc : c=d) : s=t ∧ r=q := by
  cases h with
  | input c s r hr =>
      cases g with
      | input d t q ht =>
          rw [← hc] at ht
          have he := Option.some.inj (hr.symm.trans ht)
          exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩
      | opening event he m sig hs hp =>
          rw [hc] at hr
          exact False.elim (event_no_input_role hInput he hr)
      | upper event he d m kind I φ hs t left =>
          rw [hc] at hr
          exact False.elim (event_no_input_role hInput he hr)
  | opening event he m sig hs hp =>
      cases g with
      | input d t q ht =>
          rw [← hc] at ht
          exact False.elim (event_no_input_role hInput he ht)
      | opening other ho n tag ht hq =>
          exact ⟨RetrospectiveLeft.functional_of_eq (frame := frame) hInput
            (.opening event he m sig hs hp) (.opening other ho n tag ht hq) hc,rfl⟩
      | upper other ho d n kind I φ ht t left =>
          have hef := T.usedNameEvents_name_injective he ho hc
          rw [← hef,hs] at ht
          cases ht
  | upper event he c m kind I φ hs s left =>
      cases g with
      | input d t q ht =>
          rw [← hc] at ht
          exact False.elim (event_no_input_role hInput he ht)
      | opening other ho n sig ht hp =>
          have hef := T.usedNameEvents_name_injective he ho hc
          rw [← hef,hs] at ht
          cases ht
      | upper other ho d n kind' I' φ' ht t right =>
          have hef := T.usedNameEvents_name_injective he ho hc
          have hsrc := hs.symm.trans ((congrArg (fun e : UsedNameEvent (Clock := Clock) (Var := Var)=>e.source) hef).trans ht)
          have hleft := (Predicate.upper.inj hsrc).1
          have hst := RetrospectiveLeft.functional_of_eq hInput left right hleft
          exact ⟨hst,congrArg (alternateRight frame.role) hst⟩

theorem RetrospectiveRole.injective_of_eq
    {root : Formula Var} {T : SelectedTree E U owned H Er}
    {frame : SlotFrame τ N incoming}
    {newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot}
    (hnew : Function.Injective newSlot)
    (hfree : ∀sig,newSlot sig∉SlotFrame.occupied frame.role)
    {c d : Clock} {s t : Slot} {r q : Fin 3}
    (h : RetrospectiveRole root T frame newSlot c s r)
    (g : RetrospectiveRole root T frame newSlot d t q) (htag : (s,r)=(t,q)) : c=d := by
  classical
  cases h with
  | input c s r hr =>
      cases g with
      | input d t q ht =>
          exact frame.injective c d s r hr (ht.trans (congrArg some htag.symm))
      | opening event he m sig hs hp =>
          have hslot : s=newSlot sig := congrArg Prod.fst htag
          rw [hslot] at hr
          exact False.elim (hfree sig (by
            simp only [SlotFrame.occupied,Finset.mem_filter,Finset.mem_univ,true_and]
            exact ⟨c,r,hr⟩))
      | upper event he d m kind I φ hs t left =>
          exact False.elim (frame.alternateRight_unused t c (hr.trans (congrArg some htag)))
  | opening event he m sig hs hp =>
      cases g with
      | input d t q ht =>
          have hslot : newSlot sig=t := congrArg Prod.fst htag
          rw [← hslot] at ht
          exact False.elim (hfree sig (by
            simp only [SlotFrame.occupied,Finset.mem_filter,Finset.mem_univ,true_and]
            exact ⟨d,q,ht⟩))
      | opening other ho n tag ht hq =>
          exact RetrospectiveLeft.injective_of_eq (frame := frame) hnew hfree
            (.opening event he m sig hs hp) (.opening other ho n tag ht hq) (congrArg Prod.fst htag)
      | upper other ho d n kind I φ ht t left =>
          exact False.elim (alternateRight_ne_zero frame.role t (congrArg Prod.snd htag).symm)
  | upper event he c m kind I φ hs s left =>
      cases g with
      | input d t q ht =>
          exact False.elim (frame.alternateRight_unused s d (ht.trans (congrArg some htag.symm)))
      | opening other ho n sig ht hp =>
          exact False.elim (alternateRight_ne_zero frame.role s (congrArg Prod.snd htag))
      | upper other ho d n kind' I' φ' ht t right =>
          have hleft := RetrospectiveLeft.injective_of_eq hnew hfree left right (congrArg Prod.fst htag)
          have hraw := T.rawLedger_same_left_unique event.toRawLedgerEntry other.toRawLedgerEntry c
            (T.usedNameEvents_ledger he) (T.usedNameEvents_ledger ho)
            (by simp [RawLedgerEntry.leftClock,hs])
            (by simp [RawLedgerEntry.leftClock,ht,← hleft])
          exact event.same_entry_name other hraw

end STLTableau.Section4.Finiteness
