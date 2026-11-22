import STLTableaux.Finiteness.ClockAllocation.SelectedUpperLeftOrigin
import STLTableaux.Finiteness.Bounds.SelectedRetainedCount
import STLTableaux.Finiteness.ClockAllocation.SelectedNameEvents

/-! Each timed subformula introduces at most one fresh left clock in a
selected derivation. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

/-- Two actual plain-ledger events for the same source formula are identical. -/
theorem SelectedTree.plain_ledger_event_unique
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    (e f : RawLedgerEntry (Clock := Clock) (Var := Var)) (φ : Formula Var)
    (he : e∈T.rawLedger) (hf : f∈T.rawLedger)
    (hs : e.source=.plain φ) (ht : f.source=.plain φ) : e=f :=
  LedgerList.filterMap_fiber_unique RawLedgerEntry.plainFormula T.rawLedger
    (T.plainConsumed_nodup.sublist T.plain_ledger_sublist) (v:=φ) he hf
    (by simp [RawLedgerEntry.plainFormula,hs]) (by simp [RawLedgerEntry.plainFormula,ht])

/-- The same actual family cannot open two distinct left owners. -/
theorem SelectedTree.opening_left_unique
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    (c d : Clock) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hc : ledgerOpeningLeft T.rawLedger c kind I φ)
    (hd : ledgerOpeningLeft T.rawLedger d kind I φ) : c=d := by
  obtain ⟨e,he,m,hs,hp⟩ := hc
  obtain ⟨f,hf,r,ht,hq⟩ := hd
  have hef := T.plain_ledger_event_unique e f (timedFormula kind I φ) he hf hs ht
  subst f
  exact (Predicate.upper.inj (e.actual.current_upper_unique c m kind I φ d r kind I φ hp hq)).1

/-- A genuinely generated opening name cannot belong to two distinct temporal
families. This uses actual used-name producer uniqueness, not plain-source privacy. -/
theorem SelectedTree.opening_family_unique
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) (c : Clock)
    (kind kind' : TemporalKind) (I I' : TimeInterval) (φ φ' : Formula Var)
    (hc : ledgerOpeningLeft T.rawLedger c kind I φ)
    (hd : ledgerOpeningLeft T.rawLedger c kind' I' φ') :
    kind=kind' ∧I=I' ∧φ=φ' := by
  obtain ⟨e,he,m,_,hp⟩ := hc
  obtain ⟨f,hf,r,_,hq⟩ := hd
  obtain ⟨a,ha,hae,hac⟩ := T.opening_name_producer he c m kind I φ hp
  obtain ⟨b,hb,hbf,hbc⟩ := T.opening_name_producer hf c r kind' I' φ' hq
  have hab := T.usedNameEvents_name_injective ha hb (hac.trans hbc.symm)
  have hef : e=f := hae.symm.trans ((congrArg UsedNameEvent.toRawLedgerEntry hab).trans hbf)
  have hbody : e.body=f.body := congrArg RawLedgerEntry.body hef
  rw [←hbody] at hq
  obtain ⟨_,_,hk,hI,hφ⟩ := Predicate.upper.inj
    (e.actual.current_upper_unique c m kind I φ c r kind' I' φ' hp hq)
  exact ⟨hk,hI,hφ⟩
end STLTableau.Section4.Finiteness
