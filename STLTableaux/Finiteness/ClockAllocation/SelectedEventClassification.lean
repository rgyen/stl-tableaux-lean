import STLTableaux.Finiteness.ClockAllocation.SelectedNameEvents
import STLTableaux.Finiteness.Derivation.Branches.BranchBoundedSupport

/-! Classifies fresh clocks that occur in the chosen branch. Expanding a
two-clock predicate introduces no such clock. An unclocked predicate introduces
one only when opening a timed subformula. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

namespace UsedNameEvent

theorem not_bounded (e : UsedNameEvent (Clock := Clock) (Var := Var))
    (c d : Clock) (m r : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    e.source≠.bounded c d m r kind I φ := by
  intro hs
  have hx := e.actual.bounded_whole_support c d m r kind I φ hs e.used
  apply e.not_source
  simpa only [hs,syntaxClocks] using hx

/-- A fresh clock used by a branch for an unclocked predicate is reset when the
branch opens a timed subformula. -/
theorem plain_opening (e : UsedNameEvent (Clock := Clock) (Var := Var))
    (φ : Formula Var) (hs : e.source=.plain φ) :
    ∃m kind I ψ,φ=timedFormula kind I ψ ∧
      e.body=.reset (ClockResetSet.singleton e.x 0)
        (.conj (.predicate (.upper e.x m kind I ψ)) (.marker m)) := by
  rcases e.actual.plain_opening_or_empty ⟨φ,hs⟩ with hempty | ⟨c,m,kind,I,ψ,hp,hB⟩
  · have hx := e.used
    rw [hempty] at hx
    cases hx
  · have hc : c=e.x := by
      have hx := e.used
      rw [hB] at hx
      have hx' : e.x=c := by simpa [syntaxClocks] using hx
      exact hx'.symm
    subst c
    exact ⟨m,kind,I,ψ,Predicate.plain.inj (hs.symm.trans hp),hB⟩

/-- A raw branch uses at most one clock absent from its source predicate. -/
theorem same_entry_name (e f : UsedNameEvent (Clock := Clock) (Var := Var))
    (he : e.toRawLedgerEntry=f.toRawLedgerEntry) : e.x=f.x := by
  have hbody : e.body=f.body := congrArg RawLedgerEntry.body he
  have hsource : e.source=f.source := congrArg RawLedgerEntry.source he
  have hx : e.x∈syntaxClocks f.body := hbody ▸ e.used
  rcases f.actual.syntaxClocks_subset_source_union_singleton f.x f.reset_support hx with hs | hx
  · exact False.elim (e.not_source (hsource ▸ hs))
  · exact hx

/-- Every genuine producer is either a timed opening or an upper expansion. -/
theorem opening_or_upper (e : UsedNameEvent (Clock := Clock) (Var := Var)) :
    (∃m kind I φ,e.source=.plain (timedFormula kind I φ) ∧
      e.body=.reset (ClockResetSet.singleton e.x 0)
        (.conj (.predicate (.upper e.x m kind I φ)) (.marker m))) ∨
    (∃c m kind I φ,e.source=.upper c m kind I φ) := by
  cases hs : e.source with
  | plain φ =>
    obtain ⟨m,kind,I,ψ,hφ,hB⟩ := e.plain_opening φ hs
    exact Or.inl ⟨m,kind,I,ψ,congrArg Predicate.plain hφ,hB⟩
  | upper c m kind I φ => exact Or.inr ⟨c,m,kind,I,φ,rfl⟩
  | bounded c d m r kind I φ => exact False.elim (e.not_bounded c d m r kind I φ hs)
end UsedNameEvent
end STLTableau.Section4.Finiteness
