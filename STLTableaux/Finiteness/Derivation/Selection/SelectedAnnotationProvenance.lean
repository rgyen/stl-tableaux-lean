import STLTableaux.Finiteness.Derivation.Selection.SelectedConstantProvenance
import STLTableaux.Finiteness.Derivation.Selection.SelectedLedger

/-! Clock-labelled literal annotations of actual selected ledger entries.
 This does not supply a consistent temporal-family assignment for clock names. -/
namespace STLTableau.Section4.Finiteness
open Section3 Finiteness
variable {Clock Var : Type*}

def RawGuardAt (c : Clock) (a : NNReal) : MixedJ Clock Var → Prop
  | .clock d _ b => c=d ∧ a=b
  | .conj J K => RawGuardAt c a J ∨ RawGuardAt c a K
  | .reset _ J | .next J => RawGuardAt c a J
  | _ => False

def RawResetAt (c : Clock) (a : NNReal) : MixedJ Clock Var → Prop
  | .reset R J => R.value c=some a ∨ RawResetAt c a J
  | .conj J K => RawResetAt c a J ∨ RawResetAt c a K
  | .next J => RawResetAt c a J
  | _ => False

theorem RawConstantsWithin.guard {C : Finset NNReal} {J : MixedJ Clock Var}
    (h : RawConstantsWithin C J) {c a} (ha : RawGuardAt c a J) : a∈C := by
  induction J with
  | terminal | marker | predicate => cases ha
  | clock d r b => exact ha.2 ▸ h
  | next J ih => exact ih h ha
  | reset R J ih => exact ih h.2 ha
  | conj J K ih ik =>
      rcases ha with ha | ha
      · exact ih h.1 ha
      · exact ik h.2 ha

theorem RawConstantsWithin.reset {C : Finset NNReal} {J : MixedJ Clock Var}
    (h : RawConstantsWithin C J) {c a} (ha : RawResetAt c a J) : a∈C := by
  induction J with
  | terminal | marker | predicate | clock => cases ha
  | next J ih => exact ih h ha
  | reset R J ih =>
      rcases ha with ha | ha
      · exact h.1 c a ha
      · exact ih h.2 ha
  | conj J K ih ik =>
      rcases ha with ha | ha
      · exact ih h.1 ha
      · exact ik h.2 ha

variable [DecidableEq Clock]

theorem RawBranch.guard_constant {p : Predicate Clock Var} {B : MixedJ Clock Var}
    (h : RawBranch p B) {c a} (ha : RawGuardAt c a B) : a∈branchConstants p :=
  h.raw_constants.guard ha

theorem RawBranch.reset_constant {p : Predicate Clock Var} {B : MixedJ Clock Var}
    (h : RawBranch p B) {c a} (ha : RawResetAt c a B) : a∈branchConstants p :=
  h.raw_constants.reset ha

/-- The same clock and actual source-bearing ledger entry are retained. -/
theorem RawLedgerEntry.guard_constant (entry : RawLedgerEntry (Clock := Clock) (Var := Var))
    {c a} (ha : RawGuardAt c a entry.body) : a∈branchConstants entry.source :=
  entry.actual.guard_constant ha

theorem RawLedgerEntry.reset_constant (entry : RawLedgerEntry (Clock := Clock) (Var := Var))
    {c a} (ha : RawResetAt c a entry.body) : a∈branchConstants entry.source :=
  entry.actual.reset_constant ha

end STLTableau.Section4.Finiteness
