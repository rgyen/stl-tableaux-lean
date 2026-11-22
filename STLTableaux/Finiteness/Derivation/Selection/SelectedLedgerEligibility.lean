import STLTableaux.Finiteness.Derivation.Selection.SelectedLedger

/-! Ordinary expansion sources lie outside the set eligible for boundary
merging. This includes the `↑` form in the optional boundary branch. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

theorem SelectedTree.ledger_source_not_eligible
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    {entry : RawLedgerEntry (Clock := Clock) (Var := Var)} (he : entry ∈ T.rawLedger) :
    entry.source ∉ E := by
  induction T with
  | zero => cases he
  | ordinary owned choice tail ih =>
    rcases List.mem_cons.mp he with rfl | ht
    · exact choice.allowed.1
    · exact ih ht
  | required owned choice tail ih => exact ih he
  | optional owned choice upper forced tail ih =>
    rcases List.mem_cons.mp he with rfl | ht
    · exact upper.allowed.1
    · exact ih ht
end STLTableau.Section4.Finiteness
