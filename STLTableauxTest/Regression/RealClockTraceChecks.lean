import STLTableaux.Automata.Recognition.RealClockTrace

open STLTableau STLTableau.Section4

namespace NegativeClockRegression
def guard : Section3.Guard Unit := ⟨(), .ge, 0⟩
def resetFrame (Var : Type*) : Section3.StateForm Unit Var :=
  ⟨∅, Set.finite_empty, ClockResetSet.singleton () 0, ∅, Set.finite_empty⟩
def checkFrame (Var : Type*) : Section3.StateForm Unit Var :=
  ⟨{guard}, Set.finite_singleton _, ClockResetSet.empty, ∅, Set.finite_empty⟩

-- The real clock starts negative. A reset before its first guard makes
-- transfer valid for every initial NNReal valuation, not just zero.
theorem negative_initial_clock_allowed {Var : Type*} (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (hk : 0 < P.size) :
    ∀ α : ClockValuation Unit,
      (Trace.step (resetFrame Var) (.last (checkFrame Var))).holds σ P α ⟨0, by omega⟩ := by
  apply Trace.forall_holds_of_closed_realGuards σ P _ (fun _ => -7) ⟨0, by omega⟩
    (by change 0 + 2 ≤ P.size + 1; omega)
  · ext c
    cases c
    simp [Trace.freeClocks, resetFrame, checkFrame, guard, Section3.StateForm.freeClocks,
      Section3.StateForm.guardClocks, Section3.StateForm.localClocks,
      ClockResetSet.clocks, ClockResetSet.singleton]
    exact ⟨0, rfl⟩
  · refine ⟨?_, ?_⟩
    · intro g hg
      exact hg.elim
    · simp only [Trace.realGuardsHold, dif_pos hk]
      intro g hg
      have he : g = guard := hg
      subst g
      simp [guard, resetFrame, Tableau.realComparison, Trace.realReset, ClockResetSet.singleton]
  · intro i β l hl
    fin_cases i <;> exact hl.elim

end NegativeClockRegression

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Trace.realGuardsHold_of_schedule,
      ``Trace.holds_of_realGuards, ``Trace.forall_holds_of_closed_realGuards,
      ``NegativeClockRegression.negative_initial_clock_allowed] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
