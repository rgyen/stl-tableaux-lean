import STLTableaux.Automata.Recognition.TraceClockSchedule

open STLTableau STLTableau.Section4

-- The second frame may be terminal (k + 1 = P.size). Its guard valuation
-- includes both the first reset and the duration, not merely the reset.
example {Clock Var : Type*} (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (S U : STLTableau.Section3.StateForm Clock Var) (α : ClockValuation Clock)
    (k : Judgement.Position P) (hk : k.val < P.size)
    (hgS : ∀ g ∈ S.guards, g.holds α)
    (hlS : ∀ l ∈ S.locals, l.holds σ P (S.resets.apply α) k)
    (hgU : ∀ g ∈ U.guards,
      g.holds (ClockResetSet.elapse (S.resets.apply α) (Judgement.duration P ⟨k.val, hk⟩)))
    (hlU : ∀ l ∈ U.locals, l.holds σ P
      (U.resets.apply (ClockResetSet.elapse (S.resets.apply α)
        (Judgement.duration P ⟨k.val, hk⟩))) ⟨k.val + 1, by omega⟩) :
    (Trace.step S (.last U)).holds σ P α k := by
  let β := ClockResetSet.elapse (S.resets.apply α) (Judgement.duration P ⟨k.val, hk⟩)
  let ν : ℕ → ClockValuation Clock := fun n => if n = 0 then α else β
  apply Trace.holdsWith_of_clock_schedule STLTableau.Section3.StateForm.locals σ P
    (.step S (.last U)) ν k (by change k.val + 2 ≤ P.size + 1; omega)
  · intro i
    fin_cases i
    · exact hgS
    · exact hgU
  · intro i
    fin_cases i
    · exact hlS
    · exact hlU
  · intro i hi
    fin_cases i
    · rfl
    · simp [Trace.length] at hi

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for ax in ← Lean.collectAxioms ``Trace.holdsWith_of_clock_schedule do
    unless allowed.contains ax do
      throwError "Trace.holdsWith_of_clock_schedule uses unapproved axiom {ax}"
