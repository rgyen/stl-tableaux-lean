import STLTableaux.Automata.Recognition.TableauClockValuations
import STLTableaux.Closure.Residual.BranchNormalization

/-! Extract one structural path and its sequential guarded clock witness from
a zero-time jump block. These paths do not yet carry partition positions. -/
namespace STLTableau.Section4
variable {Clock Var State : Type*}

namespace Path

/-- The starting valuation is after the first incoming reset. Each subsequent
incoming guard/reset is checked in order, without elapse. The first incoming
label is supplied by the surrounding execution, not rechecked here. -/
def JumpGuardsHold (α β : ClockValuation Clock) : Path Clock State → Prop
  | .last _ _ => β = α
  | .step _ _ p => (∀ g ∈ p.firstIncoming.guards, g.holds α) ∧
      p.JumpGuardsHold (p.firstIncoming.resets.apply α) β

/-- Accumulate resets in execution order: a later assignment overwrites an
earlier one. The first incoming label has already been processed. -/
def resetsAfter (R : ClockResetSet Clock) : Path Clock State → ClockResetSet Clock
  | .last _ _ => R
  | .step _ _ p => p.resetsAfter (p.firstIncoming.resets.union R)

/-- Guards whose clocks have not yet been reset are tested at block entry. -/
def entryGuards (R : ClockResetSet Clock) (α : ClockValuation Clock) :
    Path Clock State → Prop
  | .last _ _ => True
  | .step _ _ p =>
      (∀ g ∈ p.firstIncoming.guards, R.value g.clock = none → g.holds α) ∧
      p.entryGuards (p.firstIncoming.resets.union R) α

/-- Guards on previously reset clocks are constant tests, using the latest
assignment BEFORE the current jump, not that jump's own reset. -/
def resetGuardChecks (R : ClockResetSet Clock) : Path Clock State → Prop
  | .last _ _ => True
  | .step _ _ p =>
      (∀ g ∈ p.firstIncoming.guards, ∀ a, R.value g.clock = some a →
        g.relation.Holds a g.bound) ∧
      p.resetGuardChecks (p.firstIncoming.resets.union R)

/-- Exact arithmetic summary of a zero-time block. No consistency between
successive resets is needed. This does not assert a shortcut tableau edge. -/
theorem jumpGuardsHold_iff_summary (p : Path Clock State)
    (R : ClockResetSet Clock) (α β : ClockValuation Clock) :
    p.JumpGuardsHold (R.apply α) β ↔
      p.entryGuards R α ∧ p.resetGuardChecks R ∧
        β = (p.resetsAfter R).apply α := by
  induction p generalizing R with
  | last l s => simp [JumpGuardsHold, entryGuards, resetGuardChecks, resetsAfter]
  | step l s p ih =>
    have hg : (∀ g ∈ p.firstIncoming.guards, g.holds (R.apply α)) ↔
        (∀ g ∈ p.firstIncoming.guards, R.value g.clock = none → g.holds α) ∧
        (∀ g ∈ p.firstIncoming.guards, ∀ a, R.value g.clock = some a →
          g.relation.Holds a g.bound) := by
      constructor
      · intro h
        constructor
        · intro g hm hn
          simpa only [Section3.Guard.holds, ClockResetSet.apply, hn] using h g hm
        · intro g hm a ha
          simpa only [Section3.Guard.holds, ClockResetSet.apply, ha] using h g hm
      · rintro ⟨hn, hs⟩ g hm
        cases he : R.value g.clock with
        | none =>
          simpa only [Section3.Guard.holds, ClockResetSet.apply, he] using hn g hm he
        | some a =>
          simpa only [Section3.Guard.holds, ClockResetSet.apply, he] using hs g hm a he
    simp only [JumpGuardsHold, entryGuards, resetGuardChecks, resetsAfter,
      ← ClockResetSet.apply_union_eq_comp, ih, hg]
    tauto

end Path

namespace Tableau
variable (T : Tableau Clock Var State)

/-- The same path witnesses graph validity and all sequential guard/reset
checks. This does not replace the trace's position-advancing next operator. -/
theorem guardedClockSteps_path
    {a b : T.states × ClockValuation Clock}
    (hp : Relation.ReflTransGen T.GuardedClockStep a b)
    (incoming : EdgeLabel Clock) :
    ∃ p : Path Clock State, p.valid T ∧ p.firstState = a.1.val ∧
      p.firstIncoming = incoming ∧ p.lastState = b.1.val ∧
      p.JumpGuardsHold a.2 b.2 := by
  induction hp using Relation.ReflTransGen.head_induction_on generalizing incoming with
  | refl => exact ⟨.last incoming _, b.1.property, rfl, rfl, rfl, rfl⟩
  | @head a c hac _ ih =>
    obtain ⟨l, he, hg, hc⟩ := hac
    obtain ⟨p, hv, hf, hi, hl, hguards⟩ := ih l
    refine ⟨.step incoming a.1.val p, ⟨a.1.property, hv, ?_⟩,
      rfl, rfl, hl, ?_⟩
    · simpa only [hf, hi] using he
    · change (∀ g ∈ p.firstIncoming.guards, g.holds a.2) ∧
        p.JumpGuardsHold (p.firstIncoming.resets.apply a.2) b.2
      rw [hi]
      exact ⟨hg, hc ▸ hguards⟩

/-- Actual jump-block extraction keeps a single path and its guard valuations
together, including all intervening resets. Starting compatibility is explicit. -/
theorem discreteSteps_guarded_path
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {s s' : (T.toAutomaton h τ hτ).State} {α : ClockValuation Clock}
    (hj : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep s s')
    (hv : T.ClockCompatible s.val.2 α) (incoming : EdgeLabel Clock) :
    ∃ (β : ClockValuation Clock) (p : Path Clock State),
      T.ClockCompatible s'.val.2 β ∧ p.valid T ∧
      p.firstState = s.val.1.val ∧ p.firstIncoming = incoming ∧
      p.lastState = s'.val.1.val ∧ p.JumpGuardsHold α β := by
  obtain ⟨β, hb, hsteps⟩ := T.discreteSteps_guardedClockSteps h τ hτ hj hv
  obtain ⟨p, hp⟩ := T.guardedClockSteps_path hsteps incoming
  exact ⟨β, p, hb, hp⟩

/-- An actual jump block supplies the arithmetic summary on the SAME valid
path. The resulting reset map describes clocks, not a new graph edge. -/
theorem discreteSteps_guarded_summary
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {s s' : (T.toAutomaton h τ hτ).State} {α : ClockValuation Clock}
    (hj : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep s s')
    (hv : T.ClockCompatible s.val.2 α) (incoming : EdgeLabel Clock) :
    ∃ p : Path Clock State, p.valid T ∧
      p.firstState = s.val.1.val ∧ p.firstIncoming = incoming ∧
      p.lastState = s'.val.1.val ∧
      p.entryGuards ClockResetSet.empty α ∧
      p.resetGuardChecks ClockResetSet.empty ∧
      T.ClockCompatible s'.val.2 ((p.resetsAfter ClockResetSet.empty).apply α) := by
  obtain ⟨β, p, hb, hp, hf, hi, hl, hg⟩ :=
    T.discreteSteps_guarded_path h τ hτ hj hv incoming
  obtain ⟨he, hc, hr⟩ :=
    (p.jumpGuardsHold_iff_summary ClockResetSet.empty α β).mp hg
  exact ⟨p, hp, hf, hi, hl, he, hc, hr ▸ hb⟩

end Tableau
end STLTableau.Section4
