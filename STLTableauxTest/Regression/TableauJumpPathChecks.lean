import STLTableaux.Automata.Recognition.TableauJumpPath

open STLTableau STLTableau.Section4

-- An empty jump block leaves the post-entry valuation unchanged, regardless of
-- the incoming label that has already been applied outside this block.
example {Clock State : Type*} (l : EdgeLabel Clock) (s : State)
    (α β : ClockValuation Clock) :
    (Path.last l s).JumpGuardsHold α β ↔ β = α := Iff.rfl

-- The tail is evaluated after the next incoming reset, not at the original
-- valuation and not after any positive time elapse.
example {Clock State : Type*} (l l' : EdgeLabel Clock) (s s' : State)
    (α β : ClockValuation Clock) :
    (Path.step l s (.last l' s')).JumpGuardsHold α β ↔
      (∀ g ∈ l'.guards, g.holds α) ∧ β = l'.resets.apply α := Iff.rfl

example {Clock State : Type*} (l₀ l₁ l₂ : EdgeLabel Clock) (s₀ s₁ s₂ : State)
    (α β : ClockValuation Clock) :
    (Path.step l₀ s₀ (.step l₁ s₁ (.last l₂ s₂))).JumpGuardsHold α β ↔
      (∀ g ∈ l₁.guards, g.holds α) ∧
      (∀ g ∈ l₂.guards, g.holds (l₁.resets.apply α)) ∧
      β = l₂.resets.apply (l₁.resets.apply α) := Iff.rfl

-- Overlapping assignments need NOT be consistent across successive jumps.
-- The second guard sees 0 from the first jump, even though the final reset
-- overwrites that clock with 1. It sees neither the entry value 2 nor final 1.
private def resetZero : EdgeLabel Unit :=
  ⟨∅, Set.finite_empty, ClockResetSet.singleton () 0⟩

private def checkZeroResetOne : EdgeLabel Unit :=
  ⟨{⟨(), .eq, 0⟩}, Set.finite_singleton _, ClockResetSet.singleton () 1⟩

private def overwritePath : Path Unit Unit :=
  .step resetZero () (.step resetZero () (.last checkZeroResetOne ()))

private theorem overwritePath_valid_checks :
    overwritePath.JumpGuardsHold (fun _ => 2) (fun _ => 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    exact (Set.notMem_empty g hg).elim
  · intro g hg
    have he : g = ⟨(), .eq, 0⟩ := Set.mem_singleton_iff.mp hg
    subst g
    rfl
  · funext c
    cases c
    rfl

example : overwritePath.resetGuardChecks ClockResetSet.empty :=
  ((overwritePath.jumpGuardsHold_iff_summary ClockResetSet.empty
    (fun _ => 2) (fun _ => 1)).mp overwritePath_valid_checks).2.1

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Tableau.guardedClockSteps_path, ``Tableau.discreteSteps_guarded_path,
      ``Path.jumpGuardsHold_iff_summary, ``Tableau.discreteSteps_guarded_summary] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
