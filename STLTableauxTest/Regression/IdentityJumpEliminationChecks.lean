import STLTableaux.Automata.Execution.IdentityJumpElimination

open STLTableau.Section4

namespace ResetRegression
open STLTableau

def incoming : EdgeLabel Unit := ⟨∅, Set.finite_empty, ClockResetSet.empty⟩
def resetOne : EdgeLabel Unit :=
  ⟨∅, Set.finite_empty, ClockResetSet.singleton () 1⟩
def α : ClockValuation Unit := fun _ => 0
def β : ClockValuation Unit := fun _ => 1

-- Repeating the mode does not suffice: removing its reset changes the
-- valuation passed to the continuation, even when the guard is empty.
theorem reset_changes_witness :
    (Path.step incoming () (.last resetOne ())).JumpGuardsHold α β ∧
      ¬ ((Path.last resetOne ()).withFirstIncoming incoming).JumpGuardsHold α β := by
  constructor
  · constructor
    · intro g hg
      exact hg.elim
    · change β = resetOne.resets.apply α
      funext c
      cases c
      simp [resetOne, ClockResetSet.apply, ClockResetSet.singleton, β]
  · intro he
    change β = α at he
    have hv := congrFun he ()
    norm_num [α, β] at hv

end ResetRegression

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Path.withFirstIncoming_firstState, ``Path.withFirstIncoming_firstIncoming,
      ``Path.withFirstIncoming_lastState, ``Path.withFirstIncoming_valid,
      ``Path.drop_duplicate_run, ``Path.drop_duplicate_accepting,
      ``Path.withFirstIncoming_jumpGuardsHold, ``Path.drop_first_jump_guards,
      ``Path.drop_duplicate_guarded_run,
      ``Tableau.reset_empty, ``Tableau.identity_jump_endpoints,
      ``Tableau.reset_fixes_of_clockCompatible, ``Tableau.fixed_reset_jump_endpoints,
      ``Tableau.jump_block_erase_identity, ``ResetRegression.reset_changes_witness] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
