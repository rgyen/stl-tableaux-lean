import STLTableaux.Automata.Recognition.ExecutionObservedJumpBlock

open STLTableau STLTableau.Section4

#check Tableau.prepend_observed_discrete_block
#check Tableau.prepend_observed_nonempty_discrete_block
#check Tableau.prepend_beforeFlow_discrete_block

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Tableau.prepend_observed_discrete_block,
      ``Tableau.prepend_observed_nonempty_discrete_block,
      ``Tableau.prepend_beforeFlow_discrete_block] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
