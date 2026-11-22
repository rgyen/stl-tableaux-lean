import STLTableaux.Automata.Translation.TableauAutomata

open STLTableau.Section4.Tableau

-- Include the definitions themselves: construction must not hide axioms.
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``baseAutomaton, ``toAutomaton,
      ``reset_globalClock, ``reset_realVariable,
      ``realComparison_coe, ``guardsHold_iff, ``reset_clock_agrees, ``atomHolds_iff,
      ``initial_globalClock_zero, ``jump_globalClock_preserved,
      ``jump_realVariable_preserved, ``nonterminal_entry_lt_horizon,
      ``flow_globalClock, ``terminal_entry_eq_horizon,
      ``discreteSteps_globalClock_preserved, ``continuousStep_globalClock,
      ``execution_final_clock_eq_last_finish] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
