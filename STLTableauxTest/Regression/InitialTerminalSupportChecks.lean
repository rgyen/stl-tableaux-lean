import STLTableaux.Automata.Translation.InitialTerminalSupport

open STLTableau.Section4.Finiteness

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``normalize_noCurrentTerminal, ``finite_branch_noCurrentTerminal,
      ``infinite_branch_noCurrentTerminal, ``RawBranch.noCurrentTerminal,
      ``ACIdem.noCurrentTerminal_iff, ``noCurrentTerminal_withBoundaryGuard,
      ``Resolve.noCurrentTerminal, ``alpha_current_terminal_iff,
      ``mixed_branch_no_terminal, ``contextual_branch_no_terminal,
      ``closure_no_terminal, ``derives_no_terminal,
      ``finiteRootTableau_initial_nonterminal,
      ``finiteRootTableau_execution_initial_nonterminal,
      ``finiteRootTableau_terminal_acceptance_exhausts] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
