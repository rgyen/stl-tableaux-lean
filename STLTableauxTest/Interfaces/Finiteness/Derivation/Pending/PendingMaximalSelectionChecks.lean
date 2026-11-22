import STLTableaux.Finiteness.Derivation.Pending.PendingMaximalSelection
open STLTableau.Section4.Finiteness
#check owned_select_maximal
#check maximal_raw_branch_replacement
#print axioms owned_select_maximal
#print axioms maximal_raw_branch_replacement
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``owned_select_maximal, ``maximal_raw_branch_replacement] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
