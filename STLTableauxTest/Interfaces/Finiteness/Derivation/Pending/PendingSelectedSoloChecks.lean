import STLTableaux.Finiteness.Derivation.Pending.PendingSelectedSolo

open STLTableau.Section4.Finiteness
#check owned_selected_solo_weight
#check exists_ordinary_child_solo_of_input
#print axioms owned_selected_solo_weight
#print axioms exists_ordinary_child_solo_of_input

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``owned_selected_solo_weight, ``exists_ordinary_child_solo_of_input] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
