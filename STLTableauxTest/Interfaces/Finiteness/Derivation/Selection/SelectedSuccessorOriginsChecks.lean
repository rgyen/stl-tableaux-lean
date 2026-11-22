import STLTableaux.Finiteness.Derivation.Selection.SelectedSuccessorOrigins
open STLTableau.Section4.Finiteness
#check InputOrigins.successor_origins
#check InputOrigins.nonempty_origin_step
#print axioms InputOrigins.successor_origins
#print axioms InputOrigins.nonempty_origin_step
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``InputOrigins.successor_origins, ``InputOrigins.nonempty_origin_step] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
