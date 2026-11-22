import STLTableaux.Finiteness.Derivation.DerivationRelation

open STLTableau.Section4.Finiteness

#check Derives.original
#check Derives.resolved
#check derives_localLaws
#check derives_formula_of_recognizes
#check derives_fullTrace_and_root
#print axioms derives_localLaws
#print axioms derives_formula_of_recognizes
#print axioms derives_fullTrace_and_root

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``derives_localLaws, ``derives_formula_of_recognizes,
      ``derives_fullTrace_and_root] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
