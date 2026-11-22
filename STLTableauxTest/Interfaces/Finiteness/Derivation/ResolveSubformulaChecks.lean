import STLTableaux.Finiteness.Derivation.ResolveSubformula
open STLTableau.Section4.Finiteness
#print axioms RawBranch.subformula
#print axioms Resolve.subformula_confinement
#print axioms Derives.formulas_below
#print axioms Derives.current_formula_below
#print axioms Derives.next_formula_below
#print axioms Derives.run_formulas_below
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``RawBranch.subformula, ``Resolve.subformula_confinement, ``Derives.formulas_below,
      ``Derives.current_formula_below, ``Derives.next_formula_below, ``Derives.run_formulas_below] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
