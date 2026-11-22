import STLTableaux.Finiteness.Derivation.Selection.SelectedRetainedPredicates
open STLTableau.Section4.Finiteness
#print axioms SelectedTree.retained_nonatomic_iff
#print axioms SelectedTree.normalized_retained_nonatomic_iff
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SelectedTree.retained_nonatomic_iff, ``SelectedTree.normalized_retained_nonatomic_iff] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
