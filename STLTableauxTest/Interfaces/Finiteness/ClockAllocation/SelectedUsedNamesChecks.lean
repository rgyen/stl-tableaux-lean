import STLTableaux.Finiteness.ClockAllocation.SelectedUsedNames
open STLTableau.Section4.Finiteness
#check SelectedTree.usedFreshClocks_outside
#check SelectedTree.usedFreshClocks_nodup
#print axioms SelectedTree.usedFreshClocks_outside
#print axioms SelectedTree.usedFreshClocks_nodup
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SelectedTree.usedFreshClocks_outside, ``SelectedTree.usedFreshClocks_nodup, ``SelectedTree.used_syntax_clock_support,
    ``SelectedTree.used_normalized_clock_support] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
