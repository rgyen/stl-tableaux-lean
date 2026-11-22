import STLTableaux.Finiteness.Derivation.Selection.SelectedAnnotationProvenance
open STLTableau.Section4.Finiteness
#check RawConstantsWithin.guard
#print axioms RawConstantsWithin.guard
#check RawConstantsWithin.reset
#print axioms RawConstantsWithin.reset
#check RawBranch.guard_constant
#print axioms RawBranch.guard_constant
#check RawBranch.reset_constant
#print axioms RawBranch.reset_constant
#check RawLedgerEntry.guard_constant
#print axioms RawLedgerEntry.guard_constant
#check RawLedgerEntry.reset_constant
#print axioms RawLedgerEntry.reset_constant
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``RawConstantsWithin.guard, ``RawConstantsWithin.reset, ``RawBranch.guard_constant, ``RawBranch.reset_constant, ``RawLedgerEntry.guard_constant, ``RawLedgerEntry.reset_constant] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
