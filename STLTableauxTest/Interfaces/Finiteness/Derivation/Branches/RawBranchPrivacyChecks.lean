import STLTableaux.Finiteness.Derivation.Branches.RawBranchPrivacy

open STLTableau.Section4.Finiteness
#check RawBranch.current_private
#check RawBranch.next_private
#check ACIdem.nextPrivate_iff
#check ACIdem.nextSyntaxClocks_eq
#check RawBranch.current_next_private
#print axioms RawBranch.current_private
#print axioms RawBranch.next_private
#print axioms ACIdem.nextPrivate_iff
#print axioms ACIdem.nextSyntaxClocks_eq
#print axioms RawBranch.current_next_private

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``RawBranch.current_private, ``RawBranch.next_private,
      ``ACIdem.nextPrivate_iff, ``ACIdem.nextSyntaxClocks_eq,
      ``RawBranch.current_next_private] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
