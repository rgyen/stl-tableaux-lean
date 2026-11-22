import STLTableaux.Finiteness.Derivation.Pending.PendingComplexityBarrier
open STLTableau.Section4.Finiteness
#print axioms plain_timed_above_upper
#print axioms plain_timed_above_bounded
#print axioms RawBranch.plain_timed_producer_above
#print axioms RawBranch.no_plain_timed_of_le_upper
#print axioms maximal_no_plain_timed
#print axioms maximal_replacement_no_plain_timed
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``plain_timed_above_upper, ``plain_timed_above_bounded,
      ``RawBranch.plain_timed_producer_above, ``RawBranch.no_plain_timed_of_le_upper, ``maximal_no_plain_timed,
      ``maximal_replacement_no_plain_timed] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
