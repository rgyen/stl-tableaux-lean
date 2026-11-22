import STLTableaux.Finiteness.Derivation.Derivation

open STLTableau.Section4.Finiteness

#check RawBranch
#check RawBranch.sound
#check Resolve
#check Resolve.expandCtx
#check Resolve.Evaluated
#check Resolve.recover
#check FrozenByUpper.defer
#print axioms RawBranch.sound
#print axioms ACIdem.holds_iff
#print axioms Resolve.recover
#print axioms FrozenByUpper.defer

#check Resolve.nonPredicate_recover
#check withBoundaryGuard
#print axioms Resolve.nonPredicate_recover
#print axioms withBoundaryGuard_holds

#check Resolve.expandSolo
#check Resolve.atomic_plainAnd
#print axioms Resolve.atomic_plainAnd

#check FrozenOccurrence.check
#check FrozenByUpper.check
#print axioms FrozenByUpper.check

#check StructuralEq
#check ACIdem.resetDistrib
#check ACIdem.resetUnused
#check ACIdem.resetNested
#check ACIdem.gather_reset_right
#check ACIdem.split_consistent_resets
#print axioms ACIdem.gather_reset_right
#print axioms ACIdem.split_consistent_resets
