import STLTableaux.Finiteness.Derivation.DerivationNormalizationSoundness

open STLTableau.Section4.Finiteness

#check SafeNormalization
#check SafeNormalization.normalizes
#check SafeNormalization.holds
#check SafeNormalization.numeric
#check SafeNormalization.nonPredicate
#check SafeNormalization.ready
#check normalize_ready_iff
#check SafeNormalization.underReset_pair
#check SafeNormalization.paired_reset
#check SafeNormalization.nested_pair_reset
#check unsafe_resolve_normalization
#print axioms SafeNormalization.holds
#print axioms SafeNormalization.numeric
#print axioms SafeNormalization.nonPredicate
#print axioms normalize_ready_iff
#print axioms SafeNormalization.nested_pair_reset
#print axioms unsafe_resolve_normalization
