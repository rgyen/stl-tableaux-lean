import STLTableaux.Finiteness.Derivation.Pending.PendingComplexity

open STLTableau.Section4.Finiteness

#check pendingWeight
#check RawBranch.current_width
#check RawBranch.current_smaller
#check RawBranch.pendingWeight_lt_source
#check RawBranch.pendingWeight_lt_context
#check plain_timed_complexity
#check required_boundary_weight_lt
#check optional_boundary_weight_eq
#check optional_upper_expansion_weight_lt
#print axioms RawBranch.pendingWeight_lt_source
#print axioms RawBranch.pendingWeight_lt_context
#print axioms required_boundary_weight_lt
#print axioms optional_boundary_weight_eq
#print axioms optional_upper_expansion_weight_lt
