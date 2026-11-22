import STLTableaux.Examples
import Lean

/-! Check the Lean declarations for the twelve examples in Sections 3–4 and Appendix C. -/

run_elab do
  let names : Array Lean.Name := #[
    -- Interval predicates
    ``STLTableau.Examples.Section3.always_scope,
    ``STLTableau.Examples.Section3.eventually_scope,
    ``STLTableau.Examples.Section3.always_domain_clipped,
    ``STLTableau.Examples.Section3.always_untruncated,
    ``STLTableau.Examples.Section3.eventually_witnesses,
    -- Judgements with reset scopes
    ``STLTableau.Examples.Section3.reset_values,
    ``STLTableau.Examples.Section3.psi1,
    ``STLTableau.Examples.Section3.psi2,
    -- Partition and terminal position
    ``STLTableau.Examples.Section3.partition,
    ``STLTableau.Examples.Section3.partition_first,
    ``STLTableau.Examples.Section3.partition_last,
    -- Reset assignments
    ``STLTableau.Examples.Section3.reset_disjoint,
    ``STLTableau.Examples.Section3.reset_consistent,
    ``STLTableau.Examples.Section3.free_clock,
    ``STLTableau.Examples.Section3.reset_assignment,
    ``STLTableau.Examples.Section3.reset_clock_satisfaction,
    ``STLTableau.Examples.Section3.reset_clock_true,
    ``STLTableau.Examples.Section3.other_clock_irrelevant,
    -- Transition forms
    ``STLTableau.Examples.TransitionForms.first_transition_syntax,
    ``STLTableau.Examples.TransitionForms.second_transition_syntax,
    ``STLTableau.Examples.TransitionForms.first_normalizes,
    ``STLTableau.Examples.TransitionForms.second_normalizes,
    ``STLTableau.Examples.TransitionForms.first_empty_reset,
    ``STLTableau.Examples.TransitionForms.second_no_next,
    ``STLTableau.Examples.TransitionForms.nested_next_not_transition_syntax,
    ``STLTableau.Examples.TransitionForms.reset_guard_not_transition_syntax,
    ``STLTableau.Examples.TransitionForms.nested_next_rejected,
    -- Subsumption
    ``STLTableau.Examples.TransitionForms.positive_subsumption,
    ``STLTableau.Examples.TransitionForms.reset_capture_not_subsumed,
    -- Rule closure
    ``STLTableau.Examples.TransitionForms.atom_rule_closed,
    ``STLTableau.Examples.TransitionForms.upper_not_rule_closed,
    -- Minimal closure
    ``STLTableau.Examples.TransitionForms.terminalCheck_actual_branch,
    ``STLTableau.Examples.TransitionForms.printedClosure_same_resets,
    ``STLTableau.Examples.TransitionForms.printedClosure_closed,
    ``STLTableau.Examples.TransitionForms.printedClosure_isClosure,
    -- Complexity of interval predicates
    ``STLTableau.Examples.TableauConstruction.release_complexity,
    ``STLTableau.Examples.TableauConstruction.introduced_predicate_strictly_smaller,
    ``STLTableau.Examples.TableauConstruction.release_branch_introduces_always,
    -- Path trace
    ``STLTableau.Examples.TableauConstruction.path_trace_unfold,
    ``STLTableau.Examples.TableauConstruction.path_trace_last,
    -- Tableau construction
    ``STLTableau.Examples.TableauConstruction.release_closure_isClosure,
    ``STLTableau.Examples.TableauConstruction.release_initial_incoming,
    ``STLTableau.Examples.TableauConstruction.release_successor_incoming,
    ``STLTableau.Examples.TableauConstruction.release_successor_contextual_self_closure,
    ``STLTableau.Examples.TableauConstruction.release_generated_initial,
    ``STLTableau.Examples.TableauConstruction.release_generated_edge,
    ``STLTableau.Examples.TableauConstruction.release_generated_final,
    ``STLTableau.Examples.TableauConstruction.release_generated_accepting_path,
    -- Symbolic merging
    ``STLTableau.Examples.TableauConstruction.symbolic_merging,
  ]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
  Lean.logInfo m!"Checked {names.size} declarations. They use only standard Lean axioms."
