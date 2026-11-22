import STLTableaux.Finiteness.Correctness.Step1AcceptingEquivalence
import STLTableaux.Finiteness.Correctness.UniformRootPath
import STLTableaux.Finiteness.ClockAllocation.AllocatedRootPath
import STLTableaux.Finiteness.ClockAllocation.TypedRootPath
import STLTableaux.Finiteness.Correctness.FiniteRootTableauEdges
import STLTableaux.Finiteness.Correctness.FiniteTableau

/-! Interface and axiom checks for the correspondence of accepting runs
(Lemma 4.35), bounded accepting runs (Lemma 4.36), and the finite tableau
(Theorem 4.37). Also checks the auxiliary derivation tableau, including its
bounds and clock assignments. -/
open STLTableau.Section4.Finiteness

#check original_accepting_run_forward
#check step1_satisfied_accepting_iff
#check origin_certified_path_of_formula
#check origin_certified_path_of_original_run
#check uniform_root_accepting_path
#check uniform_root_path_of_formula
#check uniform_root_path_of_original_run
#check allocated_root_accepting_path
#check allocated_root_path_of_formula
#check allocated_root_path_of_original_run
#check SelectedTree.exists_root_typed_extension
#check typed_root_accepting_path
#check finiteRootTableau_accepting_path_of_formula
#check finiteRootTableau_accepting_path_of_revised_run
#check finiteRootTableau_accepting_path_of_original_run
#check finiteRootTableau_complete
#check finiteRootTableau_sound
#check finiteRootTableau_recognizes_iff
#check rootSlot_clockAt_injective
#check rootSlot_family_card
#check rootSlot_card_le_size_resolution
#check rootSlot_sparse_exponent_le_resolution
#check finiteRootTableau_states_finite
#check finiteRootTableau_state_card_le
#check finiteRootTableau_clocks_finite
#check finiteRootTableau_clock_card_le
#check finiteRootTableau_state_clock_support
#check finiteRootTableau_state_clock_card_le
#check finiteRootTableau_edges_finite
#check finiteRootTableau_initial_finite
#check finiteRootTableau_final_finite
#check finiteTableau_bounded_accepting_path
#check simplified_satisfied_accepting_iff
#check finiteTableau_recognizes_normalized_input
#check finiteTableau_state_card_le
#check finiteTableau_clock_card_le

#print axioms step1_satisfied_accepting_iff
#print axioms uniform_root_path_of_formula
#print axioms allocated_root_path_of_formula
#print axioms typed_root_accepting_path
#print axioms finiteRootTableau_accepting_path_of_original_run
#print axioms finiteRootTableau_recognizes_iff
#print axioms finiteRootTableau_state_card_le
#print axioms finiteRootTableau_clock_card_le
#print axioms finiteRootTableau_state_clock_support
#print axioms finiteRootTableau_edges_finite

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[
    ``original_accepting_run_forward,
    ``step1_satisfied_accepting_iff,
    ``origin_certified_path_of_formula,
    ``origin_certified_path_of_original_run,
    ``uniform_root_accepting_path,
    ``uniform_root_path_of_formula,
    ``uniform_root_path_of_original_run,
    ``allocated_root_accepting_path,
    ``allocated_root_path_of_formula,
    ``allocated_root_path_of_original_run,
    ``SelectedTree.exists_root_typed_extension,
    ``typed_root_accepting_path,
    ``finiteRootTableau_accepting_path_of_formula,
    ``finiteRootTableau_accepting_path_of_revised_run,
    ``finiteRootTableau_accepting_path_of_original_run,
    ``finiteRootTableau_complete,
    ``finiteRootTableau_sound,
    ``finiteRootTableau_recognizes_iff,
    ``rootSlot_clockAt_injective,
    ``rootSlot_family_card,
    ``rootSlot_card_le_size_resolution,
    ``rootSlot_sparse_exponent_le_resolution,
    ``finiteRootTableau_states_finite,
    ``finiteRootTableau_state_card_le,
    ``finiteRootTableau_clocks_finite,
    ``finiteRootTableau_clock_card_le,
    ``finiteRootTableau_state_clock_support,
    ``finiteRootTableau_state_clock_card_le,
    ``finiteRootTableau_edges_finite,
    ``finiteRootTableau_initial_finite,
    ``finiteRootTableau_final_finite,
    ``finiteTableau_bounded_accepting_path,
    ``simplified_satisfied_accepting_iff,
    ``simplified_fullTrace_and_formula_of_atomic,
    ``finiteTableau_recognizes_normalized_input,
    ``finiteTableau_state_card_le,
    ``finiteTableau_clock_card_le,
    ``finiteTableau_edges_finite,
    ``finiteTableau_initial_finite,
    ``finiteTableau_final_finite
  ] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
