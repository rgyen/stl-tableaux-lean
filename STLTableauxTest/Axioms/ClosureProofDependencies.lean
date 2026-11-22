import STLTableaux.Compatibility

open STLTableau.Section3.ConcreteContextual

/-! Dependency checks for the one-step expansion rank (Lemmas 4.19 and 4.20),
the common expansion level (Lemma C.15), and the auxiliary round proofs. -/
private partial def collectProjectDependencies (env : Lean.Environment)
    (name : Lean.Name) (seen : Lean.NameSet := {}) : Lean.NameSet := Id.run do
  if seen.contains name then return seen
  let mut seen := seen.insert name
  let publicName := (Lean.privateToUserName? name).getD name
  if !publicName.toString.startsWith "STLTableau." then return seen
  if let some info := env.find? name then
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    for dep in deps do
      seen := collectProjectDependencies env dep seen
  return seen

run_elab do
  let forbidden := #[
    ``STLTableau.Section3.FaithfulClosure.rank,
    ``STLTableau.Section3.FaithfulClosure.potential,
    ``STLTableau.Section3.FaithfulClosure.satisfied_closure_exists,
    ``STLTableau.Section3.GeneralClosure.satisfied_alpha_closure_exists,
    ``STLTableau.Section3.ClosureCatalogue.closed_form_of_decreasing_step,
    ``STLTableau.Section3.ClosureCatalogue.anchored_closed_extension_of_decreasing_step]
  let oneStep := #[``alpha_branchwise_freshProvenance,
    ``alpha_branchwise_rank_decrease, ``alpha_branchwise_rank_eventually_zero]
  let c15 := ``all_closures_mem_branchwise_level_at_first_rank_zero
  let commonExpansionLevel := ``all_closures_mem_branchwise_level_at_first_orbit_rank_zero
  let branchwiseClosure := #[``minimal_closure_mem_branchwise_level,
    ``minimal_closure_mem_fixed_branchwise_rounds, ``satisfied_closure_branchwise_path]
  for name in #[
    ``STLTableau.Section3.ConcreteContextual.literal_level_rank_decrease,
    ``STLTableau.Section3.ConcreteContextual.alpha_level_rank_decrease,
    ``STLTableau.Section3.ConcreteContextual.literal_level_rank_eventually_zero,
    ``STLTableau.Section3.ConcreteContextual.alpha_level_rank_eventually_zero,
    ``STLTableau.Section3.ConcreteContextual.minimal_closure_mem_expansion_level,
    ``STLTableau.Section3.ConcreteContextual.minimal_closure_expansion_sequence,
    ``minimal_closure_mem_fixed_expansion_level_at_rank_zero,
    ``minimal_closure_mem_fixed_alpha_expansion_level_at_rank_zero,
    ``fixed_expansion_order_correct,
    ``fixed_alpha_expansion_order_correct,
    ``STLTableau.Section3.ConcreteContextual.satisfied_closure_exists_via_rounds] ++
    oneStep ++ branchwiseClosure ++ #[c15, commonExpansionLevel] do
    let deps := collectProjectDependencies (← Lean.getEnv) name
    for bad in forbidden do
      if deps.contains bad then
        throwError "{name} depends on the alternative proof: {bad}"
  let invariantDeps := collectProjectDependencies (← Lean.getEnv)
    ``satisfied_alphaBranchwise_preserving
  for bad in #[
    ``STLTableau.Section3.ClosureCatalogue.PExpansion,
    ``STLTableau.Section3.ClosureCatalogue.pExpansion_exists_below,
    ``satisfied_pExpansion_preserving, ``branchwise_of_pExpansion] do
    if invariantDeps.contains bad then
      throwError "Proposition 4.16 uses the auxiliary expansion relation: {bad}"
  let roundOnly := #[``STLTableau.Section3.ExpansionFamily.level,
    ``STLTableau.Section3.ExpansionFamily.familyRank_zero_iff_closed,
    ``literalLevelRank, ``alphaLevelRank, ``literal_level_rank_decrease,
    ``alpha_level_rank_decrease, ``literal_level_rank_eventually_zero,
    ``alpha_level_rank_eventually_zero]
  for name in oneStep ++ #[c15, commonExpansionLevel] do
    let deps := collectProjectDependencies (← Lean.getEnv) name
    for bad in roundOnly do
      if deps.contains bad then
        throwError "{name} depends on auxiliary complete rounds: {bad}"
  let c15Deps := collectProjectDependencies (← Lean.getEnv) commonExpansionLevel
  for required in #[``orbitBranchwiseLevelRank_eq, ``closureSearch_common_suffix_bound,
      ``finite_alphaBranchwise_successor_cover,
      ``guided_closure_of_length_bound,
      ``STLTableau.Section3.BranchwiseLength.no_infinite_expansions,
      ``STLTableau.PrefixOrbitTermination.common_length_bound,
      ``STLTableau.PrefixOrbitTermination.lift_prefix_orbits,
      ``exists_seq_forall_proj_of_forall_finite] do
    unless c15Deps.contains required do
      throwError "C.15 is missing a step of the prefix-orbit proof: {required}"
  for bad in #[``STLTableau.Section3.BranchwiseLength.length_le,
      ``STLTableau.Section3.BranchwiseLength.bound,
      ``ClosureGuidedPrefix.length_le_componentCount] do
    if c15Deps.contains bad then
      throwError "C.15 uses the alternative quantitative length bound: {bad}"
  let numeric := ``minimal_closure_numeric
  let numericDeps := collectProjectDependencies (← Lean.getEnv) numeric
  for required in #[``minimal_closure_numeric_of_guardTypes, ``minimal_closure_guided_path,
      ``guided_closure_of_length_bound, ``STLTableau.Section3.SyntacticallySubsumed.type_subsumption,
      ``STLTableau.Section3.SyntacticallySubsumed.sound,
      ``STLTableau.Section3.NumericBranch.contextual_preserves_of_guardTypes,
      ``STLTableau.Section3.ClosureCatalogue.BranchwisePExpansion.eq_union_or_identity] do
    unless numericDeps.contains required do
      throwError "Closure numeric invariant is missing a step of the guided proof: {required}"
  for bad in roundOnly ++ #[
      ``STLTableau.Section3.ClosureCatalogue.minimal_closure_numeric,
      ``STLTableau.Section3.ClosureCatalogue.minimal_restriction_eq,
      ``STLTableau.Section3.SyntacticallySubsumed.numericProjectionTarget] do
    if numericDeps.contains bad then
      throwError "Closure numeric invariant depends on an alternative proof: {bad}"
  for name in #[``minimal_closure_holds_of_atomicProjection,
      ``STLTableau.Section4.Generated.trace_invariant,
      ``STLTableau.Section4.Generated.trace_equivalence] do
    unless (collectProjectDependencies (← Lean.getEnv) name).contains numeric do
      throwError "{name} does not use the guided closure-invariant proof"
  for name in branchwiseClosure do
    let deps := collectProjectDependencies (← Lean.getEnv) name
    for bad in oneStep ++ #[``alphaBranchwiseLevelRank,
        ``STLTableau.Section3.BranchwiseExpansion.rank] do
      if deps.contains bad then
        throwError "{name} depends on newly-seen one-step rank: {bad}"
