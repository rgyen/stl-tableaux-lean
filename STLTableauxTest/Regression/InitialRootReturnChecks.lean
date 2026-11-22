import STLTableaux.Automata.Translation.InitialRootReturn

open STLTableau

-- Equality of the initial valuations is necessary, not merely a convenient
-- condition: two witnesses of the same signal both observe its value at zero.
example {Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
    {σ : FiniteSignal Var} (e e' : H.Execution σ) :
    e'.initialState.val.2 = e.initialState.val.2 :=
  e'.initial_signal_eq.symm.trans e.initial_signal_eq

-- Rechoosing an admissible initial state is observation-preserving only
-- when its complete valuation agrees with the original owner of zero.
example {Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
    {σ : FiniteSignal Var} (e : H.Execution σ)
    (same : e.lastInitialState.val.2 = e.initialState.val.2)
    (hi : (e.start ⟨0, e.nonempty⟩).val ∈ H.initial) :
    (e.normalizeInitialBlock same).initialState = e.start ⟨0, e.nonempty⟩ :=
  e.normalizeInitialBlock_initial_eq_firstFlow hi same

example {Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
    {σ : FiniteSignal Var} (e : H.Execution σ)
    (same : e.lastInitialState.val.2 = e.initialState.val.2) :
    (e.normalizeInitialBlock same).start = e.start ∧
    (e.normalizeInitialBlock same).finish = e.finish ∧
    (e.normalizeInitialBlock same).duration = e.duration ∧
    (e.normalizeInitialBlock same).curve = e.curve ∧
    (e.normalizeInitialBlock same).boundary = e.boundary ∧
    (e.normalizeInitialBlock same).discreteSteps = e.discreteSteps ∧
    (e.normalizeInitialBlock same).finalSteps = e.finalSteps ∧
    (e.normalizeInitialBlock same).finalState = e.finalState :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

example {Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
    {σ : FiniteSignal Var} (e : H.Execution σ) (goal : Set Mode)
    (same : e.lastInitialState.val.2 = e.initialState.val.2)
    (hg : e.finalState.val.1 ∈ goal) :
    H.Reaches σ goal := ⟨e.normalizeInitialBlock same, hg⟩

-- Covers both horizon exhaustion and early stopping: the partition includes
-- exactly the same boundaries and suffix after the initial witness changes.
example {Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
    {σ : FiniteSignal Var} (e : H.Execution σ)
    (same : e.lastInitialState.val.2 = e.initialState.val.2) :
    (e.normalizeInitialBlock same).reviewInducedPartition = e.reviewInducedPartition :=
  e.normalizeInitialBlock_reviewInducedPartition same

-- An intermediate initial-block state can be selected without changing any
-- observed flow, duration, final jump tail, or final observation endpoint.
example {Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
    {σ : FiniteSignal Var} (e : H.Execution σ) (s : H.State)
    (hi : s.val ∈ H.initial)
    (hs : Relation.ReflTransGen H.DiscreteStep s (e.start ⟨0, e.nonempty⟩))
    (same : s.val.2 = e.initialState.val.2) :
    (e.rebaseInitialState s hi hs same).initialState = s ∧
    (e.rebaseInitialState s hi hs same).start = e.start ∧
    (e.rebaseInitialState s hi hs same).finish = e.finish ∧
    (e.rebaseInitialState s hi hs same).duration = e.duration ∧
    (e.rebaseInitialState s hi hs same).curve = e.curve ∧
    (e.rebaseInitialState s hi hs same).boundary = e.boundary ∧
    (e.rebaseInitialState s hi hs same).finalState = e.finalState :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Rebasing preserves the complete observed behavior and final endpoint.
example {Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
    {σ : FiniteSignal Var} (e : H.Execution σ)
    (hi : (e.start ⟨0, e.nonempty⟩).val ∈ H.initial)
    (same : (e.start ⟨0, e.nonempty⟩).val.2 = e.initialState.val.2) :
    (e.rebaseAtFirstFlow hi same).start = e.start ∧
    (e.rebaseAtFirstFlow hi same).finish = e.finish ∧
    (e.rebaseAtFirstFlow hi same).curve = e.curve ∧
    (e.rebaseAtFirstFlow hi same).boundary = e.boundary ∧
    (e.rebaseAtFirstFlow hi same).finalState = e.finalState :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

example {Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
    {σ : FiniteSignal Var} (e : H.Execution σ)
    (hi : (e.start ⟨0, e.nonempty⟩).val ∈ H.initial)
    (same : (e.start ⟨0, e.nonempty⟩).val.2 = e.initialState.val.2) :
    (e.rebaseAtFirstFlow hi same).initialState = e.start ⟨0, e.nonempty⟩ := rfl

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``HybridAutomaton.Execution.rebaseAtFirstFlow,
      ``HybridAutomaton.Execution.rebaseInitialState,
      ``HybridAutomaton.Execution.exists_last_initial,
      ``HybridAutomaton.Execution.lastInitialState_spec,
      ``HybridAutomaton.Execution.normalizeInitialBlock,
      ``HybridAutomaton.Execution.normalizeInitialBlock_reviewInducedPartition,
      ``HybridAutomaton.Execution.normalizeInitialBlock_initialSteps,
      ``HybridAutomaton.Execution.normalizeInitialBlock_initial_eq_firstFlow,
      ``Section4.Tableau.pruned_execution_accepting_observed_path_normalized,
      ``Section4.Finiteness.finiteRootTableau_pruned_root_return_initial,
      ``Section4.Finiteness.normalized_initialSteps_no_root_return,
      ``Section4.Finiteness.rebasePrunedInitialRootReturn,
      ``Section4.Tableau.initialReset_eq_reset_at_zero,
      ``Section4.Tableau.initial_of_zero_time_jump,
      ``Section4.Finiteness.finiteRootTableau_root_return_initial,
      ``Section4.Finiteness.finiteRootTableau_firstFlow_initial_of_root_return] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
