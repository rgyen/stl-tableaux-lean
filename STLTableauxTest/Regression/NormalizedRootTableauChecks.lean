import STLTableaux.Finiteness.Correctness.NormalizedRootTableau

open STLTableau STLTableau.Section4.Finiteness

-- The stability assumption applies to the normalized formula.
example {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (root : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain)
    (hStable : σ.StablePartition root.normalizeForTableau P) :
    (normalizedRootTableau (Clock := Clock) X root).recognizes
      JudgementTableau.labels_finite σ P ↔
      σ.Satisfies root ⟨0,le_rfl,σ.horizon_pos⟩ :=
  normalizedRootTableau_recognizes_iff X root σ P hStable

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[``normalizedRootTableau_recognizes_iff,
    ``normalizedRootTableau_sound, ``normalizedRootTableau_states_finite,
    ``normalizedRootTableau_edges_finite, ``normalizedRootTableau_initial_finite,
    ``normalizedRootTableau_final_finite, ``normalizedRootTableau_clocks_finite,
    ``normalizedRootTableau_clock_card_le, ``normalizedRootTableau_state_card_le]
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
