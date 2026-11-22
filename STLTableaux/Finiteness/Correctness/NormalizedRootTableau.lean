import STLTableaux.ModelChecking.Preprocessing.NormalizedInput
import STLTableaux.Finiteness.ClockAllocation.TypedRootPath
import STLTableaux.Finiteness.Correctness.FiniteRootTableauEdges

/-! Recognition of arbitrary raw STL formulas via semantic preprocessing.
Stability is required for the normalized formula, not inferred from stability
of the raw formula. Size bounds likewise refer to the normalized formula.
-/
namespace STLTableau.Section4.Finiteness
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

/-- The finite tableau constructed after total semantic normalization. -/
noncomputable def normalizedRootTableau (X : Set Var) (root : Formula Var) :=
  finiteRootTableau (Clock := Clock) X root.normalizeForTableau

theorem normalizedRootTableau_recognizes_iff
    (X : Set Var) (root : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain)
    (hStable : σ.StablePartition root.normalizeForTableau P) :
    (normalizedRootTableau (Clock := Clock) X root).recognizes
      JudgementTableau.labels_finite σ P ↔
      σ.Satisfies root ⟨0,le_rfl,σ.horizon_pos⟩ :=
  (finiteRootTableau_recognizes_iff X root.normalizeForTableau
    (Formula.mixedReady_normalizeForTableau root) σ P hStable).trans
      (Formula.satisfies_normalizeForTableau root σ _)

/-- Soundness does not require a stable partition. -/
theorem normalizedRootTableau_sound
    (X : Set Var) (root : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain)
    (h : (normalizedRootTableau (Clock := Clock) X root).recognizes
      JudgementTableau.labels_finite σ P) :
    σ.Satisfies root ⟨0,le_rfl,σ.horizon_pos⟩ :=
  (Formula.satisfies_normalizeForTableau root σ _).mp
    (finiteRootTableau_sound X root.normalizeForTableau σ P h)

theorem normalizedRootTableau_states_finite (X : Set Var) (root : Formula Var) :
    (normalizedRootTableau (Clock := Clock) X root).states.Finite :=
  finiteRootTableau_states_finite X root.normalizeForTableau

theorem normalizedRootTableau_edges_finite (X : Set Var) (root : Formula Var) :
    (normalizedRootTableau (Clock := Clock) X root).edges.Finite :=
  finiteRootTableau_edges_finite X root.normalizeForTableau

theorem normalizedRootTableau_initial_finite (X : Set Var) (root : Formula Var) :
    (normalizedRootTableau (Clock := Clock) X root).initial.Finite :=
  finiteRootTableau_initial_finite X root.normalizeForTableau

theorem normalizedRootTableau_final_finite (X : Set Var) (root : Formula Var) :
    (normalizedRootTableau (Clock := Clock) X root).final.Finite :=
  finiteRootTableau_final_finite X root.normalizeForTableau

theorem normalizedRootTableau_clocks_finite (X : Set Var) (root : Formula Var) :
    (normalizedRootTableau (Clock := Clock) X root).clocks.Finite :=
  finiteRootTableau_clocks_finite X root.normalizeForTableau

theorem normalizedRootTableau_clock_card_le (X : Set Var) (root : Formula Var) :
    Nat.card ↥(normalizedRootTableau (Clock := Clock) X root).clocks ≤
      132 * literalFormulaSize root.normalizeForTableau *
        Finiteness.formulaResolution root.normalizeForTableau :=
  finiteRootTableau_clock_card_le X root.normalizeForTableau

theorem normalizedRootTableau_state_card_le (X : Set Var) (root : Formula Var) :
    Nat.card ↥(normalizedRootTableau (Clock := Clock) X root).states ≤
      2 ^ (5634 * literalFormulaSize root.normalizeForTableau *
        Finiteness.formulaResolution root.normalizeForTableau + 7) :=
  finiteRootTableau_state_card_le X root.normalizeForTableau

end STLTableau.Section4.Finiteness
