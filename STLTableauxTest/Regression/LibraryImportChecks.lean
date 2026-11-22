import STLTableaux

/-! These examples use the finite tableau and model checking results through
`import STLTableaux`. -/
open STLTableau STLTableau.Section4.Finiteness

example {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (root : Formula Var) :
    (finiteTableau (Clock := Clock) X root).states.Finite :=
  finiteTableau_states_finite X root

example {Var : Type*} (φ : Formula Var) (σ : FiniteSignal Var) (t : σ.Time) :
    σ.Satisfies φ.normalizeForTableau t ↔ σ.Satisfies φ t :=
  Formula.satisfies_normalizeForTableau φ σ t

-- Theorem 5.7 and Corollary 5.8 are available through the same import.
#check canonical_model_checking
#check canonical_robust_model_checking
