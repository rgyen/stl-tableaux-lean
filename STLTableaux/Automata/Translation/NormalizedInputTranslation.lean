import STLTableaux.Syntax.InputSyntax
import STLTableaux.Automata.Translation.RootAutomata
import STLTableaux.Finiteness.Correctness.LiteralRootTableau
import STLTableaux.Automata.Execution.TerminalPruning

/-! Translations for inputs in the normalized grammar. The derivation
admission relation supplies the tableau states. The minimal-closure variants
restrict the state set to original closures. For the translation of the finite
tableau in Theorem 4.37, see
`STLTableaux.Automata.Translation.CanonicalTranslationCorrectness`. -/
namespace STLTableau.Section4.Finiteness
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

noncomputable def inputTableau (X : Set Var) (root : Formula.NormalizedInput Var) :=
  finiteRootTableau (Clock := Clock) X root.val

theorem inputTableau_recognizes_iff (X : Set Var) (root : Formula.NormalizedInput Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (hs : σ.StablePartition root.val P) :
    (inputTableau (Clock := Clock) X root).recognizes
      JudgementTableau.labels_finite σ P ↔
      σ.Satisfies root.val ⟨0, le_rfl, σ.horizon_pos⟩ :=
  finiteRootTableau_recognizes_iff X root.val root.property.mixedReady σ P hs

/-- No extra normalization is performed and no arbitrary-input correctness
claim is attached to the underlying low-level construction. -/
noncomputable def inputAutomaton (root : Formula.NormalizedInput Var)
    (τ : ℝ) (hτ : 0 < τ) :=
  rootAutomaton (Clock := Clock) root.val τ hτ

/-- Positional pruning preserves recognition on the original partition. -/
theorem inputTableau_pruned_recognizes_iff (X : Set Var)
    (root : Formula.NormalizedInput Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (hs : σ.StablePartition root.val P) :
    (inputTableau (Clock := Clock) X root).pruneTerminal.recognizes
      JudgementTableau.labels_finite σ P ↔
      σ.Satisfies root.val ⟨0, le_rfl, σ.horizon_pos⟩ :=
  ((inputTableau X root).pruneTerminal_recognizes_iff
    JudgementTableau.labels_finite σ P).trans
      (inputTableau_recognizes_iff X root σ P hs)

/-- Terminal-pruned translation of the extended-Derives graph, retained
separately from the auxiliary literal APIs below. -/
noncomputable def inputPrunedAutomaton (root : Formula.NormalizedInput Var)
    (τ : ℝ) (hτ : 0 < τ) :=
  (inputTableau (Clock := Clock)
    (↑(rootVariables root.val) : Set Var) root).toPrunedAutomaton
    (finiteRootTableau_translationReady (Clock := Clock) _ (Finset.finite_toSet _)
      root.val (fun _ hx => hx)) τ hτ

/-- Auxiliary literal-closure restriction of the finite inventory.
This is not the simplified finite-tableau admission relation. -/
noncomputable def literalInputTableau (X : Set Var) (root : Formula.NormalizedInput Var) :=
  finiteLiteralRootTableau (Clock := Clock) X root.val

theorem literalInputTableau_translationReady (X : Set Var) (hX : X.Finite)
    (root : Formula.NormalizedInput Var) (hvars : ∀ x ∈ rootVariables root.val, x ∈ X) :
    (literalInputTableau (Clock := Clock) X root).TranslationReady :=
  finiteLiteralRootTableau_translationReady X hX root.val hvars

theorem literalInputTableau_sound (X : Set Var) (root : Formula.NormalizedInput Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (hs : (literalInputTableau (Clock := Clock) X root).recognizes
      JudgementTableau.labels_finite σ P) :
    σ.Satisfies root.val ⟨0, le_rfl, σ.horizon_pos⟩ :=
  finiteLiteralRootTableau_sound X root.val σ P hs

theorem literalInputTableau_pruned_sound (X : Set Var) (root : Formula.NormalizedInput Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (hs : (literalInputTableau (Clock := Clock) X root).pruneTerminal.recognizes
      JudgementTableau.labels_finite σ P) :
    σ.Satisfies root.val ⟨0, le_rfl, σ.horizon_pos⟩ :=
  literalInputTableau_sound X root σ P
    (((literalInputTableau X root).pruneTerminal_recognizes_iff
      JudgementTableau.labels_finite σ P).mp hs)

noncomputable def literalInputAutomaton (root : Formula.NormalizedInput Var)
    (τ : ℝ) (hτ : 0 < τ) :=
  (literalInputTableau (Clock := Clock)
    (↑(rootVariables root.val) : Set Var) root).toAutomaton
      (literalInputTableau_translationReady _ (Finset.finite_toSet _)
        root (fun _ hx => hx)) τ hτ

noncomputable def literalInputPrunedAutomaton (root : Formula.NormalizedInput Var)
    (τ : ℝ) (hτ : 0 < τ) :=
  (literalInputTableau (Clock := Clock)
    (↑(rootVariables root.val) : Set Var) root).toPrunedAutomaton
    (literalInputTableau_translationReady _ (Finset.finite_toSet _)
      root (fun _ hx => hx)) τ hτ

end STLTableau.Section4.Finiteness
