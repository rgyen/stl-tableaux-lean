import STLTableaux.Automata.Translation.NormalizedInputTranslation

open STLTableau STLTableau.Section4
open STLTableau.Section4.Finiteness

section
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

-- The auxiliary normalized input wrapper uses the derivation tableau.
example (X : Set Var) (root : Formula.NormalizedInput Var) :
    inputTableau (Clock := Clock) X root = finiteRootTableau X root.val := rfl

example (root : Formula.NormalizedInput Var) (τ : ℝ) (hτ : 0 < τ) :
    inputAutomaton (Clock := Clock) root τ hτ = rootAutomaton root.val τ hτ := rfl

example (root : Formula.NormalizedInput Var) (τ : ℝ) (hτ : 0 < τ) :
    inputPrunedAutomaton (Clock := Clock) root τ hτ =
      (inputTableau (Clock := Clock)
        (↑(rootVariables root.val) : Set Var) root).toPrunedAutomaton
          (finiteRootTableau_translationReady _ (Finset.finite_toSet _)
            root.val (fun _ hx => hx)) τ hτ := rfl

example (X : Set Var) (root : Formula.NormalizedInput Var)
    (F : STLTableau.Section3.TransitionForm Clock Var) (l : EdgeLabel Clock)
    (hi : (l, F) ∈ (literalInputTableau X root).initial) :
    STLTableau.Section3.ConcreteContextual.catalogue.IsClosure
      (.ofState (.ofLocal (.predicate (.plain root.val)))) F :=
  finiteLiteralRootTableau_initial_closure X root.val hi

example (X : Set Var) (root : Formula.NormalizedInput Var)
    (F G : STLTableau.Section3.TransitionForm Clock Var) (l : EdgeLabel Clock)
    (he : (F, l, G) ∈ (literalInputTableau X root).edges) :
    ∃ N, F.nextPart = some N ∧
      STLTableau.Section3.ConcreteContextual.catalogue.IsClosure (.ofState N) G :=
  finiteLiteralRootTableau_edge_closure X root.val he

-- These automaton wrappers use the restriction to original minimal closures.
example (root : Formula.NormalizedInput Var) (τ : ℝ) (hτ : 0 < τ) :
    literalInputAutomaton (Clock := Clock) root τ hτ =
      (literalInputTableau (Clock := Clock) (↑(rootVariables root.val) : Set Var) root).toAutomaton
        (literalInputTableau_translationReady _ (Finset.finite_toSet _)
          root (fun _ hx => hx)) τ hτ := rfl

example (root : Formula.NormalizedInput Var) (τ : ℝ) (hτ : 0 < τ) :
    literalInputPrunedAutomaton (Clock := Clock) root τ hτ =
      (literalInputTableau (Clock := Clock)
        (↑(rootVariables root.val) : Set Var) root).toPrunedAutomaton
        (literalInputTableau_translationReady _ (Finset.finite_toSet _)
          root (fun _ hx => hx)) τ hτ := rfl
end

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``finiteLiteralRootTableau_initial_closure,
      ``finiteLiteralRootTableau_edge_closure, ``finiteLiteralRootTableau_states_finite,
      ``finiteLiteralRootTableau_edges_finite, ``finiteLiteralRootTableau_state_clock_support,
      ``finiteLiteralRootTableau_recognizes_to_extended,
      ``literalInputTableau_sound, ``literalInputTableau_pruned_sound,
      ``literalInputTableau_translationReady,
      ``inputTableau_recognizes_iff, ``inputTableau_pruned_recognizes_iff] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
