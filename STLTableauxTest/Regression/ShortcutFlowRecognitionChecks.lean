import STLTableaux.Automata.Recognition.ShortcutFlowRecognition

open STLTableau STLTableau.Section4
open STLTableau.Section4.Finiteness

/-- Certificates neither add edges nor extend the automaton language.
They are one way to establish an already existing direct edge. -/
theorem shortcut_block_iff_direct {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (root : Formula Var)
    (h : (finiteRootTableau (Clock := Clock) X root).TranslationReady)
    (τ : ℝ) (hτ : 0 < τ)
    (s t : ((finiteRootTableau X root).toAutomaton h τ hτ).State) :
    ShortcutBlock X root h τ hτ s t ↔
      ((finiteRootTableau X root).toAutomaton h τ hτ).DiscreteStep s t :=
  ⟨ShortcutBlock.direct, ShortcutBlock.of_direct⟩

/-- A nonempty prefix is allowed; all its edges remain actual automaton edges.
Value agreement is sufficient but not required by the general certificate. -/
theorem same_values_block {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (root : Formula Var)
    (h : (finiteRootTableau (Clock := Clock) X root).TranslationReady)
    (τ : ℝ) (hτ : 0 < τ)
    (s m t : ((finiteRootTableau X root).toAutomaton h τ hτ).State)
    (hp : Relation.ReflTransGen ((finiteRootTableau X root).toAutomaton h τ hτ).DiscreteStep s m)
    (hj : ((finiteRootTableau X root).toAutomaton h τ hτ).DiscreteStep m t)
    (hn : s.val.1.val.nextPart = m.val.1.val.nextPart)
    (hv : s.val.2 = m.val.2) : ShortcutBlock X root h τ hτ s t := by
  exact ⟨m, hp, hj, hn, fun _ _ _ _ _ => congrFun hv _, fun _ _ _ _ => congrFun hv _⟩

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``ShortcutBlock.direct, ``ShortcutBlock.of_direct,
      ``ExecutionShortcutBlocks.of_direct, ``inputTableau_recognizes_shortcut_flows,
      ``shortcut_block_iff_direct, ``same_values_block] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
