import STLTableaux.Automata.Execution.TerminalPruning
import STLTableaux.Automata.Translation.NormalizedInputTranslation

open STLTableau STLTableau.Section4

example {Clock Var State : Type*} (T : Tableau Clock Var State)
    (s : State) (a : AtomicProposition Var)
    (ht : Section3.Local.terminal ∈ T.label s)
    (hp : Section3.Local.predicate (.plain (.atom a)) ∈ T.label s) :
    s ∉ T.pruneTerminal.states :=
  T.terminal_predicate_not_mem_pruned s (.plain (.atom a)) ht hp

example {Clock Var State : Type*} (T : Tableau Clock Var State)
    (s : State) (ht : Section3.Local.terminal ∉ T.label s) :
    s ∈ T.pruneTerminal.final ↔ s ∈ T.final :=
  ⟨And.left, fun hs => ⟨hs, fun h => (ht h).elim⟩⟩

example {Clock Var State : Type*} (T : Tableau Clock Var State)
    (s : State) (ht : Section3.Local.terminal ∈ T.label s)
    (hm : Section3.Local.marker ○ ∈ T.label s) :
    s ∉ T.pruneTerminal.states := by
  intro hs
  rcases hs.2 ht (.marker ○) hm with h | h <;> cases h

example {Clock Var State : Type*} (T : Tableau Clock Var State)
    (s t : State) (e : EdgeLabel Clock)
    (ht : Section3.Local.terminal ∈ T.label s) :
    (s, e, t) ∉ T.pruneTerminal.edges := fun h => h.2.2.2 ht

-- Terminal pruning imposes no additional initial-marker condition.
example {Clock Var State : Type*} (T : Tableau Clock Var State)
    (s : State) (e : EdgeLabel Clock) (hi : (e, s) ∈ T.initial)
    (ht : T.TerminalCompatible s) :
    (e, s) ∈ T.pruneTerminal.initial := ⟨hi, ht⟩

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Tableau.pruneTerminal_recognizes_iff,
      ``Tableau.pruneTerminal_translationReady, ``Tableau.pruned_terminal_labels,
      ``Tableau.terminal_predicate_not_mem_pruned,
      ``Finiteness.inputTableau_pruned_recognizes_iff,
      ``Path.valid_pruneTerminal_iff_of_trace] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
