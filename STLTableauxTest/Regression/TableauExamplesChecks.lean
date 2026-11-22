import STLTableaux.Examples.TableauConstruction

open STLTableau STLTableau.Examples.TableauConstruction

example : (STLTableau.Section3.Predicate.plain releaseFormula :
    STLTableau.Section3.Predicate Clock Variable).complexity = 4 := release_complexity.1
example : (STLTableau.Section3.Predicate.plain alwaysSixTwelve :
    STLTableau.Section3.Predicate Clock Variable).complexity = 2 := release_complexity.2
example : (STLTableau.Section3.Predicate.plain alwaysSixTwelve :
    STLTableau.Section3.Predicate Clock Variable).complexity <
    (STLTableau.Section3.Predicate.plain releaseFormula :
    STLTableau.Section3.Predicate Clock Variable).complexity :=
  introduced_predicate_strictly_smaller
example : STLTableau.Judgement.predicate (.plain alwaysSixTwelve) ∈
    (ExpansionRule.plainRelease (Clock := Clock) alwaysSixTwelve tLe5).branches :=
  release_branch_introduces_always
example {C S V : Type*} (labels : S → Set (STLTableau.Section3.Local C V))
    (hf : ∀ s, (labels s).Finite) (e : STLTableau.Section4.EdgeLabel C) (s : S)
    (tail : STLTableau.Section4.Path C S) :
    (STLTableau.Section4.Path.step e s tail).trace labels hf =
      .step ⟨e.guards,e.guards_finite,e.resets,labels s,hf s⟩ (tail.trace labels hf) :=
  path_trace_unfold labels hf e s tail
example {C S V : Type*} (labels : S → Set (STLTableau.Section3.Local C V))
    (hf : ∀ s, (labels s).Finite) (e : STLTableau.Section4.EdgeLabel C) (s : S) :
    (STLTableau.Section4.Path.last e s).trace labels hf =
      .last ⟨e.guards,e.guards_finite,e.resets,labels s,hf s⟩ := path_trace_last labels hf e s
example : STLTableau.Section3.ConcreteContextual.catalogue.IsClosure
    (.ofState releaseSuccessor) (.ofState releaseSuccessor) :=
  release_successor_contextual_self_closure
example : successorState.incoming.guards = {⟨Clock.c,.gt,6⟩} := release_successor_incoming.1
example : STLTableau.Section3.ConcreteContextual.catalogue.IsClosure
    (.ofState releaseRoot) releaseClosure := release_closure_isClosure
example : (releaseState.incoming,releaseState) ∈ releaseTableau.initial :=
  release_generated_initial
example : (releaseState,successorState.incoming,successorState) ∈ releaseTableau.edges :=
  release_generated_edge
example : successorState ∈ releaseTableau.final := release_generated_final.2
example : releaseState.incoming.resets = ClockResetSet.singleton Clock.c 0 :=
  release_initial_incoming.2
example : (STLTableau.Section4.Path.step releaseState.incoming releaseState
    (.last successorState.incoming successorState)).run releaseTableau ∧
    (STLTableau.Section4.Path.step releaseState.incoming releaseState
    (.last successorState.incoming successorState)).accepting releaseTableau :=
  release_generated_accepting_path
example (σ : FiniteSignal Variable) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    mergeBefore.holds σ P α k ↔ mergeAfter.holds σ P α k := symbolic_merging σ P α k

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``release_complexity, ``introduced_predicate_strictly_smaller,
      ``release_branch_introduces_always,
      ``path_trace_unfold, ``path_trace_last, ``release_successor_incoming,
      ``release_left_actual_branch, ``release_opening_actual_branch,
      ``release_upper_actual_branch, ``release_closure_closed,
      ``release_closed_extension_contains_always, ``release_closed_extension_opening,
      ``release_closed_extension_checked, ``release_closure_isClosure,
      ``release_successor_contextual_self_closure, ``release_initial_incoming,
      ``release_generated_initial, ``release_generated_edge, ``release_generated_final,
      ``release_generated_accepting_path,
      ``symbolic_merging] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
