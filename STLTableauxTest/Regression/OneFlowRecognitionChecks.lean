import STLTableaux.Automata.Recognition.OneFlowRecognition

open STLTableau.Section4.Finiteness
open STLTableau STLTableau.Section4

-- Recognition from a first flow with unused real clock coordinates.
example {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : (inputTableau X root).ProjectsTo σ ρ)
    (hcount : e.count = 1)
    (hearly : e.boundary ⟨e.count, by omega⟩ < σ.horizon)
    (hgoal : e.finalState.val.1.val ∈ (inputTableau X root).final)
    (hj : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).DiscreteStep
      (e.finish ⟨0, e.nonempty⟩) e.finalState)
    (hfirst : Section3.Local.marker ○ ∉
      (inputTableau X root).label (e.start ⟨0, e.nonempty⟩).val.1.val)
    (hfinal : Section3.Local.marker ○ ∉ (inputTableau X root).label e.finalState.val.1.val)
    (hs : e.initialState = e.start ⟨0, e.nonempty⟩) :
    ∃ P : IntervalPartition ρ.domain,
      (inputTableau (Clock := Clock) X root).recognizes JudgementTableau.labels_finite ρ P := by
  apply inputTableau_recognizes_one_flow X root h e hp hcount hearly hgoal hj hfirst hfinal
  rw [← hs]
  exact e.initial_mem

-- Construct a recognizing path from a single observed flow.
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for ax in ← Lean.collectAxioms ``inputTableau_recognizes_one_flow do
    unless allowed.contains ax do
      throwError "inputTableau_recognizes_one_flow uses unapproved axiom {ax}"
