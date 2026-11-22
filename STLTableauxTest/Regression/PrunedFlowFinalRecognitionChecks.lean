import STLTableaux.Automata.Recognition.PrunedFlowFinalRecognition

open STLTableau STLTableau.Section4
open STLTableau.Section4.Finiteness

/-- A single accepting flow needs neither a terminal label nor a final jump.
Atomic labels are deliberately unrestricted. -/
theorem pruned_one_flow_acceptance
    {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toPrunedAutomaton h
      σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : (inputTableau X root).ProjectsTo σ ρ)
    (hcount : e.count = 1)
    (hexhaust : e.boundary ⟨e.count, by omega⟩ = σ.horizon)
    (hinit : (e.start ⟨0, e.nonempty⟩).val ∈
      ((inputTableau X root).toPrunedAutomaton h σ.horizon σ.horizon_pos).initial)
    (hgoal : (e.start ⟨0, e.nonempty⟩).val.1.val ∈
      (inputTableau X root).pruneTerminal.final)
    (hmarker : Section3.Local.marker ○ ∉
      (inputTableau X root).label (e.start ⟨0, e.nonempty⟩).val.1.val) :
    ∃ P : IntervalPartition ρ.domain, P.size = 1 ∧
      (inputTableau (Clock := Clock) X root).pruneTerminal.recognizes
        JudgementTableau.labels_finite ρ P := by
  let b : Fin 2 → ℝ := fun j => e.boundary ⟨j.val, by have := j.isLt; omega⟩
  have hend : b 1 = ρ.horizon := by
    exact (congrArg e.boundary (Fin.ext hcount.symm)).trans (hexhaust.trans hp.1)
  apply inputTableau_pruned_recognizes_final_observed_interval X root h e hp 0 b
    (by intro i hi; have := i.isLt; omega) e.first_zero hend
    (fun _ => e.start ⟨0, e.nonempty⟩) (fun _ => e.finish ⟨0, e.nonempty⟩)
    (fun _ => 0) hinit (by omega) (by omega) hgoal (fun i => Fin.elim0 i) ?_ ?_
  · intro i
    have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
    subst i
    exact Tableau.ExecutionObservedPiece.flow ⟨0, e.nonempty⟩
  · intro i mark hm
    have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
    subst i
    cases mark with
    | «open» => exact (hmarker hm).elim
    | closed => exact IntervalPartition.singletonMarkers_first b

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``inputTableau_pruned_recognizes_final_observed_interval,
      ``pruned_one_flow_acceptance, ``pruned_execution_observed_nonterminal,
      ``Tableau.ExecutionObservedPiece.left_lt_horizon,
      ``Tableau.ExecutionObservedPiece.left_le_right] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
