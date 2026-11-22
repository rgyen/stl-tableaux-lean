import STLTableaux.Automata.Recognition.SingletonFlowFinalRecognition

open STLTableau STLTableau.Section4
open STLTableau.Section4.Finiteness

/-- One observed flow can itself be accepting. No final jump, terminal-label
restriction, or absence of atomic labels is assumed. -/
theorem one_flow_acceptance_without_terminal_tail
    {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : (inputTableau X root).ProjectsTo σ ρ)
    (hcount : e.count = 1)
    (hexhaust : e.boundary ⟨e.count, by omega⟩ = σ.horizon)
    (hinit : (e.start ⟨0, e.nonempty⟩).val ∈
      ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).initial)
    (hgoal : (e.start ⟨0, e.nonempty⟩).val.1.val ∈ (inputTableau X root).final)
    (hmarker : Section3.Local.marker ○ ∉
      (inputTableau X root).label (e.start ⟨0, e.nonempty⟩).val.1.val) :
    ∃ P : IntervalPartition ρ.domain, P.size = 1 ∧
      (inputTableau (Clock := Clock) X root).recognizes
        JudgementTableau.labels_finite ρ P := by
  let b : Fin 2 → ℝ := fun j => e.boundary ⟨j.val, by have := j.isLt; omega⟩
  have hb : StrictMono b := by
    intro i j hij
    exact e.increasing (show (⟨i.val, by omega⟩ : Fin (e.count + 1)) <
      ⟨j.val, by omega⟩ from hij)
  have hend : b 1 = ρ.horizon := by
    change e.boundary _ = ρ.horizon
    exact (congrArg e.boundary (Fin.ext hcount.symm)).trans (hexhaust.trans hp.1)
  apply inputTableau_recognizes_final_observed_interval X root h e hp 0 b hb.monotone
    (fun _ => ●) ?_ rfl rfl e.first_zero hend
    (fun _ => e.start ⟨0, e.nonempty⟩) (fun _ => e.finish ⟨0, e.nonempty⟩)
    (fun _ => 0) hinit (by omega) (by omega) hgoal (fun i => Fin.elim0 i) ?_ ?_
    (fun _ _ => rfl)
  · intro i he
    exact ((ne_of_lt (hb (by change i.val < i.val + 1; omega))) he).elim
  · intro i
    have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
    subst i
    exact Tableau.ExecutionObservedPiece.flow ⟨0, e.nonempty⟩
  · intro i mark hm
    cases mark with
    | «open» => exact (hmarker hm).elim
    | closed => rfl

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``inputTableau_recognizes_final_observed_interval,
      ``one_flow_acceptance_without_terminal_tail] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
