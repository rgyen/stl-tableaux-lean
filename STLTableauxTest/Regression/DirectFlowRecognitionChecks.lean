import STLTableaux.Automata.Recognition.DirectFlowRecognition

open STLTableau STLTableau.Section4
open STLTableau.Section4.Finiteness

/-- The construction for several flows also applies to a single flow. -/
theorem one_flow_via_direct_flows {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : (inputTableau X root).ProjectsTo σ ρ)
    (hcount : e.count = 1)
    (hearly : e.boundary ⟨e.count, by omega⟩ < σ.horizon)
    (hgoal : e.finalState.val.1.val ∈ (inputTableau X root).final)
    (hinit : (e.start ⟨0, e.nonempty⟩).val ∈
      ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).initial)
    (hj : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).DiscreteStep
      (e.finish ⟨0, e.nonempty⟩) e.finalState)
    (hfirst : Section3.Local.marker ○ ∉
      (inputTableau X root).label (e.start ⟨0, e.nonempty⟩).val.1.val)
    (hfinal : Section3.Local.marker ○ ∉
      (inputTableau X root).label e.finalState.val.1.val) :
    ∃ P : IntervalPartition ρ.domain,
      (inputTableau (Clock := Clock) X root).recognizes JudgementTableau.labels_finite ρ P := by
  apply inputTableau_recognizes_direct_flows X root h e hp hearly hgoal hinit
    (fun i hi => by have := i.isLt; omega) ?_ hfirst ?_ hfinal
  · have heq : (⟨e.count - 1, by have := e.nonempty; omega⟩ : Fin e.count) =
        ⟨0, e.nonempty⟩ := Fin.ext (by change e.count - 1 = 0; omega)
    rw [heq]
    exact hj
  · intro i hi
    have heq : i = ⟨0, e.nonempty⟩ := Fin.ext (by change i.val = 0; have := i.isLt; omega)
    rw [heq] at hi
    exact hfirst hi.1

/-- The terminal position is not a zero-duration signal interval. -/
theorem terminal_rejects_truth {Clock Var : Type*} (ρ : FiniteSignal Var)
    (P : IntervalPartition ρ.domain) (β : ClockValuation Clock) :
    ¬ (Section3.Local.predicate (.plain .truth)).holds ρ P β ⟨P.size, by omega⟩ := by
  rw [local_holds_terminal_iff]
  simp

theorem terminal_accepts_closed_marker {Clock Var : Type*} (ρ : FiniteSignal Var)
    (P : IntervalPartition ρ.domain) (β : ClockValuation Clock) :
    (Section3.Local.marker ●).holds ρ P β ⟨P.size, by omega⟩ := by
  exact (local_holds_terminal_iff ρ P β _).mpr (Or.inr rfl)

theorem terminal_rejects_open_marker {Clock Var : Type*} (ρ : FiniteSignal Var)
    (P : IntervalPartition ρ.domain) (β : ClockValuation Clock) :
    ¬ (Section3.Local.marker ○).holds ρ P β ⟨P.size, by omega⟩ := by
  rw [local_holds_terminal_iff]
  simp

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``inputTableau_recognizes_direct_flows_on_partition,
      ``inputTableau_recognizes_direct_flows,
      ``inputTableau_recognizes_direct_flows_at_horizon,
      ``local_holds_terminal_iff, ``one_flow_via_direct_flows,
      ``terminal_rejects_truth, ``terminal_accepts_closed_marker,
      ``terminal_rejects_open_marker] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
