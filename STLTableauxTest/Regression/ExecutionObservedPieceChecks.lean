import STLTableaux.Automata.Recognition.SingletonLabelPartition

open STLTableau STLTableau.Section4

/-- The intermediate singleton may precede an arbitrary discrete chain.
No equality of modes, empty-reset premise or direct shortcut is required. -/
example {Clock Var State : Type*} (T : Tableau Clock Var State)
    (h : T.TranslationReady) {σ : FiniteSignal T.HAVar}
    (e : (T.toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : T.ProjectsTo σ ρ)
    (i : Fin e.count) (s : (T.toAutomaton h σ.horizon σ.horizon_pos).State)
    (hj : Relation.ReflTransGen (T.toAutomaton h σ.horizon σ.horizon_pos).DiscreteStep
      s (e.start i))
    (a : AtomicProposition Var)
    (ha : Section3.Local.predicate (.plain (.atom a)) ∈ T.label s.val.1.val)
    (u : ρ.Time) (hu : u.val = e.boundary ⟨i.val, by omega⟩) :
    a.Holds (ρ.value u) := by
  have ho := Tableau.ExecutionObservedPiece.beforeFlow i s hj
  apply ho.atom T h _ _ e hp a ha u
  simpa using hu

/-- The last flow endpoint is covered too, provided it is an actual signal
time. No next-flow hypothesis is needed; the final jump chain is used. -/
theorem observed_flow_right_endpoint {Clock Var State : Type*}
    (T : Tableau Clock Var State) (h : T.TranslationReady)
    {σ : FiniteSignal T.HAVar}
    (e : (T.toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : T.ProjectsTo σ ρ)
    (i : Fin e.count) (u : ρ.Time)
    (hu : u.val = e.boundary ⟨i.val + 1, by omega⟩)
    (a : AtomicProposition Var)
    (ha : Section3.Local.predicate (.plain (.atom a)) ∈ T.label (e.start i).val.1.val) :
    a.Holds (ρ.value u) := by
  apply (Tableau.ExecutionObservedPiece.flow i).closed_atom T h _ _ e hp a ha u
  rw [hu]
  exact ⟨e.increasing.monotone (by change i.val ≤ i.val + 1; omega), le_rfl⟩

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Tableau.ExecutionObservedPiece.atom,
      ``Tableau.ExecutionObservedPiece.closed_atom,
      ``Finiteness.execution_labels_hold_on_marked_partition,
      ``observed_flow_right_endpoint,
      ``Tableau.ExecutionObservedPiece.raw_atom,
      ``Finiteness.execution_labels_hold_on_singleton_partition] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
