import STLTableaux.Automata.Composition.SharedParallelExecution
import STLTableaux.Automata.Execution.ObservedFlowExecution

/-! Formula-independent execution projection from local transition maps.
Discrete steps may project to stutters. Standard trajectory closure removes
only the resulting idle flow boundaries, preserving the stop and all visits.
This is not an alternative execution semantics or an assumed composition iff.
-/
namespace STLTableau.HybridAutomaton
variable {M L V N K W : Type*}
variable {H : HybridAutomaton M L V} {G : HybridAutomaton N K W}

/-- Local data for a component projection. None of the fields assumes an
execution/trace projection theorem; those are proved below. -/
structure ExecutionProjection (H : HybridAutomaton M L V) (G : HybridAutomaton N K W) where
  mode : M → N
  coordinate : W → V
  state : H.State → G.State
  state_val : ∀ s, (state s).val = (mode s.val.1, s.val.2 ∘ coordinate)
  initial : ∀ s, s.val ∈ H.initial → (state s).val ∈ G.initial
  flow : ∀ {a b r} {γ : HybridFlow.Curve V r}, H.ContinuousStep a b r γ →
    G.ContinuousStep (state a) (state b) r (fun t => γ t ∘ coordinate)
  discrete : ∀ {a b}, H.DiscreteStep a b →
    Relation.ReflTransGen G.DiscreteStep (state a) (state b)

namespace ExecutionProjection
variable (p : ExecutionProjection H G)

theorem map_closure {a b : H.State} (steps : Relation.ReflTransGen H.DiscreteStep a b) :
    Relation.ReflTransGen G.DiscreteStep (p.state a) (p.state b) :=
  steps.lift' p.state (fun _ _ step => p.discrete step)

variable {σ : FiniteSignal V}

def observedFlow (e : H.PrelimExecution σ) (i : Fin e.count) :
    ObservedFlow G (σ.reindex p.coordinate) where
  start := p.state (e.start i)
  finish := p.state (e.finish i)
  beginTime := e.boundary i.castSucc
  endTime := e.boundary i.succ
  duration := e.duration i
  positive := e.duration_pos i
  duration_eq := e.duration_eq i
  curve := fun t => e.curve i t ∘ p.coordinate
  step := p.flow (e.continuousStep i)
  observe := by
    intro t ht
    exact congrArg (fun v => v ∘ p.coordinate) (e.signal_eq i t ht)

theorem observedChain (e : H.PrelimExecution σ) (k : ℕ) (hk : k < e.count) :
    ∃ word : ObservedFlowChain G (σ.reindex p.coordinate)
        (Relation.ReflTransGen G.DiscreteStep)
        (p.state (e.start ⟨0, e.nonempty⟩)) (e.boundary 0)
        (p.state (e.finish ⟨k, hk⟩)) (e.boundary (⟨k, hk⟩ : Fin e.count).succ),
      (∀ (j : Fin e.count), j.val ≤ k → ∀ s,
        (p.observedFlow e j).VisitsState s → word.VisitsState s) ∧
      (∀ (j : Fin e.count) (hj : j.val + 1 < e.count), j.val < k → ∀ s,
        Relation.ReflTransGen G.DiscreteStep (p.state (e.finish j)) s →
        Relation.ReflTransGen G.DiscreteStep s (p.state (e.start ⟨j.val + 1, hj⟩)) →
        word.VisitsState s) := by
  induction k with
  | zero =>
    refine ⟨.single (p.observedFlow e ⟨0, e.nonempty⟩), ?_, ?_⟩
    · intro j hj s visit
      have same : j = ⟨0, e.nonempty⟩ := Fin.ext (by change j.val = 0; omega)
      change (p.observedFlow e ⟨0, e.nonempty⟩).VisitsState s
      simpa only [same] using visit
    · intro j hj impossible
      omega
  | succ k ih =>
    have old : k < e.count := by omega
    obtain ⟨word, flows, jumps⟩ := ih old
    let i : Fin e.count := ⟨k, old⟩
    let j : Fin e.count := ⟨k + 1, hk⟩
    let f := p.observedFlow e j
    have time : e.boundary i.succ = f.beginTime := rfl
    have step : Relation.ReflTransGen G.DiscreteStep (p.state (e.finish i)) f.start :=
      p.map_closure (e.discreteSteps i hk).to_reflTransGen
    refine ⟨.snoc word f time step, ?_, ?_⟩
    · intro l hl s visit
      by_cases previous : l.val ≤ k
      · exact Or.inl (flows l previous s visit)
      · have same : l = j := Fin.ext (by dsimp [j]; omega)
        exact Or.inr (Or.inr (by simpa only [same] using visit))
    · intro l hl earlier s before after
      by_cases previous : l.val < k
      · exact Or.inl (jumps l hl previous s before after)
      · have same : l = i := Fin.ext (by dsimp [i]; omega)
        subst l
        exact Or.inr (Or.inl ⟨before, after⟩)

/-- The same entire observed prefix is projected. Final state, exact stop
time and all continuous/initial/interflow state visits are preserved. -/
theorem execution (e : H.PrelimExecution σ) :
    ∃ out : G.PrelimExecution (σ.reindex p.coordinate),
      out.finalState = p.state e.finalState ∧
      out.boundary ⟨out.count, by omega⟩ = e.boundary ⟨e.count, by omega⟩ ∧
      ∀ s, e.VisitsState s → out.VisitsState (p.state s) := by
  obtain ⟨word, flows, jumps⟩ := p.observedChain e (e.count - 1)
    (by have := e.nonempty; omega)
  obtain ⟨normal, normalize⟩ := word.normalize
  have lastTime : e.lastIndex.succ = (⟨e.count, by omega⟩ : Fin (e.count + 1)) := by
    apply Fin.ext
    change e.count - 1 + 1 = e.count
    have := e.nonempty
    omega
  have horizon : e.boundary e.lastIndex.succ ≤ σ.horizon := lastTime ▸ e.last_le_horizon
  obtain ⟨out, oi, of, ol, ot, preserve⟩ := normal.toExecution (p.state e.initialState)
    (p.initial e.initialState e.initial_mem)
    e.first_zero (p.map_closure e.initialSteps) horizon
  refine ⟨out, ol, ot.trans (congrArg e.boundary lastTime), ?_⟩
  intro s visit
  rcases visit with ⟨i, t, hs⟩ | ⟨before, after⟩ | ⟨i, hi, before, after⟩
  · apply preserve
    apply normalize
    apply flows i (by have := i.isLt; omega)
    refine ⟨t, ?_⟩
    change (p.state s).val =
      ((p.state (e.start i)).val.1, fun x => e.curve i t (p.coordinate x))
    rw [p.state_val, p.state_val]
    exact congrArg (fun v => (p.mode v.1, v.2 ∘ p.coordinate)) hs
  · exact Or.inr (Or.inl ⟨oi.symm ▸ p.map_closure before,
      of.symm ▸ p.map_closure after⟩)
  · apply preserve
    apply normalize
    exact jumps i hi (by omega) (p.state s) (p.map_closure before) (p.map_closure after)

/-- Full-horizon execution projection is derived from exact stop preservation. -/
theorem full_execution (e : H.PrelimExecution σ) (full : e.ReachesHorizon) :
    ∃ out : G.PrelimExecution (σ.reindex p.coordinate), out.ReachesHorizon ∧
      out.finalState = p.state e.finalState ∧
      ∀ s, e.VisitsState s → out.VisitsState (p.state s) := by
  obtain ⟨out, final, stop, visits⟩ := p.execution e
  exact ⟨out, stop.trans full, final, visits⟩

theorem trajectory (trajectory : H.IsPrelimTrajectory σ) :
    G.IsPrelimTrajectory (σ.reindex p.coordinate) := by
  obtain ⟨e, full⟩ := trajectory
  obtain ⟨out, full, _, _⟩ := p.full_execution e full
  exact ⟨out, full⟩

theorem reaches (goal : Set G.State)
    (reached : H.PrelimReachesState σ {s | p.state s ∈ goal}) :
    G.PrelimReachesState (σ.reindex p.coordinate) goal := by
  obtain ⟨e, s, goal, visit⟩ := reached
  obtain ⟨out, _, _, preserve⟩ := p.execution e
  exact ⟨out, p.state s, goal, preserve s visit⟩

run_elab do
  for n in #[``map_closure, ``execution, ``full_execution, ``trajectory, ``reaches] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{n} uses unexpected axiom {ax}"

end ExecutionProjection
end STLTableau.HybridAutomaton
