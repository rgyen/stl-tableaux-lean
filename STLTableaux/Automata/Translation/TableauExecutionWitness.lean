import STLTableaux.Automata.Recognition.TableauExecutionPath

/-! Retain the actual continuous steps, jump guards and resets while extracting
the path. Flows do not insert tableau edges. No partition or marker
compatibility is assumed or concluded here. -/
namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)

def ExecutionStep (s t : (T.toAutomaton h τ hτ).State) : Prop :=
  (T.toAutomaton h τ hτ).DiscreteStep s t ∨
    ∃ (r : NNReal) (γ : Set.Icc (0 : ℝ) r → T.HAVar → ℝ),
      (T.toAutomaton h τ hτ).ContinuousStep s t r γ

/-- A path with the actual semantic states and continuous/jump witnesses.
Each jump uses its destination's incoming label, with its real guard/reset
equations. A continuous step changes valuations but not the tableau path. -/
inductive ExecutionPathWitness : (T.toAutomaton h τ hτ).State →
    (T.toAutomaton h τ hτ).State → Path Clock State → Prop
  | stop (s) (incoming) : ExecutionPathWitness s s (.last incoming s.val.1.val)
  | flow {s u t p} (r : NNReal) (γ : Set.Icc (0 : ℝ) r → T.HAVar → ℝ)
      (hc : (T.toAutomaton h τ hτ).ContinuousStep s u r γ)
      (tail : ExecutionPathWitness u t p) : ExecutionPathWitness s t p
  | jump {s u t p} (incoming)
      (edge : (s.val.1.val, p.firstIncoming, u.val.1.val) ∈ T.edges)
      (guard : T.guardsHold p.firstIncoming s.val.2)
      (reset : u.val.2 = T.reset p.firstIncoming.resets s.val.2)
      (step : (T.toAutomaton h τ hτ).DiscreteStep s u)
      (tail : ExecutionPathWitness u t p) :
      ExecutionPathWitness s t (.step incoming s.val.1.val p)

theorem ExecutionPathWitness.valid {s t p}
    (hw : T.ExecutionPathWitness h τ hτ s t p) :
    p.valid T ∧ p.firstState = s.val.1.val ∧ p.lastState = t.val.1.val := by
  induction hw with
  | stop s incoming => exact ⟨s.val.1.property, rfl, rfl⟩
  | flow r γ hc hw ih =>
      exact ⟨ih.1, ih.2.1.trans (congrArg Subtype.val hc.1.symm), ih.2.2⟩
  | jump incoming he hg hr hj hw ih =>
      exact ⟨⟨(h.edge_states _ he).1, ih.1, by simpa only [ih.2.1] using he⟩,
        rfl, ih.2.2⟩

theorem executionSteps_path {s t : (T.toAutomaton h τ hτ).State}
    (steps : Relation.ReflTransGen (T.ExecutionStep h τ hτ) s t)
    (incoming : EdgeLabel Clock) :
    ∃ p, T.ExecutionPathWitness h τ hτ s t p ∧ p.firstIncoming = incoming := by
  induction steps using Relation.ReflTransGen.head_induction_on generalizing incoming with
  | refl => exact ⟨_, .stop _ incoming, rfl⟩
  | @head s u hs rest ih =>
      rcases hs with hj | ⟨r, γ, hc⟩
      · obtain ⟨l, he, hg, hr, _⟩ := (T.discreteStep_iff h τ hτ).mp hj
        obtain ⟨p, hp, hin⟩ := ih l
        refine ⟨.step incoming s.val.1.val p, ?_, rfl⟩
        exact .jump incoming (hin ▸ he) (hin ▸ hg) (hin ▸ hr) hj hp
      · obtain ⟨p, hp, hin⟩ := ih incoming
        exact ⟨p, .flow r γ hc hp, hin⟩

theorem discreteSteps_executionSteps {s t : (T.toAutomaton h τ hτ).State}
    (hj : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep s t) :
    Relation.ReflTransGen (T.ExecutionStep h τ hτ) s t := by
  induction hj with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (Or.inl step)

/-- Unfold the supplied execution itself, including its initial and final
jump blocks. This construction needs no marker or label-satisfaction premise. -/
theorem execution_steps {σ : FiniteSignal T.HAVar}
    (e : (T.toAutomaton h τ hτ).Execution σ) :
    Relation.ReflTransGen (T.ExecutionStep h τ hτ) e.initialState e.finalState := by
  have hs : ∀ k (hk : k < e.count),
      Relation.ReflTransGen (T.ExecutionStep h τ hτ) e.initialState (e.start ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero => intro hk; exact T.discreteSteps_executionSteps h τ hτ e.initialSteps
    | succ k ih =>
        intro hk
        have hk' : k < e.count := by omega
        exact ((ih hk').tail (Or.inr ⟨_, _, e.continuousStep ⟨k, hk'⟩⟩)).trans
          (T.discreteSteps_executionSteps h τ hτ
            (e.discreteSteps ⟨k, hk'⟩ hk).to_reflTransGen)
  have hk : e.count - 1 < e.count := by have := e.nonempty; omega
  exact ((hs _ hk).tail (Or.inr ⟨_, _, e.continuousStep ⟨e.count - 1, hk⟩⟩)).trans
    (T.discreteSteps_executionSteps h τ hτ e.finalSteps)

/-- The accepting path and its real execution evidence are returned together.
Initialization retains the actual pre-reset valuation. -/
theorem execution_accepting_path_witness {σ : FiniteSignal T.HAVar}
    (e : (T.toAutomaton h τ hτ).Execution σ)
    (goal : e.finalState.val.1 ∈ T.goalModes) :
    ∃ p, p.run T ∧ p.accepting T ∧
      T.ExecutionPathWitness h τ hτ e.initialState e.finalState p ∧
      ∃ v : T.HAVar → ℝ, T.guardsHold p.firstIncoming v ∧
        e.initialState.val.2 = T.initialReset p.firstIncoming.resets v := by
  obtain ⟨incoming, hi, v, hg, hr⟩ := e.initial_mem
  obtain ⟨p, hw, hin⟩ := T.executionSteps_path h τ hτ (T.execution_steps h τ hτ e) incoming
  obtain ⟨hv, hfirst, hlast⟩ := hw.valid T h τ hτ
  refine ⟨p, ⟨hv, ?_⟩, ⟨hv, ?_⟩, hw, v, ?_, ?_⟩
  · simpa only [hin, hfirst] using hi
  · rw [hlast]
    exact goal
  · simpa only [hin] using hg
  · simpa only [hin] using hr

end STLTableau.Section4.Tableau
