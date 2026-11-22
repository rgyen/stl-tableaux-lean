import STLTableaux.Automata.Recognition.ExecutionObservedPath

/-! Prepend an actual finite zero-time jump block. A step whose full semantic
state is unchanged may be omitted; all other intermediate frames are retained.
Incoming labels are chosen from actual jumps, never fabricated. -/
namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {σ : FiniteSignal T.HAVar} (e : (T.toAutomaton h τ hτ).Execution σ)

def ObservedSuffix (source finalState : (T.toAutomaton h τ hτ).State)
    (time stop : ℝ) (incoming : EdgeLabel Clock) : Prop :=
  ∃ p ds, T.ExecutionPathWitness h τ hτ source finalState p ∧
    T.TimedPath p source.val.2 finalState.val.2 ds ∧
    T.ObservedPath h τ hτ e p time stop ds ∧ p.firstIncoming = incoming

/-- The observation hypothesis concerns actual states on this jump block.
It is discharged by `beforeFlow` or early `atFinal`, not by partition labels. -/
theorem prepend_observed_discrete_block
    (target finalState source : (T.toAutomaton h τ hτ).State)
    (time stop : ℝ)
    (steps : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep source target)
    (observe : ∀ s, Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep s target →
      T.ExecutionObservedPiece h τ hτ e s.val.1.val time time)
    (build : ∀ incoming, T.ObservedSuffix h τ hτ e target finalState time stop incoming)
    (incoming : EdgeLabel Clock) :
    T.ObservedSuffix h τ hτ e source finalState time stop incoming := by
  classical
  induction steps using Relation.ReflTransGen.head_induction_on generalizing incoming with
  | refl => exact build incoming
  | @head s t hj rest ih =>
      by_cases heq : s = t
      · subst t
        exact ih incoming
      obtain ⟨label, he, hg, hr, _⟩ := (T.discreteStep_iff h τ hτ).mp hj
      obtain ⟨p, ds, hw, ht, hp, hin⟩ := ih label
      have hpfirst := (hw.valid T h τ hτ).2.1
      refine ⟨.step incoming s.val.1.val p, 0 :: ds, ?_, ?_, ?_, rfl⟩
      · exact .jump incoming (by simpa only [hin, hpfirst] using he)
          (hin ▸ hg) (hin ▸ hr) hj hw
      · exact .step incoming _ (ClockElapse.zero T _) (hin ▸ hg) ((hin ▸ hr) ▸ ht)
      · exact .step (observe s ((Relation.ReflTransGen.single hj).trans rest))
          (by simp) hp

/-- A nonempty block supplies an explicit zero head duration, which can then
be replaced by its preceding actual flow without changing the tail. -/
theorem prepend_observed_nonempty_discrete_block
    (target finalState source : (T.toAutomaton h τ hτ).State)
    (time stop : ℝ)
    (steps : Relation.TransGen (T.toAutomaton h τ hτ).DiscreteStep source target)
    (observe : ∀ s, Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep s target →
      T.ExecutionObservedPiece h τ hτ e s.val.1.val time time)
    (build : ∀ incoming, T.ObservedSuffix h τ hτ e target finalState time stop incoming)
    (incoming : EdgeLabel Clock) :
    ∃ p ds, T.ExecutionPathWitness h τ hτ source finalState p ∧
      T.TimedPath p source.val.2 finalState.val.2 (0 :: ds) ∧
      T.ObservedPath h τ hτ e p time stop (0 :: ds) ∧ p.firstIncoming = incoming := by
  obtain ⟨middle, hj, rest⟩ := Relation.TransGen.head'_iff.mp steps
  obtain ⟨label, he, hg, hr, _⟩ := (T.discreteStep_iff h τ hτ).mp hj
  obtain ⟨p, ds, hw, ht, hp, hin⟩ :=
    T.prepend_observed_discrete_block h τ hτ e target finalState middle time stop rest
      observe build label
  have hpfirst := (hw.valid T h τ hτ).2.1
  refine ⟨.step incoming source.val.1.val p, ds, ?_, ?_, ?_, rfl⟩
  · exact .jump incoming (by simpa only [hin, hpfirst] using he)
      (hin ▸ hg) (hin ▸ hr) hj hw
  · exact .step incoming _ (ClockElapse.zero T _) (hin ▸ hg) ((hin ▸ hr) ▸ ht)
  · exact .step (observe source ((Relation.ReflTransGen.single hj).trans rest))
      (by simp) hp

theorem prepend_beforeFlow_discrete_block
    (i : Fin e.count) (finalState source : (T.toAutomaton h τ hτ).State) (stop : ℝ)
    (steps : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep source (e.start i))
    (build : ∀ incoming, T.ObservedSuffix h τ hτ e (e.start i) finalState
      (e.boundary ⟨i.val, by omega⟩) stop incoming)
    (incoming : EdgeLabel Clock) :
    T.ObservedSuffix h τ hτ e source finalState
      (e.boundary ⟨i.val, by omega⟩) stop incoming :=
  T.prepend_observed_discrete_block h τ hτ e (e.start i) finalState source _ stop steps
    (fun s hs => .beforeFlow i s hs) build incoming

end STLTableau.Section4.Tableau
