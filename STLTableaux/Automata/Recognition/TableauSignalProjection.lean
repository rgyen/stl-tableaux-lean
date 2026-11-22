import STLTableaux.Automata.Recognition.TableauExecutionTime
import STLTableaux.Automata.Recognition.TableauExecutionPath

/-! Atomic-label satisfaction along the executed signal prefix.
Projection identifies only declared real coordinates, never clock coordinates.
No claim is made about the unconstrained suffix or a value at the horizon. -/
namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)

/-- An augmented signal agrees with the original signal on declared variables
at equal times. Variables outside the tableau support remain unrestricted. -/
def ProjectsTo (σ : FiniteSignal T.HAVar) (ρ : FiniteSignal Var) : Prop :=
  σ.horizon = ρ.horizon ∧ ∀ (t : σ.Time) (u : ρ.Time), t.val = u.val →
    ∀ x : T.realVariables, σ.value t (.inl x) = ρ.value u x.val

/-- Reachability for an original signal existentially supplies only the
extra coordinates. The automaton horizon is the signal's horizon. -/
def ReachesSignal (h : T.TranslationReady) (ρ : FiniteSignal Var) : Prop :=
  ∃ σ : FiniteSignal T.HAVar, T.ProjectsTo σ ρ ∧
    (T.toAutomaton h ρ.horizon ρ.horizon_pos).Reaches σ T.goalModes

variable (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)

theorem state_atom {s : (T.toAutomaton h τ hτ).State}
    (a : AtomicProposition Var)
    (ha : Section3.Local.predicate (.plain (.atom a)) ∈ T.label s.val.1.val) :
    T.atomHolds a s.val.2 := s.property.1 a ha

theorem discreteSteps_realVariable_preserved
    {s s' : (T.toAutomaton h τ hτ).State}
    (hj : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep s s')
    (x : T.realVariables) : s'.val.2 (.inl x) = s.val.2 (.inl x) := by
  induction hj with
  | refl => rfl
  | tail _ hstep ih => exact (T.jump_realVariable_preserved h τ hτ hstep x).trans ih

variable {σ : FiniteSignal T.HAVar} (e : (T.toAutomaton h τ hτ).Execution σ)

theorem execution_curve_atom (i : Fin e.count)
    (a : AtomicProposition Var)
    (ha : Section3.Local.predicate (.plain (.atom a)) ∈ T.label (e.start i).val.1.val)
    (u : Set.Icc (0 : ℝ) (e.duration i)) : T.atomHolds a (e.curve i u) :=
  ((e.continuousStep i).2.2.2 u).2.1 a ha

theorem execution_signal_atom (i : Fin e.count) (t : σ.Time)
    (ht : e.boundary ⟨i.val, by omega⟩ ≤ t.val ∧
      t.val < e.boundary ⟨i.val + 1, by omega⟩)
    (a : AtomicProposition Var)
    (ha : Section3.Local.predicate (.plain (.atom a)) ∈ T.label (e.start i).val.1.val) :
    T.atomHolds a (σ.value t) := by
  change e.boundary i.castSucc ≤ t.val ∧ t.val < e.boundary i.succ at ht
  by_cases positive : 0 < t.val
  · rw [e.signal_eq i t ht positive]
    exact T.execution_curve_atom h τ hτ e i a ha _
  · have zero : t.val = 0 := le_antisymm (le_of_not_gt positive) t.property.1
    have index : i = ⟨0, e.nonempty⟩ := by
      apply Fin.ext
      change i.val = 0
      have lower := e.increasing.monotone (Fin.zero_le i.castSucc)
      have first : e.boundary 0 = 0 := e.first_zero
      rw [first] at lower
      have boundary : e.boundary i.castSucc = e.boundary 0 := by
        rw [first]
        linarith [ht.1]
      simpa using congrArg Fin.val (e.increasing.injective boundary)
    subst i
    have time : t = ⟨0, le_rfl, σ.horizon_pos⟩ := Subtype.ext zero
    rw [time, e.initial_signal_eq]
    obtain ⟨support, holds⟩ := T.state_atom h τ hτ a ha
    refine ⟨support, ?_⟩
    simpa only [T.discreteSteps_realVariable_preserved h τ hτ e.initialSteps] using holds

/-- Every atomic label of the flow mode holds on its half-open interval in
the original signal. The right endpoint is deliberately not asserted here. -/
theorem execution_projected_atom {ρ : FiniteSignal Var} (hp : T.ProjectsTo σ ρ)
    (i : Fin e.count) (t : σ.Time) (u : ρ.Time) (htu : t.val = u.val)
    (ht : e.boundary ⟨i.val, by omega⟩ ≤ t.val ∧
      t.val < e.boundary ⟨i.val + 1, by omega⟩)
    (a : AtomicProposition Var)
    (ha : Section3.Local.predicate (.plain (.atom a)) ∈ T.label (e.start i).val.1.val) :
    a.Holds (ρ.value u) :=
  (T.atomHolds_iff a (σ.value t) (ρ.value u)
    (h.atom_variables _ (e.start i).val.1.property a ha) (hp.2 t u htu)).mp
    (T.execution_signal_atom h τ hτ e i t ht a ha)

/-- Intermediate zero-time states have the same real coordinates as their
destination. Their atomic labels can therefore be checked at that destination.
This does not identify a final flow endpoint with a signal value at `τ`. -/
theorem discreteSteps_source_atom_at_destination
    {s s' : (T.toAutomaton h τ hτ).State}
    (hj : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep s s')
    (a : AtomicProposition Var)
    (ha : Section3.Local.predicate (.plain (.atom a)) ∈ T.label s.val.1.val) :
    T.atomHolds a s'.val.2 := by
  obtain ⟨hs, hv⟩ := T.state_atom h τ hτ a ha
  refine ⟨hs, ?_⟩
  simpa only [T.discreteSteps_realVariable_preserved h τ hτ hj] using hv

theorem execution_start_value (i : Fin e.count) (t : σ.Time)
    (ht : t.val = e.boundary ⟨i.val, by omega⟩) (positive : 0 < t.val) :
    σ.value t = (e.start i).val.2 := by
  have hlt : t.val < e.boundary ⟨i.val + 1, by omega⟩ := by
    rw [ht]
    exact e.increasing (by change i.val < i.val + 1; omega)
  have hv := e.signal_eq i t ⟨le_of_eq ht.symm, hlt⟩ positive
  simpa only [ht, sub_self, (e.continuousStep i).2.1] using hv

/-- Jumps of `toAutomaton` preserve the real-valued variables, so the initial
observation agrees with the start of the first continuous transition. -/
theorem execution_start_realValue (i : Fin e.count) (t : σ.Time)
    (ht : t.val = e.boundary i.castSucc) (x : T.realVariables) :
    σ.value t (.inl x) = (e.start i).val.2 (.inl x) := by
  by_cases positive : 0 < t.val
  · exact congrFun (T.execution_start_value h τ hτ e i t ht positive) (.inl x)
  · have zero : t.val = 0 := le_antisymm (le_of_not_gt positive) t.property.1
    have index : i = ⟨0, e.nonempty⟩ := by
      apply Fin.ext
      change i.val = 0
      have boundary : e.boundary i.castSucc = e.boundary 0 := ht.symm.trans (zero.trans e.first_zero.symm)
      simpa using congrArg Fin.val (e.increasing.injective boundary)
    subst i
    have time : t = ⟨0, le_rfl, σ.horizon_pos⟩ := Subtype.ext zero
    rw [time, e.initial_signal_eq]
    exact (T.discreteSteps_realVariable_preserved h τ hτ e.initialSteps x).symm

/-- Atomic labels of zero-time states immediately before a flow hold at the
same starting signal time, including initial discrete chains. -/
theorem execution_projected_preflow_atom {ρ : FiniteSignal Var}
    (hp : T.ProjectsTo σ ρ) (i : Fin e.count)
    {s : (T.toAutomaton h τ hτ).State}
    (hj : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep s (e.start i))
    (t : σ.Time) (u : ρ.Time) (htu : t.val = u.val)
    (ht : t.val = e.boundary ⟨i.val, by omega⟩)
    (a : AtomicProposition Var)
    (ha : Section3.Local.predicate (.plain (.atom a)) ∈ T.label s.val.1.val) :
    a.Holds (ρ.value u) := by
  have hv := T.discreteSteps_source_atom_at_destination h τ hτ hj a ha
  obtain ⟨support, holds⟩ := hv
  have hv : T.atomHolds a (σ.value t) := by
    refine ⟨support, ?_⟩
    simpa only [T.execution_start_realValue h τ hτ e i t ht] using holds
  exact (T.atomHolds_iff a _ _
    (h.atom_variables _ s.val.1.property a ha) (hp.2 t u htu)).mp hv

/-- At an early final endpoint, atoms of the final state and of preceding
zero-time states hold in the original signal. Resets may change clocks but
preserve real variables. At the horizon no signal time `t` exists. -/
theorem execution_projected_final_atom {ρ : FiniteSignal Var}
    (hp : T.ProjectsTo σ ρ)
    {s : (T.toAutomaton h τ hτ).State}
    (hj : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep s e.finalState)
    (t : σ.Time) (u : ρ.Time) (htu : t.val = u.val)
    (ht : t.val = e.boundary ⟨e.count, by omega⟩)
    (a : AtomicProposition Var)
    (ha : Section3.Local.predicate (.plain (.atom a)) ∈ T.label s.val.1.val) :
    a.Holds (ρ.value u) := by
  have hv := T.discreteSteps_source_atom_at_destination h τ hτ hj a ha
  rw [← e.final_signal_eq t ht] at hv
  exact (T.atomHolds_iff a _ _
    (h.atom_variables _ s.val.1.property a ha) (hp.2 t u htu)).mp hv

/-- Internal flow endpoints agree with the observed next-flow value on real
variables, even when a nonempty chain of zero-time jumps intervenes. This does
not assert equality of clocks, which may be reset by that chain. -/
theorem execution_finish_realValue (i : Fin e.count) (hi : i.val + 1 < e.count)
    (t : σ.Time) (ht : t.val = e.boundary ⟨i.val + 1, by omega⟩)
    (x : T.realVariables) :
    (e.finish i).val.2 (.inl x) = σ.value t (.inl x) := by
  rw [T.execution_start_realValue h τ hτ e ⟨i.val + 1, hi⟩ t ht]
  exact (T.discreteSteps_realVariable_preserved h τ hτ
    (e.discreteSteps i hi).to_reflTransGen x).symm

/-- The preceding mode's atoms hold at an internal boundary in the original
signal. The final endpoint has no analogous next-flow observation premise. -/
theorem execution_projected_finish_atom {ρ : FiniteSignal Var}
    (hp : T.ProjectsTo σ ρ) (i : Fin e.count) (hi : i.val + 1 < e.count)
    (t : σ.Time) (u : ρ.Time) (htu : t.val = u.val)
    (ht : t.val = e.boundary ⟨i.val + 1, by omega⟩)
    (a : AtomicProposition Var)
    (ha : Section3.Local.predicate (.plain (.atom a)) ∈ T.label (e.start i).val.1.val) :
    a.Holds (ρ.value u) := by
  have ha' : Section3.Local.predicate (.plain (.atom a)) ∈
      T.label (e.finish i).val.1.val := by
    rwa [← (e.continuousStep i).1]
  exact T.execution_projected_preflow_atom h τ hτ e hp ⟨i.val + 1, hi⟩
    (e.discreteSteps i hi).to_reflTransGen t u htu ht a ha'

/-- Nonfinal positive flows satisfy their atomic labels on the closed interval,
using the next flow at the right endpoint and the ordinary observation inside.
No continuity or extra invariant on an unexecuted suffix is assumed. -/
theorem execution_projected_closed_atom {ρ : FiniteSignal Var}
    (hp : T.ProjectsTo σ ρ) (i : Fin e.count) (hi : i.val + 1 < e.count)
    (t : σ.Time) (u : ρ.Time) (htu : t.val = u.val)
    (ht : e.boundary ⟨i.val, by omega⟩ ≤ t.val ∧
      t.val ≤ e.boundary ⟨i.val + 1, by omega⟩)
    (a : AtomicProposition Var)
    (ha : Section3.Local.predicate (.plain (.atom a)) ∈ T.label (e.start i).val.1.val) :
    a.Holds (ρ.value u) := by
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · exact T.execution_projected_atom h τ hτ e hp i t u htu ⟨ht.1, hlt⟩ a ha
  · exact T.execution_projected_finish_atom h τ hτ e hp i hi t u htu heq a ha

theorem reachesSignal_accepting_run {ρ : FiniteSignal Var}
    (hr : T.ReachesSignal h ρ) :
    ∃ p : Path Clock State, p.run T ∧ p.accepting T := by
  obtain ⟨σ, _, he⟩ := hr
  exact T.reaches_accepting_run h ρ.horizon ρ.horizon_pos he

end STLTableau.Section4.Tableau
