import STLTableaux.Automata.Recognition.ExecutionBoundaryObservations
import STLTableaux.Automata.Recognition.ExecutionPathTiming

/-! Observation annotations for a fixed path. This is not a partition, and a
zero-width horizon endpoint carries no local-label satisfaction assertion. -/
namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {σ : FiniteSignal T.HAVar} (e : (T.toAutomaton h τ hτ).Execution σ)

inductive ObservedPath : Path Clock State → ℝ → ℝ → List NNReal → Prop
  | last {incoming s l r} {d : NNReal}
      (piece : T.ExecutionObservedPiece h τ hτ e s l r ∨
        (l = σ.horizon ∧ r = σ.horizon ∧ Section3.Local.terminal ∈ T.label s))
      (duration : r = l + d) :
      ObservedPath (.last incoming s) l r [d]
  | step {incoming s p l r z ds} {d : NNReal}
      (piece : T.ExecutionObservedPiece h τ hτ e s l r)
      (duration : r = l + d)
      (tail : ObservedPath p r z ds) :
      ObservedPath (.step incoming s p) l z (d :: ds)

theorem ObservedPath.total_duration {p l r ds}
    (hp : T.ObservedPath h τ hτ e p l r ds) : r = l + (ds.sum : ℝ) := by
  induction hp with
  | last _ hd => simpa using hd
  | step _ hd _ ih => simpa [hd, add_assoc] using ih

theorem ObservedPath.frame_count {p l r ds}
    (hp : T.ObservedPath h τ hτ e p l r ds)
    (labels : State → Set (Section3.Local Clock Var)) (hf : ∀ s, (labels s).Finite) :
    ds.length = (p.trace labels hf).length := by
  induction hp with
  | last => rfl
  | step _ _ _ ih => simpa [Path.trace, Trace.length] using congrArg Nat.succ ih

/-- One actual jump can be prefixed at the next flow boundary. Iterating this
operation retains every source frame in a finite zero-time jump block.
This annotation operation does not assert incoming-label/edge agreement;
an actual path witness must be retained separately by its caller. -/
theorem ObservedPath.prepend_zero_jump {p z ds}
    (i : Fin e.count)
    (hp : T.ObservedPath h τ hτ e p (e.boundary ⟨i.val, by omega⟩) z ds)
    (s t : (T.toAutomaton h τ hτ).State)
    (hj : (T.toAutomaton h τ hτ).DiscreteStep s t)
    (hsuffix : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep
      t (e.start i))
    (_hfirst : p.firstState = t.val.1.val)
    (incoming : EdgeLabel Clock) :
    T.ObservedPath h τ hτ e (.step incoming s.val.1.val p)
      (e.boundary ⟨i.val, by omega⟩) z (0 :: ds) := by
  apply ObservedPath.step
  · exact .beforeFlow i s ((Relation.ReflTransGen.single hj).trans hsuffix)
  · simp
  · exact hp

/-- Keep the actual edge, incoming guard/reset, timing and observation together
when prefixing a jump. No transitive shortcut edge is introduced. -/
theorem ObservedPath.prepend_zero_jump_with_witness {p z ds}
    (i : Fin e.count) (s t finalState : (T.toAutomaton h τ hτ).State)
    (hp : T.ObservedPath h τ hτ e p (e.boundary ⟨i.val, by omega⟩) z ds)
    (hw : T.ExecutionPathWitness h τ hτ t finalState p)
    (ht : T.TimedPath p t.val.2 finalState.val.2 ds)
    (incoming : EdgeLabel Clock)
    (he : (s.val.1.val, p.firstIncoming, t.val.1.val) ∈ T.edges)
    (hg : T.guardsHold p.firstIncoming s.val.2)
    (hr : t.val.2 = T.reset p.firstIncoming.resets s.val.2)
    (hj : (T.toAutomaton h τ hτ).DiscreteStep s t)
    (hsuffix : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep
      t (e.start i)) :
    T.ExecutionPathWitness h τ hτ s finalState (.step incoming s.val.1.val p) ∧
    T.TimedPath (.step incoming s.val.1.val p) s.val.2 finalState.val.2 (0 :: ds) ∧
    T.ObservedPath h τ hτ e (.step incoming s.val.1.val p)
      (e.boundary ⟨i.val, by omega⟩) z (0 :: ds) := by
  exact ⟨.jump incoming he hg hr hj hw,
    .step incoming _ (ClockElapse.zero T _) hg (hr ▸ ht),
    hp.prepend_zero_jump T h τ hτ e i s t hj hsuffix (hw.valid T h τ hτ).2.1 incoming⟩

/-- Replace only a zero-width first dwell by an actual flow interval. All
tail frames, labels and residence times are retained literally. -/
theorem ObservedPath.prepend_flow {p z ds} (i : Fin e.count)
    (hp : T.ObservedPath h τ hτ e p
      (e.boundary ⟨i.val + 1, by omega⟩) z (0 :: ds))
    (hfirst : p.firstState = (e.finish i).val.1.val) :
    T.ObservedPath h τ hτ e p
      (e.boundary ⟨i.val, by omega⟩) z (e.duration i :: ds) := by
  have hm : p.firstState = (e.start i).val.1.val :=
    hfirst.trans (congrArg Subtype.val (e.continuousStep i).1.symm)
  have hd : e.boundary ⟨i.val + 1, by omega⟩ =
      e.boundary ⟨i.val, by omega⟩ + (e.duration i : ℝ) := by
    have := e.duration_eq i
    linarith
  have ho : T.ExecutionObservedPiece h τ hτ e p.firstState
      (e.boundary ⟨i.val, by omega⟩) (e.boundary ⟨i.val + 1, by omega⟩) := by
    rw [hm]
    exact .flow i
  cases hp with
  | last piece duration =>
      simp only [NNReal.coe_zero, add_zero] at duration
      subst z
      exact .last (Or.inl ho) hd
  | step piece duration tail =>
      have hr := duration
      simp only [NNReal.coe_zero, add_zero] at hr
      subst hr
      exact .step ho hd tail

/-- Synchronize the observation update with the actual flow witness and its
clock traversal. The path itself and every tail frame remain unchanged. -/
theorem ObservedPath.prepend_flow_with_witness {p z ds}
    (i : Fin e.count) (finalState : (T.toAutomaton h τ hτ).State)
    (hp : T.ObservedPath h τ hτ e p
      (e.boundary ⟨i.val + 1, by omega⟩) z (0 :: ds))
    (hw : T.ExecutionPathWitness h τ hτ (e.finish i) finalState p)
    (ht : T.TimedPath p (e.finish i).val.2 finalState.val.2 (0 :: ds)) :
    T.ExecutionPathWitness h τ hτ (e.start i) finalState p ∧
    T.TimedPath p (e.start i).val.2 finalState.val.2 (e.duration i :: ds) ∧
    T.ObservedPath h τ hτ e p
      (e.boundary ⟨i.val, by omega⟩) z (e.duration i :: ds) := by
  refine ⟨.flow (e.duration i) (e.curve i) (e.continuousStep i) hw, ?_,
    hp.prepend_flow T h τ hτ e i (hw.valid T h τ hτ).2.1⟩
  have hc := T.continuousStep_clockElapse h τ hτ (e.continuousStep i)
  cases ht with
  | last incoming s he =>
      simpa using (TimedPath.last (T := T) incoming s (hc.add T he))
  | step incoming s he hg tail =>
      simpa using (TimedPath.step (T := T) incoming s (hc.add T he) hg tail)

end STLTableau.Section4.Tableau
