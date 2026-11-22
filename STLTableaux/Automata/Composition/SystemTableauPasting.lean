import STLTableaux.Automata.Composition.SystemTableauComposition
import STLTableaux.Automata.Composition.SharedParallelPasting
import STLTableaux.Automata.Execution.ExecutionTimeRefinement

/-! Constructs valuations for the composed hybrid automaton. The system
coordinates retain their values. The clocks and boundary coordinates of the
translated automaton have distinct names. The transition constructions use
the supplied component transitions, including their guards and resets. -/
namespace STLTableau.HybridFlow
variable {V : Type*} {r s : NNReal}

/-- Transport a closed curve across equality of durations, without changing
any time value or coordinate. -/
def castCurve (γ : Curve V r) (same : s = r) : Curve V s :=
  fun t => γ ⟨t.val, by simpa only [same] using t.property⟩

end STLTableau.HybridFlow

namespace STLTableau.HybridAutomaton
variable {M L V : Type*} {H : HybridAutomaton M L V}

theorem ContinuousStep.castDuration {a b : H.State} {r s : NNReal}
    {γ : HybridFlow.Curve V r} (step : H.ContinuousStep a b r γ) (same : s = r) :
    H.ContinuousStep a b s (HybridFlow.castCurve γ same) := by
  subst s
  exact step

end STLTableau.HybridAutomaton

namespace STLTableau.Section4.Tableau
open HybridAutomaton
variable {Clock Var State Mode Label : Type*} (T : Tableau Clock Var State)

def joinValuation (v : Var → ℝ) (w : T.TypedVar → ℝ) : T.CompositionVar → ℝ :=
  fun x => match x.val with
    | .inl y => v y
    | .inr (.inl c) => w (.inl (.inr c))
    | .inr (.inr b) => w (.inr b)

theorem joinValuation_system (v : Var → ℝ) (w : T.TypedVar → ℝ) :
    T.joinValuation v w ∘ T.systemCoordinate = v := rfl

theorem joinValuation_tableau (v : Var → ℝ) (w : T.TypedVar → ℝ)
    (agree : ∀ x : T.realVariables, v x.val = w (.inl (.inl x))) :
    T.joinValuation v w ∘ T.tableauCoordinate = w := by
  funext x
  cases x with
  | inl x =>
    cases x with
    | inl x => exact agree x
    | inr c => rfl
  | inr b => rfl

/-- Join the signal of the translated automaton to the system signal on their
common time domain. -/
def joinSignal (ρ : FiniteSignal Var) (aug : FiniteSignal T.TypedVar)
    (proj : T.TypedProjectsTo aug ρ) : FiniteSignal T.CompositionVar where
  horizon := ρ.horizon
  horizon_pos := ρ.horizon_pos
  value := fun t => T.joinValuation (ρ.value t)
    (aug.value ⟨t.val, by rw [proj.1]; exact t.property⟩)

theorem joinSignal_system (ρ : FiniteSignal Var) (aug : FiniteSignal T.TypedVar)
    (proj : T.TypedProjectsTo aug ρ) : T.systemSignal (T.joinSignal ρ aug proj) = ρ := by
  cases ρ
  rfl

theorem joinSignal_tableau (ρ : FiniteSignal Var) (aug : FiniteSignal T.TypedVar)
    (proj : T.TypedProjectsTo aug ρ) : T.tableauSignal (T.joinSignal ρ aug proj) = aug := by
  rcases ρ with ⟨τ, τpos, values⟩
  rcases aug with ⟨u, upos, augmented⟩
  rcases proj with ⟨time, proj⟩
  dsimp only at time
  subst u
  dsimp only [tableauSignal, joinSignal, FiniteSignal.reindex]
  congr 1
  funext t
  exact T.joinValuation_tableau (values t) (augmented t) (fun x => (proj t t rfl x).symm)

variable (H : HybridAutomaton Mode Label Var) (h : T.TranslationReady) (τ : ℝ)
local notation "A" => T.prelimAutomaton h τ
local notation "P" => T.systemTableauAutomaton H h τ
local notation "left" => H.leftStateOn (A) T.systemVarName T.tableauVarName
local notation "right" => H.rightStateOn (A) T.systemVarName T.tableauVarName

def joinState (s : H.State) (m : (A).State)
    (agree : ∀ x : T.realVariables, s.val.2 x.val = m.val.2 (.inl (.inl x))) : (P).State :=
  ⟨((s.val.1, m.val.1), T.joinValuation s.val.2 m.val.2), by
    change (s.val.1, T.joinValuation s.val.2 m.val.2 ∘ T.systemCoordinate) ∈ H.invariant ∧
      (m.val.1, T.joinValuation s.val.2 m.val.2 ∘ T.tableauCoordinate) ∈ (A).invariant
    rw [T.joinValuation_system, T.joinValuation_tableau _ _ agree]
    exact ⟨s.property, m.property⟩⟩

theorem joinState_system (s : H.State) (m : (A).State) (agree) :
    left (T.joinState H h τ s m agree) = s := Subtype.ext rfl

theorem joinState_tableau (s : H.State) (m : (A).State) (agree) :
    right (T.joinState H h τ s m agree) = m := by
  apply Subtype.ext
  exact Prod.ext rfl (T.joinValuation_tableau _ _ agree)

theorem joinState_initial (s : H.State) (m : (A).State) (agree)
    (system : s.val ∈ H.initial) (monitor : m.val ∈ (A).initial) :
    (T.joinState H h τ s m agree).val ∈ (P).initial := by
  apply (H.parallelOn_initial_iff (A) T.systemVarName T.tableauVarName _).mpr
  rw [T.joinState_system, T.joinState_tableau]
  exact ⟨system, monitor⟩

/-- Component endpoint observations supply the compatible joint endpoint. -/
theorem curve_initial_agreement {s s' : H.State} {m m' : (A).State} {r : NNReal}
    {γ : HybridFlow.Curve Var r} {δ : HybridFlow.Curve T.TypedVar r}
    (system : H.ContinuousStep s s' r γ) (monitor : (A).ContinuousStep m m' r δ)
    (agree : ∀ t x, γ t x.val = δ t (.inl (.inl x))) :
    ∀ x : T.realVariables, s.val.2 x.val = m.val.2 (.inl (.inl x)) := by
  intro x
  rw [← system.2.1, ← monitor.2.1]
  exact agree _ x

theorem curve_final_agreement {s s' : H.State} {m m' : (A).State} {r : NNReal}
    {γ : HybridFlow.Curve Var r} {δ : HybridFlow.Curve T.TypedVar r}
    (system : H.ContinuousStep s s' r γ) (monitor : (A).ContinuousStep m m' r δ)
    (agree : ∀ t x, γ t x.val = δ t (.inl (.inl x))) :
    ∀ x : T.realVariables, s'.val.2 x.val = m'.val.2 (.inl (.inl x)) := by
  intro x
  rw [← system.2.2.1, ← monitor.2.2.1]
  exact agree _ x

/-- Actual same-duration component flows yield an actual product flow.
Agreement is on the closed curves, not just half-open signal observations. -/
theorem paste_continuous {s s' : H.State} {m m' : (A).State} {r : NNReal}
    {γ : HybridFlow.Curve Var r} {δ : HybridFlow.Curve T.TypedVar r}
    (system : H.ContinuousStep s s' r γ) (monitor : (A).ContinuousStep m m' r δ)
    (agree : ∀ t x, γ t x.val = δ t (.inl (.inl x))) :
    (P).ContinuousStep
      (T.joinState H h τ s m (T.curve_initial_agreement H h τ system monitor agree))
      (T.joinState H h τ s' m' (T.curve_final_agreement H h τ system monitor agree)) r
      (fun t => T.joinValuation (γ t) (δ t)) := by
  apply (H.parallelOn_continuous_iff (A) T.systemVarName T.tableauVarName).mpr
  rw [T.joinState_system, T.joinState_system, T.joinState_tableau, T.joinState_tableau]
  constructor
  · exact system
  · have curve : (fun t x => T.joinValuation (γ t) (δ t) (T.tableauCoordinate x)) = δ := by
      funext t
      exact T.joinValuation_tableau _ _ (agree t)
    change (A).ContinuousStep m m' r
      (fun t x => T.joinValuation (γ t) (δ t) (T.tableauCoordinate x))
    rw [curve]
    exact monitor

variable {ρ : FiniteSignal Var} {aug : FiniteSignal T.TypedVar}

theorem flow_duration_eq (f : ObservedFlow H ρ) (g : ObservedFlow (A) aug)
    (start : f.beginTime = g.beginTime) (finish : f.endTime = g.endTime) :
    f.duration = g.duration := by
  apply Subtype.ext
  change (f.duration : ℝ) = (g.duration : ℝ)
  rw [f.duration_eq, g.duration_eq, start, finish]

/-- Paste actual observed component flows on one common cell. Equal duration
is derived from its time endpoints; both half-open observations are retained
on the constructed joint signal. -/
noncomputable def pasteObservedFlow (proj : T.TypedProjectsTo aug ρ)
    (f : ObservedFlow H ρ) (g : ObservedFlow (A) aug)
    (start : f.beginTime = g.beginTime) (finish : f.endTime = g.endTime)
    (agree : ∀ t x, f.curve t x.val =
      HybridFlow.castCurve g.curve (T.flow_duration_eq H h τ f g start finish) t (.inl (.inl x))) :
    ObservedFlow (P) (T.joinSignal ρ aug proj) where
  start := T.joinState H h τ f.start g.start (T.curve_initial_agreement H h τ f.step
    (g.step.castDuration (T.flow_duration_eq H h τ f g start finish)) agree)
  finish := T.joinState H h τ f.finish g.finish (T.curve_final_agreement H h τ f.step
    (g.step.castDuration (T.flow_duration_eq H h τ f g start finish)) agree)
  beginTime := f.beginTime
  endTime := f.endTime
  duration := f.duration
  positive := f.positive
  duration_eq := f.duration_eq
  curve := fun t => T.joinValuation (f.curve t)
    (HybridFlow.castCurve g.curve (T.flow_duration_eq H h τ f g start finish) t)
  step := T.paste_continuous H h τ f.step
    (g.step.castDuration (T.flow_duration_eq H h τ f g start finish)) agree
  observe := by
    intro t ht
    apply congrArg₂ (T.joinValuation)
    · exact f.observe t ht
    · let u : aug.Time := ⟨t.val, by rw [proj.1]; exact t.property⟩
      have observed := g.observe u ⟨by dsimp [u]; linarith [ht.1],
        by dsimp [u]; linarith [ht.2]⟩
      refine observed.trans ?_
      apply congrArg g.curve
      apply Subtype.ext
      dsimp [u, HybridFlow.castCurve]
      linarith

/-- Optional-label component actions paste without dropping any original
guard/reset test. One-sided idle actions are included, both-idle is excluded. -/
theorem paste_discrete (s s' : H.State) (m m' : (A).State) (agree) (agree')
    (l : Option Label) (a : Option (EdgeLabel Clock)) (live : (l, a) ≠ (none, none))
    (systemEdge : H.IdleEdge s.val.1 l s'.val.1)
    (monitorEdge : (A).IdleEdge m.val.1 a m'.val.1)
    (systemJump : H.IdleJump l s.val s'.val) (monitorJump : (A).IdleJump a m.val m'.val) :
    (P).DiscreteStep (T.joinState H h τ s m agree) (T.joinState H h τ s' m' agree') := by
  apply (H.parallelOn_discrete_iff (A) T.systemVarName T.tableauVarName _ _).mpr
  rw [T.joinState_system, T.joinState_system, T.joinState_tableau, T.joinState_tableau]
  exact ⟨l, a, live, systemEdge, monitorEdge, systemJump, monitorJump⟩

theorem paste_simultaneous {s s' : H.State} {m m' : (A).State} (agree) (agree')
    (system : H.DiscreteStep s s') (monitor : (A).DiscreteStep m m') :
    (P).DiscreteStep (T.joinState H h τ s m agree) (T.joinState H h τ s' m' agree') := by
  obtain ⟨e, es, et, jump⟩ := system
  obtain ⟨f, fs, ft, move⟩ := monitor
  have he : e.val = (s.val.1, e.val.2.1, s'.val.1) :=
    Prod.ext es (Prod.ext rfl et)
  have hf : f.val = (m.val.1, f.val.2.1, m'.val.1) :=
    Prod.ext fs (Prod.ext rfl ft)
  exact T.paste_discrete H h τ s s' m m' agree agree' (some e.val.2.1) (some f.val.2.1)
    (by simp) (he ▸ e.property) (hf ▸ f.property) ⟨e, he, jump⟩ ⟨f, hf, move⟩

theorem paste_system_step {s s' : H.State} (m : (A).State) (agree) (agree')
    (system : H.DiscreteStep s s') :
    (P).DiscreteStep (T.joinState H h τ s m agree) (T.joinState H h τ s' m agree') := by
  obtain ⟨e, es, et, jump⟩ := system
  have he : e.val = (s.val.1, e.val.2.1, s'.val.1) :=
    Prod.ext es (Prod.ext rfl et)
  exact T.paste_discrete H h τ s s' m m agree agree' (some e.val.2.1) none
    (by simp) (he ▸ e.property) rfl ⟨e, he, jump⟩ rfl

theorem paste_monitor_step (s : H.State) {m m' : (A).State} (agree) (agree')
    (monitor : (A).DiscreteStep m m') :
    (P).DiscreteStep (T.joinState H h τ s m agree) (T.joinState H h τ s m' agree') := by
  obtain ⟨f, fs, ft, jump⟩ := monitor
  have hf : f.val = (m.val.1, f.val.2.1, m'.val.1) :=
    Prod.ext fs (Prod.ext rfl ft)
  exact T.paste_discrete H h τ s s m m' agree agree' none (some f.val.2.1)
    (by simp) rfl (hf ▸ f.property) rfl ⟨f, hf, jump⟩

run_elab do
  for name in #[``joinValuation_tableau, ``joinSignal_system, ``joinSignal_tableau,
      ``joinState_system, ``joinState_tableau, ``joinState_initial,
      ``ContinuousStep.castDuration, ``paste_continuous, ``flow_duration_eq,
      ``pasteObservedFlow, ``paste_discrete, ``paste_simultaneous,
      ``paste_system_step, ``paste_monitor_step] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name} uses unexpected axiom {ax}"

end STLTableau.Section4.Tableau
