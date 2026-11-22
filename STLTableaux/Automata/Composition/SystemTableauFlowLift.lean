import STLTableaux.Automata.Composition.SystemTableauPasting
import STLTableaux.Automata.Recognition.ForwardVisits
import STLTableaux.Automata.Recognition.ClosedFlowAtoms

/-! Construct a property flow over the actual closed system evolution.
Real coordinates are copied, including both endpoints; only the property's
clocks and type bit are added. This is a local step of the model-checking
construction, not an assumption that independent executions can be pasted. -/
namespace STLTableau.Section4.Tableau
open Section3 HybridAutomaton
variable {Clock Var State Mode Label : Type*} (T : Tableau Clock Var State)

/-- Add the rate-one clocks and fixed type bit without changing the real
coordinates at any point of the closed system curve. -/
def clockLiftCurve (v : T.TypedVar → ℝ) {r : NNReal}
    (γ : HybridFlow.Curve Var r) : HybridFlow.Curve T.TypedVar r :=
  fun u => T.forwardCurveValue v u.val (fun x => γ u x.val)

@[simp] theorem clockLiftCurve_real (v : T.TypedVar → ℝ) {r : NNReal}
    (γ : HybridFlow.Curve Var r) (u) (x : T.realVariables) :
    T.clockLiftCurve v γ u (.inl (.inl x)) = γ u x.val := rfl

@[simp] theorem clockLiftCurve_clock (v : T.TypedVar → ℝ) {r : NNReal}
    (γ : HybridFlow.Curve Var r) (u) (c : T.clocks) :
    T.clockLiftCurve v γ u (.inl (.inr (.inl c))) =
      v (.inl (.inr (.inl c))) + u.val := rfl

@[simp] theorem clockLiftCurve_global (v : T.TypedVar → ℝ) {r : NNReal}
    (γ : HybridFlow.Curve Var r) (u) :
    T.clockLiftCurve v γ u (.inl T.globalClock) = v (.inl T.globalClock) + u.val := rfl

@[simp] theorem clockLiftCurve_dwell (v : T.TypedVar → ℝ) {r : NNReal}
    (γ : HybridFlow.Curve Var r) (u) :
    T.clockLiftCurve v γ u T.dwell = v T.dwell + u.val := rfl

@[simp] theorem clockLiftCurve_bit (v : T.TypedVar → ℝ) {r : NNReal}
    (γ : HybridFlow.Curve Var r) (u) :
    T.clockLiftCurve v γ u T.bit = v T.bit := rfl

theorem monitor_flow_of_closed_system_curve (H : HybridAutomaton Mode Label Var)
    (h : T.TranslationReady) (τ : ℝ) {σ : FiniteSignal Var}
    (f : ObservedFlow H σ) (q : T.states) (α : ClockValuation Clock) (m : Marker)
    (atoms : ∀ u a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      a.Holds (f.curve u))
    (marks : ∀ b, Local.marker b ∈ T.label q.val → b = m)
    (bound : f.endTime ≤ τ) :
    let v := T.entryValue f.beginTime α (f.curve ⟨0, by simp⟩) m
    ∃ a b : (T.prelimAutomaton h τ).State,
      a.val = (q, v) ∧
      b.val = (q, T.clockLiftCurve v f.curve ⟨f.duration, by simp⟩) ∧
      (T.prelimAutomaton h τ).ContinuousStep a b f.duration
        (T.clockLiftCurve v f.curve) := by
  intro v
  have atZero : T.clockLiftCurve v f.curve ⟨0, by simp⟩ = v := by
    funext x
    cases x with
    | inl x =>
      cases x with
      | inl x => rfl
      | inr c => simp [clockLiftCurve, forwardCurveValue]
    | inr b => cases b <;> simp [clockLiftCurve, forwardCurveValue, dwell, bit]
  have inv (u : Set.Icc (0 : ℝ) f.duration) :
      (q, T.clockLiftCurve v f.curve u) ∈ (T.prelimAutomaton h τ).invariant := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · cases m
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro _
      change f.beginTime + u.val ≤ τ
      linarith [f.duration_eq, u.property.2]
    · intro a ha
      exact (T.atomHolds_iff a _ _ (h.atom_variables _ q.property a ha)
        (fun _ => rfl)).2 (atoms u a ha)
    · intro b hb
      rw [marks b hb]
      cases m
      · change Marker.open = Marker.closed ↔ (0 : ℝ) = 1
        simp
      · exact iff_of_true rfl rfl
  let a : (T.prelimAutomaton h τ).State :=
    ⟨(q, v), atZero ▸ inv ⟨0, by simp⟩⟩
  let b : (T.prelimAutomaton h τ).State :=
    ⟨(q, T.clockLiftCurve v f.curve ⟨f.duration, by simp⟩), inv _⟩
  refine ⟨a, b, rfl, rfl, rfl, atZero, rfl, ?_⟩
  intro u
  exact ⟨⟨fun _ => rfl, rfl, rfl, rfl⟩, inv u⟩

/-- Extend the recognized interval's atomic predicates to the actual
system curve's endpoints by continuity, not by selecting another sample.
Only interior observations are used; no value of the signal at its horizon
or equality across a system jump is required. -/
theorem closed_system_cell_atoms (H : HybridAutomaton Mode Label Var)
    {σ : FiniteSignal Var} (f : ObservedFlow H σ) (flows : H.ContinuousFlows)
    (P : IntervalPartition σ.domain) (i : Fin P.size)
    (left : f.beginTime = (P.interval i).left) (right : f.endTime = (P.interval i).right)
    (q : T.states) (β : ClockValuation Clock)
    (labels : ∀ l ∈ T.label q.val, l.holds σ P β ⟨i.val, by omega⟩)
    (nonStrict : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      a.relation = .ge)
    (functions : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      Continuous a.function) :
    ∀ u a, Local.predicate (.plain (.atom a)) ∈ T.label q.val → a.Holds (f.curve u) := by
  intro u a ha
  apply atom_on_closed_curve_of_interior f.curve f.positive (flows _ f.step.evolves)
    a (nonStrict a ha) (functions a ha) _ u
  intro v positive upper
  have lower : 0 ≤ f.beginTime := by
    rw [left]
    exact (pieceEntry σ P i).property.1
  let t : σ.Time := ⟨f.beginTime + v.val, by linarith, by
    have := P.right_le_domain_right i
    linarith [f.duration_eq]⟩
  have inside : t.val ∈ P.interval i := by
    refine ⟨Or.inl ?_, Or.inl ?_⟩
    · dsimp only [t]
      linarith
    · dsimp only [t]
      linarith [f.duration_eq]
  have body : ∀ t : σ.Time, t.val ∈ P.interval i → a.Holds (σ.value t) := by
    simpa only [Local.holds, Local.toJudgement, Section3.Judgement.holds,
      dif_pos i.isLt, Predicate.holds, predicateSatisfies, FiniteSignal.Satisfies]
      using labels _ ha
  have observed := f.observe t ⟨by dsimp [t]; linarith, by
    dsimp [t]; linarith [f.duration_eq]⟩
  have time : (⟨t.val - f.beginTime, by
      constructor <;> dsimp [t] <;> linarith⟩ : Set.Icc (0 : ℝ) f.duration) = v :=
    Subtype.ext (by dsimp [t]; ring)
  simpa only [observed, time] using body t inside

/-- Construct the continuous transition of the translated automaton on one
recognized interval from the system curve and the clock valuations of the
tableau run. -/
theorem monitor_flow_over_system_cell (H : HybridAutomaton Mode Label Var)
    (h : T.TranslationReady) {σ : FiniteSignal Var}
    (f : ObservedFlow H σ) (flows : H.ContinuousFlows)
    (P : IntervalPartition σ.domain) (i : Fin P.size)
    (left : f.beginTime = (P.interval i).left) (right : f.endTime = (P.interval i).right)
    (q : T.states) (β α : ClockValuation Clock)
    (labels : ∀ l ∈ T.label q.val, l.holds σ P β ⟨i.val, by omega⟩)
    (nonStrict : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      a.relation = .ge)
    (functions : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      Continuous a.function) :
    let v := T.entryValue f.beginTime α (f.curve ⟨0, by simp⟩) (P.interval i).leftBoundary
    ∃ a b : (T.prelimAutomaton h σ.horizon).State,
      a.val = (q, v) ∧
      b.val = (q, T.clockLiftCurve v f.curve ⟨f.duration, by simp⟩) ∧
      (T.prelimAutomaton h σ.horizon).ContinuousStep a b f.duration
        (T.clockLiftCurve v f.curve) :=
  T.monitor_flow_of_closed_system_curve H h σ.horizon f q α _
    (T.closed_system_cell_atoms H f flows P i left right q β labels nonStrict functions)
    (T.piece_entry_markers σ P i q β labels) (right ▸ P.right_le_domain_right i)

/-- An actual composed flow on the cell. Its system component is exactly
the supplied system flow, and its translated coordinates are given by the
clock lift. Closed-coordinate agreement is proved by the construction itself. -/
theorem systemTableau_flow_over_cell (H : HybridAutomaton Mode Label Var)
    (h : T.TranslationReady) {σ : FiniteSignal Var}
    (f : ObservedFlow H σ) (flows : H.ContinuousFlows)
    (P : IntervalPartition σ.domain) (i : Fin P.size)
    (left : f.beginTime = (P.interval i).left) (right : f.endTime = (P.interval i).right)
    (q : T.states) (β α : ClockValuation Clock)
    (labels : ∀ l ∈ T.label q.val, l.holds σ P β ⟨i.val, by omega⟩)
    (nonStrict : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      a.relation = .ge)
    (functions : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      Continuous a.function) :
    let A := T.prelimAutomaton h σ.horizon
    let B := T.systemTableauAutomaton H h σ.horizon
    let v := T.entryValue f.beginTime α (f.curve ⟨0, by simp⟩) (P.interval i).leftBoundary
    ∃ a b : B.State,
      H.leftStateOn A T.systemVarName T.tableauVarName a = f.start ∧
      H.leftStateOn A T.systemVarName T.tableauVarName b = f.finish ∧
      (H.rightStateOn A T.systemVarName T.tableauVarName a).val = (q, v) ∧
      (H.rightStateOn A T.systemVarName T.tableauVarName b).val =
        (q, T.clockLiftCurve v f.curve ⟨f.duration, by simp⟩) ∧
      B.ContinuousStep a b f.duration
        (fun u => T.joinValuation (f.curve u) (T.clockLiftCurve v f.curve u)) := by
  intro A B v
  obtain ⟨a, b, entry, finish, step⟩ :=
    T.monitor_flow_over_system_cell H h f flows P i left right q β α labels nonStrict functions
  have agree : ∀ u x, f.curve u x.val = T.clockLiftCurve v f.curve u (.inl (.inl x)) :=
    fun _ _ => rfl
  let ja := T.joinState H h σ.horizon f.start a
    (T.curve_initial_agreement H h σ.horizon f.step step agree)
  let jb := T.joinState H h σ.horizon f.finish b
    (T.curve_final_agreement H h σ.horizon f.step step agree)
  refine ⟨ja, jb, T.joinState_system H h σ.horizon _ _ _,
    T.joinState_system H h σ.horizon _ _ _, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val (T.joinState_tableau H h σ.horizon _ _ _)
      |>.trans entry
  · exact congrArg Subtype.val (T.joinState_tableau H h σ.horizon _ _ _)
      |>.trans finish
  · exact T.paste_continuous H h σ.horizon f.step step agree

/-- If the first partition interval has positive duration, the actual
composed residence starts in the original initial set. Initial guards and
resets come from the given tableau run; the first marker comes from the
partition. Initial-singleton execution assembly is a separate case. -/
theorem systemTableau_initial_flow_over_first_cell (H : HybridAutomaton Mode Label Var)
    (h : T.TranslationReady) {σ : FiniteSignal Var}
    (f : ObservedFlow H σ) (flows : H.ContinuousFlows)
    (P : IntervalPartition σ.domain) (size : 0 < P.size)
    (left : f.beginTime = (P.interval ⟨0, size⟩).left)
    (right : f.endTime = (P.interval ⟨0, size⟩).right)
    (systemInit : f.start.val ∈ H.initial)
    (q : T.states) (l : EdgeLabel Clock) (initial : (l, q.val) ∈ T.initial)
    (α : ClockValuation Clock) (guards : ∀ g ∈ l.guards, g.holds α)
    (labels : ∀ loc ∈ T.label q.val,
      loc.holds σ P (l.resets.apply α) ⟨0, by omega⟩)
    (nonStrict : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      a.relation = .ge)
    (functions : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      Continuous a.function) :
    let A := T.prelimAutomaton h σ.horizon
    let B := T.systemTableauAutomaton H h σ.horizon
    let v := T.entryValue f.beginTime (l.resets.apply α) (f.curve ⟨0, by simp⟩)
      (P.interval ⟨0, size⟩).leftBoundary
    ∃ a b : B.State,
      a.val ∈ B.initial ∧
      H.leftStateOn A T.systemVarName T.tableauVarName a = f.start ∧
      H.leftStateOn A T.systemVarName T.tableauVarName b = f.finish ∧
      B.ContinuousStep a b f.duration
        (fun u => T.joinValuation (f.curve u) (T.clockLiftCurve v f.curve u)) := by
  intro A B v
  let i : Fin P.size := ⟨0, size⟩
  have atZero : f.beginTime = 0 := left.trans (P.first_left_eq_domain_left size σ.horizon_pos)
  have closed : (P.interval i).leftBoundary = ● := P.first_leftBoundary_closed size σ.horizon_pos
  have atoms := T.closed_system_cell_atoms H f flows P i left right q _ labels nonStrict functions
  obtain ⟨m, init, entry⟩ := T.forward_initial_entry h σ.horizon σ.horizon_pos q l initial
    α (f.curve ⟨0, by simp⟩) guards (atoms ⟨0, by simp⟩)
    (fun n hn => (T.piece_entry_markers σ P i q _ labels n hn).trans closed)
  obtain ⟨a, b, systemA, systemB, monitorA, _, step⟩ :=
    T.systemTableau_flow_over_cell H h f flows P i left right q _ _ labels nonStrict functions
  have same : H.rightStateOn A T.systemVarName T.tableauVarName a = m := by
    apply Subtype.ext
    rw [monitorA, entry, atZero, closed]
  refine ⟨a, b, ?_, systemA, systemB, step⟩
  apply (H.parallelOn_initial_iff A T.systemVarName T.tableauVarName a).mpr
  exact ⟨systemA ▸ systemInit, same.symm ▸ init⟩

run_elab do
  for n in #[``clockLiftCurve_real, ``clockLiftCurve_clock, ``clockLiftCurve_global,
      ``clockLiftCurve_dwell, ``clockLiftCurve_bit, ``monitor_flow_of_closed_system_curve,
      ``closed_system_cell_atoms, ``monitor_flow_over_system_cell,
      ``systemTableau_flow_over_cell, ``systemTableau_initial_flow_over_first_cell] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{n} uses unexpected axiom {ax}"

end STLTableau.Section4.Tableau
