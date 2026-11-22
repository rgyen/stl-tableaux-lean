import STLTableaux.Automata.Execution.FlowConcatenation

/-! Proof-only finite lists of observed positive flows. The connector relation
is a parameter, so this is not a replacement trajectory semantics. Normalizing
RTG connectors to TG retains genuine cycles and contracts only boundaries
which admit no nonempty discrete path. -/
namespace STLTableau.HybridAutomaton
variable {Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
variable {σ : FiniteSignal Var}

structure ObservedFlow (H : HybridAutomaton Mode Label Var) (σ : FiniteSignal Var) where
  start : H.State
  finish : H.State
  beginTime : ℝ
  endTime : ℝ
  duration : NNReal
  positive : 0 < (duration : ℝ)
  duration_eq : (duration : ℝ) = endTime - beginTime
  curve : Set.Icc (0 : ℝ) duration → Var → ℝ
  step : H.ContinuousStep start finish duration curve
  observe : ∀ (t : σ.Time) (ht : beginTime ≤ t.val ∧ t.val < endTime),
    σ.value t = curve ⟨t.val - beginTime, by
      constructor
      · linarith [ht.1]
      · linarith [ht.2, duration_eq]⟩

namespace ObservedFlow

def VisitsState (f : ObservedFlow H σ) (s : H.State) : Prop :=
  ∃ t, s.val = (f.start.val.1, f.curve t)

theorem visits_start (f : ObservedFlow H σ) : f.VisitsState f.start :=
  ⟨⟨0, by simp⟩, Prod.ext rfl f.step.2.1.symm⟩

theorem visits_finish (f : ObservedFlow H σ) : f.VisitsState f.finish :=
  ⟨⟨f.duration, by simp⟩, Prod.ext f.step.1.symm f.step.2.2.1.symm⟩

noncomputable def concat (f g : ObservedFlow H σ)
    (time : f.endTime = g.beginTime) (state : f.finish = g.start) : ObservedFlow H σ where
  start := f.start
  finish := g.finish
  beginTime := f.beginTime
  endTime := g.endTime
  duration := f.duration + g.duration
  positive := by push_cast; linarith [f.positive, g.positive]
  duration_eq := by push_cast; linarith [f.duration_eq, g.duration_eq]
  curve := ContinuousStep.concatCurve f.duration g.duration f.curve g.curve
  step := ContinuousStep.concat f.step (by simpa only [state] using g.step)
  observe := by
    intro t ht
    have offset : (f.duration : ℝ) + f.beginTime = g.beginTime := by
      linarith [f.duration_eq]
    have join : f.curve ⟨f.duration, by simp⟩ = g.curve ⟨0, by simp⟩ :=
      f.step.2.2.1.trans (by rw [state]; exact g.step.2.1.symm)
    by_cases before : t.val < g.beginTime
    · let u : Set.Icc (0 : ℝ) f.duration := ⟨t.val - f.beginTime, by
        constructor <;> linarith [ht.1]⟩
      have observed := f.observe t ⟨ht.1, before.trans_eq time.symm⟩
      have curveEq := ContinuousStep.concatCurve_left f.duration g.duration f.curve g.curve u
      exact observed.trans curveEq.symm
    · let u : Set.Icc (0 : ℝ) g.duration := ⟨t.val - g.beginTime, by
        constructor <;> linarith [g.duration_eq, ht.2]⟩
      have observed := g.observe t ⟨le_of_not_gt before, ht.2⟩
      have curveEq := ContinuousStep.concatCurve_right f.duration g.duration f.curve g.curve join u
      refine observed.trans (curveEq.symm.trans ?_)
      apply congrArg (ContinuousStep.concatCurve f.duration g.duration f.curve g.curve)
      apply Subtype.ext
      dsimp [u]
      linarith

theorem concat_visits_left (f g : ObservedFlow H σ)
    (time : f.endTime = g.beginTime) (state : f.finish = g.start)
    {s : H.State} (visit : f.VisitsState s) : (f.concat g time state).VisitsState s := by
  obtain ⟨t, ht⟩ := visit
  obtain ⟨u, hu⟩ := ContinuousStep.concat_visits_left f.duration g.duration f.curve g.curve t
  exact ⟨u, ht.trans (Prod.ext rfl hu.symm)⟩

theorem concat_visits_right (f g : ObservedFlow H σ)
    (time : f.endTime = g.beginTime) (state : f.finish = g.start)
    {s : H.State} (visit : g.VisitsState s) : (f.concat g time state).VisitsState s := by
  obtain ⟨t, ht⟩ := visit
  have join : f.curve ⟨f.duration, by simp⟩ = g.curve ⟨0, by simp⟩ :=
    f.step.2.2.1.trans (by rw [state]; exact g.step.2.1.symm)
  obtain ⟨u, hu⟩ :=
    ContinuousStep.concat_visits_right f.duration g.duration f.curve g.curve join t
  refine ⟨u, ht.trans (Prod.ext ?_ hu.symm)⟩
  exact (congrArg (fun s : H.State => s.val.1) state).symm.trans f.step.1.symm

end ObservedFlow

inductive ObservedFlowChain (H : HybridAutomaton Mode Label Var) (σ : FiniteSignal Var)
    (J : H.State → H.State → Prop) : H.State → ℝ → H.State → ℝ → Type _
  | single (f : ObservedFlow H σ) :
      ObservedFlowChain H σ J f.start f.beginTime f.finish f.endTime
  | snoc {a b : H.State} {t u : ℝ}
      (p : ObservedFlowChain H σ J a t b u) (f : ObservedFlow H σ)
      (time : u = f.beginTime) (step : J b f.start) :
      ObservedFlowChain H σ J a t f.finish f.endTime

namespace ObservedFlowChain
variable {J : H.State → H.State → Prop} {a b : H.State} {t u : ℝ}

def finish (_ : ObservedFlowChain H σ J a t b u) : H.State := b

def VisitsState : {a b : H.State} → {t u : ℝ} →
    ObservedFlowChain H σ J a t b u → H.State → Prop
  | _, _, _, _, .single f, s => f.VisitsState s
  | _, _, _, _, .snoc p f _ _, s => p.VisitsState s ∨
      (Relation.ReflTransGen H.DiscreteStep p.finish s ∧
        Relation.ReflTransGen H.DiscreteStep s f.start) ∨ f.VisitsState s

theorem visits_finish (p : ObservedFlowChain H σ J a t b u) : p.VisitsState b := by
  cases p with
  | single f => exact f.visits_finish
  | snoc p f time step => exact Or.inr (Or.inr f.visits_finish)

noncomputable def extendLast (p : ObservedFlowChain H σ J a t b u) (g : ObservedFlow H σ)
    (time : u = g.beginTime) (state : b = g.start) :
    ObservedFlowChain H σ J a t g.finish g.endTime := by
  cases p with
  | single f => exact .single (f.concat g time state)
  | snoc p f ht hs => exact .snoc p (f.concat g time state) ht hs

theorem extendLast_visits_old (p : ObservedFlowChain H σ J a t b u) (g : ObservedFlow H σ)
    (time : u = g.beginTime) (state : b = g.start) {s : H.State}
    (visit : p.VisitsState s) : (p.extendLast g time state).VisitsState s := by
  cases p with
  | single f => exact f.concat_visits_left g time state visit
  | snoc p f ht hs =>
    rcases visit with old | jump | flow
    · exact Or.inl old
    · exact Or.inr (Or.inl jump)
    · exact Or.inr (Or.inr (f.concat_visits_left g time state flow))

theorem extendLast_visits_new (p : ObservedFlowChain H σ J a t b u) (g : ObservedFlow H σ)
    (time : u = g.beginTime) (state : b = g.start) {s : H.State}
    (visit : g.VisitsState s) : (p.extendLast g time state).VisitsState s := by
  cases p with
  | single f => exact f.concat_visits_right g time state visit
  | snoc p f ht hs => exact Or.inr (Or.inr (f.concat_visits_right g time state visit))

/-- Retain all boundaries admitting genuine jumps, even cycles with equal
endpoints. Only a connector with no nonempty path is contracted. -/
theorem normalize (p : ObservedFlowChain H σ (Relation.ReflTransGen H.DiscreteStep) a t b u) :
    ∃ q : ObservedFlowChain H σ (Relation.TransGen H.DiscreteStep) a t b u,
      ∀ s, p.VisitsState s → q.VisitsState s := by
  classical
  induction p with
  | single f => exact ⟨.single f, fun _ visit => visit⟩
  | @snoc a b t u p f time step ih =>
    obtain ⟨q, preserve⟩ := ih
    by_cases genuine : Relation.TransGen H.DiscreteStep b f.start
    · refine ⟨.snoc q f time genuine, ?_⟩
      intro s visit
      rcases visit with old | jump | flow
      · exact Or.inl (preserve s old)
      · exact Or.inr (Or.inl jump)
      · exact Or.inr (Or.inr flow)
    · have equal : b = f.start := by
        rcases Relation.reflTransGen_iff_eq_or_transGen.mp step with same | nonempty
        · exact same.symm
        · exact (genuine nonempty).elim
      refine ⟨q.extendLast f time equal, ?_⟩
      intro s visit
      rcases visit with old | ⟨before, after⟩ | flow
      · exact q.extendLast_visits_old f time equal (preserve s old)
      · have same : s = b := by
          rcases Relation.reflTransGen_iff_eq_or_transGen.mp before with same | nonempty
          · exact same
          · exact (genuine (nonempty.trans_left after)).elim
        subst s
        exact q.extendLast_visits_old f time equal q.visits_finish
      · exact q.extendLast_visits_new f time equal flow

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``ObservedFlow.concat, ``ObservedFlow.concat_visits_left,
      ``ObservedFlow.concat_visits_right, ``normalize, ``extendLast_visits_old,
      ``extendLast_visits_new] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do throwError "{name} uses unexpected axiom {ax}"

end ObservedFlowChain
end STLTableau.HybridAutomaton
