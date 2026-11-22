import STLTableaux.Automata.Recognition.ProjectedFlowAssembly
import STLTableaux.Automata.Composition.SharedParallelExecution
import STLTableaux.Automata.Recognition.ForwardGoalCut
import STLTableaux.Automata.Recognition.TypedOrdinaryTrace
import STLTableaux.Semantics.Partitions.BoundaryPartition

namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
variable (H : HybridAutomaton T.states (EdgeLabel Clock) T.TypedVar) (ρ : FiniteSignal Var)

/-- One actual positive flow over the original signal; no augmented signal
is presupposed or read at the right endpoint. -/
structure FlowPiece where
  left : ℝ
  duration : NNReal
  positive : 0 < duration
  start : H.State
  finish : H.State
  curve : Set.Icc (0 : ℝ) duration → T.TypedVar → ℝ
  flow : H.ContinuousStep start finish duration curve
  obs : ∀ (t : ρ.Time) (u : Set.Icc (0 : ℝ) duration),
    left + u.val = t.val → u.val < duration →
    ∀ x : T.realVariables, curve u (.inl (.inl x)) = ρ.value t x.val

/-- The nonempty flow word. Its inter-flow discrete chain retains every
actual discrete witness; a singleton between flows gives two jumps here. -/
inductive FlowWord : H.State → ℝ → H.State → ℝ → Prop where
  | last (p : FlowPiece T H ρ) : FlowWord p.start p.left p.finish (p.left + p.duration)
  | cons (p : FlowPiece T H ρ) {a b z}
      (jumps : Relation.TransGen H.DiscreteStep p.finish a)
      (tail : FlowWord a (p.left + p.duration) b z) :
      FlowWord p.start p.left b z

namespace FlowWord
variable {T H ρ}
private structure Packed (a : H.State) (l : ℝ) (b : H.State) (r : ℝ) where
  k : ℕ
  ps : Fin (k+1) → FlowPiece T H ρ
  firstS : (ps 0).start = a
  firstL : (ps 0).left = l
  lastS : (ps (Fin.last k)).finish = b
  lastR : (ps (Fin.last k)).left + (ps (Fin.last k)).duration = r
  time : ∀ i : Fin k, (ps i.castSucc).left + (ps i.castSucc).duration = (ps i.succ).left
  jumps : ∀ i : Fin k, Relation.TransGen H.DiscreteStep (ps i.castSucc).finish (ps i.succ).start

private theorem pack {a l b r} (word : FlowWord T H ρ a l b r) :
    Nonempty (Packed (T := T) (ρ := ρ) a l b r) := by
  induction word with
  | last p => exact ⟨⟨0,fun _ => p,rfl,rfl,rfl,rfl,Fin.elim0,Fin.elim0⟩⟩
  | cons p jump rest ih =>
    obtain ⟨s⟩ := ih
    refine ⟨⟨s.k + 1,Fin.cases p s.ps,rfl,rfl,?_,?_,?_,?_⟩⟩
    · exact s.lastS
    · exact s.lastR
    · intro i; refine Fin.cases ?_ (fun j => ?_) i
      · exact s.firstL.symm
      · exact s.time j
    · intro i; refine Fin.cases ?_ (fun j => ?_) i
      · exact s.firstS.symm ▸ jump
      · exact s.jumps j

namespace Packed
variable {a b : H.State} {l r : ℝ} (s : Packed (T := T) (H := H) (ρ := ρ) a l b r)
private def bounds (i : Fin (s.k + 2)) : ℝ :=
  Fin.lastCases r (fun i => (s.ps i).left) i

private theorem leftTime (i : Fin (s.k + 1)) : s.bounds i.castSucc = (s.ps i).left := by
  simp [bounds]
private theorem rightTime (i : Fin (s.k + 1)) :
    s.bounds i.succ = (s.ps i).left + (s.ps i).duration := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [bounds] using s.lastR.symm
  · change s.bounds j.succ.castSucc = _
    rw [s.leftTime]
    exact (s.time j).symm
private theorem boundsMono : StrictMono s.bounds := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  rw [s.leftTime,s.rightTime]
  exact lt_add_of_pos_right _ (s.ps i).positive
private theorem boundsFirst : s.bounds 0 = l := (s.leftTime 0).trans s.firstL
private theorem boundsLast : s.bounds (Fin.last (s.k + 1)) = r := by simp [bounds]

private theorem seg_unique {t : ℝ} {i j : Fin (s.k + 1)}
    (hi : t ∈ Set.Ico (s.bounds i.castSucc) (s.bounds i.succ))
    (hj : t ∈ Set.Ico (s.bounds j.castSucc) (s.bounds j.succ)) : i = j := by
  rcases lt_trichotomy i j with h|he|h
  · have h' : i.succ ≤ j.castSucc := h
    exact (not_lt_of_ge (s.boundsMono.monotone h') (hj.1.trans_lt hi.2)).elim
  · exact he
  · have h' : j.succ ≤ i.castSucc := h
    exact (not_lt_of_ge (s.boundsMono.monotone h') (hi.1.trans_lt hj.2)).elim

private theorem seg_exists (t : ρ.Time) (h0 : l = 0) (ht : t.val < r) :
    ∃ i : Fin (s.k + 1), t.val ∈ Set.Ico (s.bounds i.castSucc) (s.bounds i.succ) :=
  IntervalPartition.exists_boundary_piece s.bounds ⟨(s.boundsFirst.trans h0).le.trans t.property.1,
    ht.trans_eq s.boundsLast.symm⟩

private def localTime (t : ρ.Time) (i : Fin (s.k + 1))
    (ht : t.val ∈ Set.Ico (s.bounds i.castSucc) (s.bounds i.succ)) :
    Set.Icc (0 : ℝ) (s.ps i).duration :=
  ⟨t.val - s.bounds i.castSucc,sub_nonneg.mpr ht.1, by
    rw [s.leftTime]; have := ht.2; rw [s.rightTime] at this; linarith⟩

private noncomputable def aug (h0 : l = 0) (init : H.State) : FiniteSignal T.TypedVar :=
  ⟨ρ.horizon,ρ.horizon_pos,fun t => if t.val = 0 then init.val.2 else if ht : t.val < r then
    let i := (s.seg_exists t h0 ht).choose
    (s.ps i).curve (s.localTime t i (s.seg_exists t h0 ht).choose_spec)
    else fun x => match x with | .inl (.inl v) => ρ.value t v.val | _ => 0⟩

private theorem obs (h0 : l = 0) (init : H.State) (i : Fin (s.k + 1)) (t : (s.aug h0 init).Time)
    (ht : t.val ∈ Set.Ico (s.bounds i.castSucc) (s.bounds i.succ)) (positive : 0 < t.val) :
    (s.aug h0 init).value t = (s.ps i).curve (s.localTime t i ht) := by
  have he : t.val < r :=
    ht.2.trans_le ((s.boundsMono.monotone (Fin.le_last _)).trans_eq s.boundsLast)
  simp only [aug,if_neg positive.ne',dif_pos he]
  have eq := s.seg_unique (s.seg_exists t h0 he).choose_spec ht
  subst i
  rfl

private theorem projects (h0 : l = 0) (init : H.State)
    (initial : ∀ x : T.realVariables, init.val.2 (.inl (.inl x)) =
      ρ.value ⟨0, le_rfl, ρ.horizon_pos⟩ x.val) : T.TypedProjectsTo (s.aug h0 init) ρ := by
  refine ⟨rfl,?_⟩
  intro t u he x
  have eq : (t : ρ.Time) = u := Subtype.ext he
  subst u
  by_cases zero : t.val = 0
  · have time : t = ⟨0, le_rfl, ρ.horizon_pos⟩ := Subtype.ext zero
    simpa [aug, zero, time] using initial x
  have positive : 0 < t.val := lt_of_le_of_ne t.property.1 (Ne.symm zero)
  by_cases ht : t.val < r
  · obtain ⟨i,hi⟩ := s.seg_exists t h0 ht
    rw [s.obs h0 init i t hi positive]
    apply (s.ps i).obs
    · change (s.ps i).left + (t.val - s.bounds i.castSucc) = t.val
      rw [s.leftTime]; ring
    · change t.val - s.bounds i.castSucc < (s.ps i).duration
      have := hi.2; rw [s.rightTime] at this; rw [s.leftTime]; linarith
  · simp only [aug,if_neg zero,dif_neg ht]

private noncomputable def makePrefix (h0 : l = 0) (he : r ≤ ρ.horizon) (init : H.State)
    (hi : init.val ∈ H.initial) (hs : Relation.ReflTransGen H.DiscreteStep init a) :
    H.ForwardPrefix (s.aug h0 init) where
  n := s.k + 1
  hn := Nat.succ_pos _
  boundary := s.bounds
  zero := s.boundsFirst.trans h0
  mono := s.boundsMono
  horizon := s.boundsLast.le.trans he
  duration := fun i => (s.ps i).duration
  diff := by intro i; rw [s.rightTime,s.leftTime]; ring
  init := init
  init_mem := hi
  initial_obs := by simp [aug]
  start := fun i => (s.ps i).start
  finish := fun i => (s.ps i).finish
  curve := fun i => (s.ps i).curve
  flow := fun i => (s.ps i).flow
  firstSteps := s.firstS.symm ▸ hs
  between := by
    intro i hik
    let j : Fin s.k := ⟨i.val,by omega⟩
    exact s.jumps j
  obs := fun i t ht positive => s.obs h0 init i t ht positive

private noncomputable def horizonExecution (h0 : l = 0) (he : r = ρ.horizon) (init fin : H.State)
    (hi : init.val ∈ H.initial) (hs : Relation.ReflTransGen H.DiscreteStep init a)
    (hf : Relation.ReflTransGen H.DiscreteStep b fin) : H.Execution (s.aug h0 init) :=
  let p := s.makePrefix h0 he.le init hi hs
  { count := p.n, nonempty := p.hn, initialState := p.init, initial_mem := p.init_mem
    initial_signal_eq := p.initial_obs
    start := p.start, finish := p.finish, boundary := p.boundary
    first_zero := p.zero, increasing := p.mono, last_le_horizon := p.horizon
    duration := p.duration, duration_eq := p.diff, curve := p.curve
    continuousStep := p.flow, initialSteps := p.firstSteps, discreteSteps := p.between
    finalState := fin, finalSteps := by
      change Relation.ReflTransGen H.DiscreteStep (s.ps (Fin.last s.k)).finish fin
      rw [s.lastS]; exact hf
    signal_eq := p.obs
    final_signal_eq := by
      intro t ht
      change t.val = s.bounds (Fin.last _) at ht
      exact (t.property.2.ne (ht.trans (s.boundsLast.trans he))).elim }

end Packed

private def FlowPiece.project (p : FlowPiece T H ρ) :
    HybridAutomaton.ProjectedFlowPiece H (ρ.reindex Subtype.val)
      (fun x : T.realVariables => .inl (.inl x)) where
  left := p.left
  duration := p.duration
  positive := p.positive
  start := p.start
  finish := p.finish
  curve := p.curve
  step := p.flow
  observe := fun t u time before x => p.obs t u time before x

private theorem toProjected {a b : H.State} {l r : ℝ} (word : FlowWord T H ρ a l b r) :
    Nonempty (HybridAutomaton.ProjectedFlowWord H (ρ.reindex Subtype.val)
      (fun x : T.realVariables => .inl (.inl x)) a l b r) := by
  induction word with
  | last p => exact ⟨.last (FlowPiece.project p)⟩
  | cons p jump _ ih =>
    obtain ⟨tail⟩ := ih
    exact ⟨.cons (FlowPiece.project p) jump.to_reflTransGen tail⟩

/-- Realize the projected flows as an execution with the given initial state,
first flow start, final state, and cut. -/
theorem prelim_execution_with_entries {a b : H.State} {r : ℝ} (word : FlowWord T H ρ a 0 b r)
    (init : H.State) (hi : init.val ∈ H.initial)
    (hs : Relation.ReflTransGen H.DiscreteStep init a) (he : r ≤ ρ.horizon) :
    ∃ σ, T.TypedProjectsTo σ ρ ∧ ∃ e : H.PrelimExecution σ,
      e.initialState = init ∧ e.start ⟨0, e.nonempty⟩ = a ∧
      e.finalState = b ∧ e.boundary ⟨e.count, by omega⟩ = r := by
  obtain ⟨p⟩ := toProjected word
  let extend (v : T.realVariables → ℝ) : T.TypedVar → ℝ
    | .inl (.inl x) => v x
    | _ => 0
  obtain ⟨σ, e, horizon, projects, hinit, start, finish, stop, _, _⟩ :=
    p.toExecution extend (fun _ _ => rfl) init hi rfl hs he
  refine ⟨σ, ⟨horizon, ?_⟩, e, hinit, start, finish, stop⟩
  intro t u time x
  exact projects t u time x

/-- Realize the projected flows as an execution with final state `b` and cut `r`. -/
theorem prelim_execution {a b : H.State} {r : ℝ} (word : FlowWord T H ρ a 0 b r)
    (init : H.State) (hi : init.val ∈ H.initial)
    (hs : Relation.ReflTransGen H.DiscreteStep init a) (he : r ≤ ρ.horizon) :
    ∃ σ, T.TypedProjectsTo σ ρ ∧ ∃ e : H.PrelimExecution σ,
      e.finalState = b ∧ e.boundary ⟨e.count, by omega⟩ = r := by
  obtain ⟨σ, proj, e, _, _, final, stop⟩ :=
    word.prelim_execution_with_entries init hi hs he
  exact ⟨σ, proj, e, final, stop⟩

/-- If the last flow ends in a goal mode, the resulting execution reaches that goal. -/
theorem reaches_prelim {a b : H.State} {r : ℝ} (word : FlowWord T H ρ a 0 b r)
    (init : H.State) (hi : init.val ∈ H.initial)
    (hs : Relation.ReflTransGen H.DiscreteStep init a) (he : r ≤ ρ.horizon)
    (goal : Set T.states) (hg : b.val.1 ∈ goal) :
    ∃ σ, T.TypedProjectsTo σ ρ ∧ H.PrelimReaches σ goal := by
  obtain ⟨σ, proj, e, finish, _⟩ := word.prelim_execution init hi hs he
  exact ⟨σ, proj, e.reaches_of_final_mode (finish.symm ▸ hg)⟩

/-- Shorten the last positive flow in a goal mode to end at the given interior time. -/
theorem reaches_positive {a b : H.State} {r : ℝ} (word : FlowWord T H ρ a 0 b r)
    (init : H.State) (hi : init.val ∈ H.initial)
    (initial : ∀ x : T.realVariables, init.val.2 (.inl (.inl x)) =
      ρ.value ⟨0, le_rfl, ρ.horizon_pos⟩ x.val)
    (hs : Relation.ReflTransGen H.DiscreteStep init a) (he : r ≤ ρ.horizon)
    (goal : Set T.states) (hg : b.val.1 ∈ goal) :
    ∃ σ, T.TypedProjectsTo σ ρ ∧ H.Reaches σ goal := by
  obtain ⟨s⟩ := pack word
  let p := s.makePrefix rfl he init hi hs
  refine ⟨s.aug rfl init,s.projects rfl init initial,p.reaches_if_last_goal goal ?_⟩
  have hm := (s.ps (Fin.last s.k)).flow.1
  exact hm.symm ▸ (s.lastS.symm ▸ hg)

/-- Horizon tail: retain every prescribed final jump and observe no
endpoint outside the original signal's half-open domain. -/
theorem reaches_horizon_tail {a b : H.State} (word : FlowWord T H ρ a 0 b ρ.horizon)
    (init fin : H.State) (hi : init.val ∈ H.initial)
    (initial : ∀ x : T.realVariables, init.val.2 (.inl (.inl x)) =
      ρ.value ⟨0, le_rfl, ρ.horizon_pos⟩ x.val)
    (hs : Relation.ReflTransGen H.DiscreteStep init a)
    (hf : Relation.ReflTransGen H.DiscreteStep b fin)
    (goal : Set T.states) (hg : fin.val.1 ∈ goal) :
    ∃ σ, T.TypedProjectsTo σ ρ ∧ H.Reaches σ goal := by
  obtain ⟨s⟩ := pack word
  exact ⟨s.aug rfl init, s.projects rfl init initial,
    s.horizonExecution rfl rfl init fin hi hs hf, hg⟩

/-- The final bookkeeping jump is the single-jump instance. -/
theorem reaches_end {a b : H.State} (word : FlowWord T H ρ a 0 b ρ.horizon)
    (init fin : H.State) (hi : init.val ∈ H.initial)
    (initial : ∀ x : T.realVariables, init.val.2 (.inl (.inl x)) =
      ρ.value ⟨0, le_rfl, ρ.horizon_pos⟩ x.val)
    (hs : Relation.ReflTransGen H.DiscreteStep init a)
    (hf : H.DiscreteStep b fin) (goal : Set T.states) (hg : fin.val.1 ∈ goal) :
    ∃ σ, T.TypedProjectsTo σ ρ ∧ H.Reaches σ goal :=
  word.reaches_horizon_tail init fin hi initial hs (.single hf) goal hg

end FlowWord

run_elab do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for n in #[``FlowWord.prelim_execution_with_entries, ``FlowWord.prelim_execution,
      ``FlowWord.reaches_prelim,
      ``FlowWord.reaches_positive,
      ``FlowWord.reaches_end, ``FlowWord.reaches_horizon_tail] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do throwError "{n} uses unexpected axiom {ax}"

end STLTableau.Section4.Tableau
