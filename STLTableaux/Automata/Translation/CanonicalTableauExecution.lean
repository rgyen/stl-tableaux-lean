import STLTableaux.Automata.Recognition.IndexedPath
import STLTableaux.Automata.Recognition.TableauRealClockSchedule
import STLTableaux.Automata.Translation.EndPositionTranslation
import STLTableaux.Automata.Translation.FinalGoalStep
import STLTableaux.Automata.Recognition.VisitCutSuffix
import STLTableaux.Semantics.Partitions.PartitionFirstBoundary
import STLTableaux.Semantics.Partitions.SingletonMarkerAssignment
import STLTableaux.Automata.Recognition.NormalizedInputLabelSemantics

/-! The translated automaton has no auxiliary residence or marker coordinate.
Boundary compatibility is needed for reconstructing an induced partition,
not for following a given tableau run. -/

namespace STLTableau.Section4.Tableau
open Section3

variable {Clock Var State : Type*} (T : Tableau Clock Var State)
variable (h : T.TranslationReady) (τ : ℝ)

/-- The tableau graph, its original clocks, and the global clock. Only the
clock part of a jump is specified by the property automaton. -/
def canonicalAutomaton : HybridAutomaton T.states (EdgeLabel Clock) T.HAVar :=
  let A := T.baseAutomaton h
  { A with
    invariant := {s | s ∈ A.invariant ∧ (s.1 ∉ T.terminalModes → s.2 T.globalClock ≤ τ)}
    trajectory_closed := A.trajectory_closed.strengthen _
    jump := fun e s s' => s.1 = e.val.1 ∧ s'.1 = e.val.2.2 ∧
      T.guardsHold e.val.2.1 s.2 ∧
      (∀ c : T.clocks, s'.2 (.inr (.inl c)) = T.reset e.val.2.1.resets s.2 (.inr (.inl c))) ∧
      s'.2 T.globalClock = s.2 T.globalClock ∧
      (s'.1 ∈ T.terminalModes → τ ≤ s'.2 T.globalClock) ∧
      (¬ T.EndGoal s'.1 → s'.2 T.globalClock < τ) }

local notation "A" => T.canonicalAutomaton h τ

/-- Goal is exactly the set of final modes, lifted to valid states. -/
def canonicalGoal : Set (A).State :=
  {s | s.val.1 ∈ T.goalModes}

/-- Execute the existing final edge at the end of the last flow.
Its target has no atomic tests, so no value of the signal at τ is needed. -/
theorem horizon_entry (a : (A).State) (atHorizon : a.val.2 T.globalClock = τ)
    (l : EdgeLabel Clock) (q : T.states)
    (edge : (a.val.1.val,l,q.val) ∈ T.edges) (guards : T.guardsHold l a.val.2)
    (target : T.EndGoal q) :
    ∃ b : (A).State, (A).DiscreteStep a b ∧ b.val.1 = q ∧
      ∀ x : T.realVariables, b.val.2 (.inl x) = a.val.2 (.inl x) := by
  let w := T.reset l.resets a.val.2
  have inv : (q,w) ∈ (A).invariant := by
    refine ⟨?_,fun _ => atHorizon.le⟩
    intro p hp
    rcases target.2 _ hp with he | he <;> cases he
  let b : (A).State := ⟨(q,w),inv⟩
  refine ⟨b,?_,rfl,fun _ => rfl⟩
  exact ⟨⟨(a.val.1,l,q),edge⟩,rfl,rfl,rfl,rfl,guards,fun _ => rfl,rfl,
    fun _ => atHorizon.ge, fun no => (no target).elim⟩

/-- Conversely, an actual jump at τ gives the last tableau edge and its
terminal-position label test directly from the jump relation. -/
theorem horizon_step_data (a b : (A).State) (step : (A).DiscreteStep a b)
    (atHorizon : a.val.2 T.globalClock = τ) :
    T.EndGoal b.val.1 ∧
      ∃ l : EdgeLabel Clock, (a.val.1.val,l,b.val.1.val) ∈ T.edges ∧ T.guardsHold l a.val.2 := by
  classical
  obtain ⟨e,hs,ht,_,_,guard,_,clock,_,entry⟩ := step
  have target : T.EndGoal b.val.1 := by
    by_contra incompatible
    have late := entry incompatible
    rw [clock,atHorizon] at late
    exact (lt_irrefl τ) late
  have edge : (e.val.1.val,e.val.2.1,e.val.2.2.val) ∈ T.edges := e.property
  exact ⟨target,e.val.2.1,by simpa only [hs,ht] using edge,guard⟩

run_elab do
  for decl in #[``horizon_entry, ``horizon_step_data] do
    for ax in ← Lean.collectAxioms decl do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{decl} uses unexpected axiom {ax}"

/-- This is an execution prefix ending in a positive flow. The modes in
the list are the actual visits, including any intermediate singleton. -/
structure TableauExecution (σ : FiniteSignal Var) where
  n : ℕ
  nonempty : 0 < n
  time : Fin (n+1) → ℝ
  first_zero : time 0 = 0
  monotone : Monotone time
  isolated : IntervalPartition.IsolatedSingletons time
  last_positive : ∀ i : Fin n, i.val + 1 = n → time i.castSucc ≠ time i.succ
  stop_le : time (Fin.last n) ≤ τ
  horizon : σ.horizon = τ
  start : Fin n → (A).State
  finish : Fin n → (A).State
  initial : (start ⟨0,nonempty⟩).val ∈ (A).initial
  initialLabel : EdgeLabel Clock
  initialValue : T.HAVar → ℝ
  initial_edge : (initialLabel,(start ⟨0,nonempty⟩).val.1.val) ∈ T.initial
  initial_guard : T.guardsHold initialLabel initialValue
  initial_reset : (start ⟨0,nonempty⟩).val.2 = T.initialReset initialLabel.resets initialValue
  initial_observation : ∀ x : T.realVariables,
    σ.value ⟨0,le_rfl,σ.horizon_pos⟩ x.val = (start ⟨0,nonempty⟩).val.2 (.inl x)
  duration : Fin n → NNReal
  duration_eq : ∀ i, (duration i : ℝ) = time i.succ - time i.castSucc
  curve : ∀ i, Set.Icc (0 : ℝ) (duration i) → T.HAVar → ℝ
  flow : ∀ i, (A).ContinuousStep (start i) (finish i) (duration i) (curve i)
  jump : ∀ i : Fin (n-1), { l : EdgeLabel Clock //
    let s := finish ⟨i.val,by have := i.isLt; omega⟩
    let s' := start ⟨i.val+1,by have := i.isLt; omega⟩
    (s.val.1.val,l,s'.val.1.val) ∈ T.edges ∧ T.guardsHold l s.val.2 ∧
      (∀ c : T.clocks, s'.val.2 (.inr (.inl c)) = T.reset l.resets s.val.2 (.inr (.inl c))) ∧
      s'.val.2 T.globalClock = s.val.2 T.globalClock ∧
      (s'.val.1 ∈ T.terminalModes → τ ≤ s'.val.2 T.globalClock) }
  singleton_exit : ∀ (i : Fin (n-1)) (x : T.realVariables),
    duration ⟨i.val,by have := i.isLt; omega⟩ = 0 →
    (finish ⟨i.val,by have := i.isLt; omega⟩).val.2 (.inl x) =
      (start ⟨i.val+1,by have := i.isLt; omega⟩).val.2 (.inl x)
  observes : ∀ (i : Fin n) (t : σ.Time)
    (ht : time i.castSucc ≤ t.val ∧ t.val < time i.succ), 0 < t.val → ∀ x : T.realVariables,
    σ.value t x.val = curve i ⟨t.val - time i.castSucc, by
      constructor <;> linarith [ht.1, ht.2, duration_eq i]⟩ (.inl x)

/-- The marker condition needed to reconstruct the partition from durations. -/
def TableauExecution.BoundaryCompatible {σ : FiniteSignal Var} (e : T.TableauExecution h τ σ) : Prop :=
  ∀ (i : Fin e.n) m, Local.marker m ∈ T.label (e.start i).val.1.val →
    m = IntervalPartition.singletonMarkers e.time i.castSucc

/-- A tableau execution whose left-end requirements agree with the boundary
forms in Definition E.1. -/
structure CanonicalExecution (σ : FiniteSignal Var) extends T.TableauExecution h τ σ where
  compatible : toTableauExecution.BoundaryCompatible

variable {T h τ}

namespace TableauExecution

variable {σ : FiniteSignal Var} (e : T.TableauExecution h τ σ)

def last : Fin e.n := ⟨e.n - 1, by have := e.nonempty; omega⟩

def cut : ℝ := e.time (Fin.last e.n)

def goal : Prop := (A).GoalAtEnd (T.canonicalGoal h τ) (e.finish e.last) (e.cut = τ)

theorem last_succ : e.last.succ = Fin.last e.n := by
  apply Fin.ext
  change e.n - 1 + 1 = e.n
  have := e.nonempty
  omega

theorem starts_before_horizon (i : Fin e.n) : e.time i.castSucc < τ := by
  have hn : (e.last : ℕ) + 1 = e.n := congrArg Fin.val e.last_succ
  have hl := lt_of_le_of_ne (e.monotone (show e.last.castSucc ≤ e.last.succ from
    (Fin.castSucc_lt_succ (i := e.last)).le))
    (e.last_positive e.last hn)
  have hi : i.castSucc ≤ e.last.castSucc := by
    change i.val ≤ e.n - 1
    have := i.isLt
    omega
  exact (e.monotone hi).trans_lt (hl.trans_le (e.last_succ ▸ e.stop_le))

theorem duration_zero_iff (i : Fin e.n) :
    e.duration i = 0 ↔ e.time i.castSucc = e.time i.succ := by
  constructor
  · intro hz
    have hd := e.duration_eq i
    rw [hz, NNReal.coe_zero] at hd
    linarith
  · intro hz
    apply Subtype.ext
    simp [e.duration_eq i, hz]

theorem finish_clock (i : Fin e.n) (c : T.clocks) :
    (e.finish i).val.2 (.inr (.inl c)) =
      (e.start i).val.2 (.inr (.inl c)) + e.duration i := by
  have hf := ((e.flow i).2.2.2 ⟨e.duration i,by simp⟩).1.1 c
  rwa [(e.flow i).2.2.1] at hf

theorem finish_global (i : Fin e.n) :
    (e.finish i).val.2 T.globalClock = (e.start i).val.2 T.globalClock + e.duration i := by
  have hf := ((e.flow i).2.2.2 ⟨e.duration i,by simp⟩).1.2
  rwa [(e.flow i).2.2.1] at hf

theorem start_global (i : Fin e.n) : (e.start i).val.2 T.globalClock = e.time i.castSucc := by
  obtain ⟨k,hk⟩ := i
  induction k with
  | zero =>
    have he := congrFun e.initial_reset T.globalClock
    exact he.trans e.first_zero.symm
  | succ k ih =>
    let j : Fin e.n := ⟨k, by omega⟩
    have hcg := (e.jump ⟨k, by have := e.nonempty; omega⟩).property.2.2.2.1
    calc
      _ = (e.finish j).val.2 T.globalClock := hcg
      _ = e.time j.castSucc + (e.time j.succ - e.time j.castSucc) := by
        rw [e.finish_global j, ih j.isLt, e.duration_eq j]
      _ = e.time j.succ := by ring

theorem not_terminal
    (initial : ∀ l q, (l,q.val) ∈ T.initial → q ∉ T.terminalModes)
    (i : Fin e.n) : (e.start i).val.1 ∉ T.terminalModes := by
  obtain ⟨k,hk⟩ := i
  cases k with
  | zero =>
    exact initial e.initialLabel _ e.initial_edge
  | succ k =>
    have horizon := (e.jump ⟨k,by omega⟩).property.2.2.2.2
    intro ht
    have hb := horizon ht
    rw [e.start_global] at hb
    exact (e.starts_before_horizon ⟨k+1,hk⟩).not_ge hb

/-- Every labelled jump in the witness is a jump of Definition 5.3. -/
theorem discreteStep (i : Fin (e.n-1)) : (A).DiscreteStep
    (e.finish ⟨i.val,by have := i.isLt; omega⟩)
    (e.start ⟨i.val+1,by have := i.isLt; omega⟩) := by
  obtain ⟨l,edge,guard,reset,global,terminal⟩ := e.jump i
  let a := e.finish ⟨i.val,by have := i.isLt; omega⟩
  let j : Fin e.n := ⟨i.val+1,by have := i.isLt; omega⟩
  let b := e.start j
  have before : b.val.2 T.globalClock < τ := by
    change (e.start j).val.2 T.globalClock < τ
    rw [e.start_global]
    exact e.starts_before_horizon j
  exact ⟨⟨(a.val.1,l,b.val.1),edge⟩,rfl,rfl,rfl,rfl,guard,reset,global,terminal,fun _ => before⟩

theorem start_eq_finish_of_zero (i : Fin e.n) (zero : e.duration i = 0) :
    e.start i = e.finish i := by
  apply Subtype.ext
  refine Prod.ext (e.flow i).1 ?_
  have eq : (⟨(e.duration i : ℝ),by simp⟩ : Set.Icc (0 : ℝ) (e.duration i)) =
      ⟨0,by simp⟩ := Subtype.ext (by simp [zero])
  exact (e.flow i).2.1.symm.trans (eq ▸ (e.flow i).2.2.1)

end TableauExecution

namespace CanonicalExecution

variable {σ : FiniteSignal Var} (e : T.CanonicalExecution h τ σ)

abbrev last := e.toTableauExecution.last
abbrev cut := e.toTableauExecution.cut
def goal : Prop := (A).GoalAtEnd (T.canonicalGoal h τ) (e.finish e.last) (e.cut = τ)

def incoming (i : Fin e.n) : EdgeLabel Clock :=
  if hi : i.val = 0 then e.initialLabel else
    (e.jump ⟨i.val - 1,by have := i.isLt; omega⟩).val

def incomingValue (i : Fin e.n) : T.HAVar → ℝ :=
  if hi : i.val = 0 then e.initialValue else
    (e.finish ⟨i.val-1,by have := i.isLt; omega⟩).val.2

private theorem incoming_first : e.incoming ⟨0,e.nonempty⟩ = e.initialLabel := by
  simp [incoming]

private theorem incoming_jump (i : Fin (e.n-1)) :
    e.incoming ⟨i.val+1,by have := i.isLt; omega⟩ = (e.jump i).val := by
  simp [incoming]

private theorem incomingValue_jump (i : Fin (e.n-1)) :
    e.incomingValue ⟨i.val+1,by have := i.isLt; omega⟩ =
      (e.finish ⟨i.val,by have := i.isLt; omega⟩).val.2 := by
  simp [incomingValue]

theorem incoming_guards (i : Fin e.n) : T.guardsHold (e.incoming i) (e.incomingValue i) := by
  obtain ⟨k,hk⟩ := i
  cases k with
  | zero => simpa [incoming,incomingValue] using e.initial_guard
  | succ k =>
    let j : Fin (e.n-1) := ⟨k,by omega⟩
    rw [show e.incoming ⟨k+1,hk⟩ = (e.jump j).val from e.incoming_jump j,
      show e.incomingValue ⟨k+1,hk⟩ = _ from e.incomingValue_jump j]
    exact (e.jump j).property.2.1

theorem incoming_support (i : Fin e.n) : (e.incoming i).resets.clocks ⊆ T.clocks := by
  obtain ⟨k,hk⟩ := i
  cases k with
  | zero =>
    simpa [incoming] using h.initial_resets _ e.initial_edge
  | succ k =>
    let j : Fin (e.n-1) := ⟨k,by omega⟩
    rw [show e.incoming ⟨k+1,hk⟩ = (e.jump j).val from e.incoming_jump j]
    exact h.edge_resets _ (e.jump j).property.1

theorem incoming_reset (i : Fin e.n) (c : T.clocks) :
    (e.start i).val.2 (.inr (.inl c)) =
      T.reset (e.incoming i).resets (e.incomingValue i) (.inr (.inl c)) := by
  obtain ⟨k,hk⟩ := i
  cases k with
  | zero =>
    have he := congrFun e.initial_reset (Sum.inr (Sum.inl c))
    simpa [incoming,incomingValue,initialReset] using he
  | succ k =>
    let j : Fin (e.n-1) := ⟨k,by omega⟩
    rw [show e.incoming ⟨k+1,hk⟩ = (e.jump j).val from e.incoming_jump j,
      show e.incomingValue ⟨k+1,hk⟩ = _ from e.incomingValue_jump j]
    exact (e.jump j).property.2.2.1 c

theorem finish_time (i : Fin e.n) : (e.finish i).val.2 T.globalClock = e.time i.succ := by
  rw [e.finish_global,e.start_global,e.duration_eq]
  ring

/-- The induced partition is geometric. No trace satisfaction is a field. -/
structure Induces (P : IntervalPartition σ.domain) : Prop where
  count : e.n ≤ P.size
  pieces : ∀ i : Fin e.n, P.interval ⟨i.val,i.isLt.trans_le count⟩ =
    IntervalPartition.markedBoundaryPiece e.time (IntervalPartition.singletonMarkers e.time) i
  full : e.cut = σ.horizon → P.size = e.n
  suffix : e.cut < σ.horizon → ∃ hi : e.n < P.size,
    P.size = e.n+1 ∧ P.interval ⟨e.n,hi⟩ = ⟨e.cut,σ.horizon,●,○⟩

theorem exists_induces : ∃ P : IntervalPartition σ.domain, e.Induces P := by
  obtain ⟨P,hn,hp,hfull,hsuffix⟩ := IntervalPartition.completeVisitBounds
    e.time e.monotone (IntervalPartition.singletonMarkers e.time)
    (IntervalPartition.singletonMarkers_compatible _ e.isolated)
    (IntervalPartition.singletonMarkers_first _)
    (IntervalPartition.singletonMarkers_last _ e.last_positive) e.stop_le
  let Q : IntervalPartition σ.domain := { P with
    covers := by
      rw [P.covers, e.first_zero]
      change Set.Ico 0 τ = Set.Ico 0 σ.horizon
      rw [e.horizon] }
  refine ⟨Q,hn,hp,?_,?_⟩
  · change e.time (Fin.last e.n) = σ.horizon → P.size = e.n
    rw [e.horizon]
    exact hfull
  · change e.time (Fin.last e.n) < σ.horizon → ∃ hi : e.n < P.size,
      P.size = e.n+1 ∧ P.interval ⟨e.n,hi⟩ = ⟨e.time (Fin.last e.n),σ.horizon,●,○⟩
    rw [e.horizon]
    exact hsuffix

theorem Induces.duration {P : IntervalPartition σ.domain} (layout : e.Induces P) (i : Fin e.n) :
    STLTableau.Judgement.duration P ⟨i.val,i.isLt.trans_le layout.count⟩ = e.duration i := by
  apply Subtype.ext
  change (P.interval _).right - (P.interval _).left = (e.duration i : ℝ)
  rw [layout.pieces i, e.duration_eq i]
  rfl

private theorem flow_atom (i : Fin e.n) (a : AtomicProposition Var)
    (ha : Local.predicate (.plain (.atom a)) ∈ T.label (e.start i).val.1.val)
    (t : σ.Time) (ht : e.time i.castSucc ≤ t.val ∧ t.val < e.time i.succ) (positive : 0 < t.val) :
    a.Holds (σ.value t) := by
  let u : Set.Icc (0 : ℝ) (e.duration i) := ⟨t.val - e.time i.castSucc, by
    constructor <;> linarith [ht.1, ht.2, e.duration_eq i]⟩
  have inv := ((e.flow i).2.2.2 u).2
  apply (T.atomHolds_iff a (e.curve i u) (σ.value t)
    (h.atom_variables _ (e.start i).val.1.property a ha) (fun x => (e.observes i t ht positive x).symm)).1
  exact inv.1 a ha

private theorem singleton_atom (i : Fin e.n) (zero : e.time i.castSucc = e.time i.succ)
    (a : AtomicProposition Var)
    (ha : Local.predicate (.plain (.atom a)) ∈ T.label (e.start i).val.1.val)
    (t : σ.Time) (ht : t.val = e.time i.succ) (positive : 0 < t.val) : a.Holds (σ.value t) := by
  have hi : i.val + 1 < e.n := by
    have := i.isLt
    by_contra! hlast
    exact e.last_positive i (by omega) zero
  let j : Fin e.n := ⟨i.val+1,hi⟩
  have hnext : e.time j.castSucc ≠ e.time j.succ := e.isolated i hi zero
  have hj : e.time j.castSucc ≤ t.val ∧ t.val < e.time j.succ := by
    change e.time i.succ ≤ t.val ∧ t.val < e.time j.succ
    rw [ht]
    exact ⟨le_rfl,lt_of_le_of_ne (e.monotone (show j.castSucc ≤ j.succ from
      Fin.castSucc_lt_succ.le)) hnext⟩
  have hzero := (e.duration_zero_iff i).2 zero
  have equal : (e.finish i).val.2 = (e.start i).val.2 := by
    have ht0 : (⟨e.duration i,by simp⟩ : Set.Icc (0 : ℝ) (e.duration i)) =
        ⟨0,by simp⟩ := Subtype.ext (by simp [hzero])
    exact (e.flow i).2.2.1.symm.trans (ht0 ▸ (e.flow i).2.1)
  apply (T.atomHolds_iff a (e.start i).val.2 (σ.value t)
    (h.atom_variables _ (e.start i).val.1.property a ha) ?_).1 ((e.start i).property.1 a ha)
  intro x
  have hx := e.singleton_exit ⟨i.val,by omega⟩ x hzero
  change (e.finish i).val.2 (.inl x) = (e.start j).val.2 (.inl x) at hx
  rw [equal] at hx
  have obs := e.observes j t hj positive x
  have z : (⟨t.val-e.time j.castSucc,by
    constructor <;> linarith [hj.1,hj.2,e.duration_eq j]⟩ : Set.Icc (0 : ℝ) (e.duration j)) =
      ⟨0,by simp⟩ := Subtype.ext (by change t.val - e.time i.succ = 0; linarith)
  rw [obs,z,(e.flow j).2.1]
  exact hx

theorem Induces.atom {P : IntervalPartition σ.domain} (layout : e.Induces P) (i : Fin e.n)
    (a : AtomicProposition Var)
    (ha : Local.predicate (.plain (.atom a)) ∈ T.label (e.start i).val.1.val)
    (t : σ.Time) (ht : t.val ∈ P.interval ⟨i.val,i.isLt.trans_le layout.count⟩) :
    a.Holds (σ.value t) := by
  by_cases zero : t.val = 0
  · have hn : 0 < P.size := e.nonempty.trans_le layout.count
    let j : Fin P.size := ⟨0,hn⟩
    have hj : t.val ∈ P.interval j := by
      rw [zero, ← P.first_left_eq_domain_left hn σ.horizon_pos]
      exact (P.interval j).left_mem (P.nonempty j)
        (P.first_leftBoundary_closed hn σ.horizon_pos ▸ (show (● : Marker).Includes from trivial))
    have he : i = ⟨0,e.nonempty⟩ := Fin.ext
      (congrArg (fun k : Fin P.size => k.val) (P.eq_of_shared_point ht hj))
    subst i
    have tz : t = ⟨0,le_rfl,σ.horizon_pos⟩ := Subtype.ext zero
    exact (T.atomHolds_iff a _ _ (h.atom_variables _ (e.start _).val.1.property a ha)
      (fun x => (tz ▸ e.initial_observation x).symm)).1 ((e.start _).property.1 a ha)
  have positive := lt_of_le_of_ne t.property.1 (Ne.symm zero)
  rw [layout.pieces i] at ht
  have bounds := IntervalPartition.markedBoundaryPiece_subset_closed _ _ _ ht
  rcases lt_or_eq_of_le bounds.2 with lt | eq
  · exact e.flow_atom i a ha t ⟨bounds.1,lt⟩ positive
  · change t.val = e.time i.succ at eq
    have marker : IntervalPartition.singletonMarkers e.time i.succ = ○ := by
      have hr := ht.2
      change t.val < e.time i.succ ∨ (t.val = e.time i.succ ∧
        (Marker.complement (IntervalPartition.singletonMarkers e.time i.succ)).Includes) at hr
      cases m : IntervalPartition.singletonMarkers e.time i.succ with
      | «open» => rfl
      | closed => rw [m,eq] at hr; simp [Marker.complement,Marker.Includes] at hr
    change IntervalPartition.singletonMarkers e.time ⟨i.val+1,by omega⟩ = ○ at marker
    rw [IntervalPartition.singletonMarkers_succ e.time i] at marker
    split_ifs at marker with hz
    · exact e.singleton_atom i hz a ha t eq positive

theorem Induces.local_holds {P : IntervalPartition σ.domain} (layout : e.Induces P)
    (initial : ∀ l (q : T.states), (l,q.val) ∈ T.initial → q ∉ T.terminalModes)
    (ready : ∀ i : Fin e.n, ∀ l ∈ T.label (e.start i).val.1.val, l.NormalizedReady)
    (i : Fin e.n) (β : ClockValuation Clock) {l : Local Clock Var}
    (hl : l ∈ T.label (e.start i).val.1.val) :
    l.holds σ P β ⟨i.val,Nat.lt_succ_of_lt (i.isLt.trans_le layout.count)⟩ := by
  apply (Finiteness.normalizedReady_labels_hold_iff T _ (ready i) σ P β _
    (i.isLt.trans_le layout.count)).2 _ _ hl
  refine ⟨e.not_terminal initial i,fun m hm => ?_,fun a ha t ht => layout.atom e i a ha t ht⟩
  rw [layout.pieces i]
  exact (e.compatible i m hm).symm

private theorem indexed_trace (hf : ∀ s, (T.label s).Finite)
    (closed : ∀ p : Path Clock State, p.run T → (p.trace T.label hf).freeClocks = ∅)
    {P : IntervalPartition σ.domain} {n : ℕ}
    (incoming : Fin (n+1) → EdgeLabel Clock) (states : Fin (n+1) → T.states)
    (pre : Fin (n+1) → T.HAVar → ℝ)
    (initial : (incoming 0,(states 0).val) ∈ T.initial)
    (edge : ∀ i : Fin n, ((states i.castSucc).val,incoming i.succ,(states i.succ).val) ∈ T.edges)
    (final : (states (Fin.last n)).val ∈ T.final)
    (hlen : n+1 ≤ P.size+1)
    (guard : ∀ i, T.guardsHold (incoming i) (pre i))
    (next : ∀ (i : Fin n) (c : T.clocks), pre i.succ (.inr (.inl c)) =
      T.reset (incoming i.castSucc).resets (pre i.castSucc) (.inr (.inl c)) +
        STLTableau.Judgement.duration P ⟨i.val,by omega⟩)
    (locals : ∀ (i : Fin (n+1)) (β : ClockValuation Clock) l,
      l ∈ T.label (states i).val → l.holds σ P β ⟨i.val,by omega⟩) : T.recognizes hf σ P := by
  classical
  let p := Path.ofIndexed n incoming (fun i => (states i).val)
  have run : p.run T := Path.ofIndexed_run T n incoming _ (fun i => (states i).property) edge initial
  have acc : p.accepting T := Path.ofIndexed_accepting T n incoming _ (fun i => (states i).property) edge final
  let tr := p.trace T.label hf
  have htr : tr.length = n+1 := Path.ofIndexed_trace_length T.label hf n incoming _
  let ι (i : Fin tr.length) : Fin (n+1) := i.cast htr
  have frame (i : Fin tr.length) : tr.frameAt i =
      ⟨(incoming (ι i)).guards,(incoming (ι i)).guards_finite,(incoming (ι i)).resets,
        T.label (states (ι i)).val,hf _⟩ := by
    have hh := Path.ofIndexed_trace_frameAt T.label hf n incoming (fun i => (states i).val) (ι i)
    simpa [ι,p,tr] using hh
  let d (i : ℕ) : NNReal := if hi : i < P.size then STLTableau.Judgement.duration P ⟨i,hi⟩ else 0
  let idx (i : ℕ) : Fin (n+1) := ⟨min i n,by omega⟩
  let L (i : ℕ) := incoming (idx i)
  let v (i : ℕ) := pre (idx i)
  let ν := T.realClockSchedule L d (v 0)
  have idx_eq (i : ℕ) (hi : i ≤ n) : idx i = ⟨i,by omega⟩ :=
    Fin.ext (min_eq_left hi)
  have hstep : ∀ i < n, ∀ c : T.clocks, v (i+1) (.inr (.inl c)) =
      T.reset (L i).resets (v i) (.inr (.inl c)) + d i := by
    intro i hi c
    simp only [v,L,idx_eq i (by omega),idx_eq (i+1) (by omega),d,dif_pos (show i < P.size by omega)]
    exact next ⟨i,hi⟩ c
  have align (i : Fin tr.length) : idx i.val = ι i := Fin.ext (min_eq_left (by omega))
  have hguards : tr.realGuardsHold σ P (ν 0) ⟨0,by omega⟩ := by
    apply Trace.realGuardsHold_of_schedule σ P tr ν ⟨0,by omega⟩
      (by simp [htr,hlen])
    · intro i g hg
      rw [frame i] at hg
      exact T.realClockSchedule_guards n L d v hstep (fun j hj => guard (idx j)) i.val
        (by omega) g (by simpa only [L,align i] using hg)
    · intro i hi
      rw [frame i,show ν (i.val+1) = _ from T.realClockSchedule_succ L d (v 0) i.val]
      have duration : d i.val = STLTableau.Judgement.duration P ⟨i.val,by omega⟩ := dif_pos (by omega)
      have label : L i.val = incoming (ι i) := congrArg incoming (align i)
      change (fun c => Trace.realReset (L i.val).resets (ν i.val) c + (d i.val : ℝ)) = _
      simp only [label,duration,Nat.zero_add]
  refine ⟨p,run,acc,Trace.forall_holds_of_closed_realGuards σ P tr (ν 0) ⟨0,by omega⟩
    (by simp [htr,hlen]) (closed p run) hguards ?_⟩
  intro i β l hl
  rw [frame i] at hl
  simpa only [Fin.val_zero,Nat.zero_add,ι,Fin.val_cast] using locals (ι i) β l hl

/-- The ordinary accepting cut keeps all actual modes and their incoming labels. -/
theorem recognizes_at_ordinary_cut (hf : ∀ s, (T.label s).Finite)
    (closed : ∀ p : Path Clock State, p.run T → (p.trace T.label hf).freeClocks = ∅)
    (initial : ∀ l (q : T.states), (l,q.val) ∈ T.initial → q ∉ T.terminalModes)
    (ready : ∀ i : Fin e.n, ∀ l ∈ T.label (e.start i).val.1.val, l.NormalizedReady)
    {P : IntervalPartition σ.domain} (layout : e.Induces P)
    (final : (e.start e.last).val.1 ∈ T.goalModes) : T.recognizes hf σ P := by
  let k := e.n - 1
  have hk : k + 1 = e.n := by dsimp [k]; have := e.nonempty; omega
  let idx (i : Fin (k+1)) : Fin e.n := i.cast hk
  have st : ∀ i : Fin k, idx i.castSucc = ⟨i.val,by have := i.isLt; omega⟩ := fun _ => rfl
  have su : ∀ i : Fin k, idx i.succ = ⟨i.val+1,by have := i.isLt; omega⟩ := fun _ => rfl
  have hlen : k+1 ≤ P.size+1 := hk.trans_le (Nat.le_succ_of_le layout.count)
  refine indexed_trace hf closed (fun i => e.incoming (idx i))
    (fun i => (e.start (idx i)).val.1) (fun i => e.incomingValue (idx i))
    ?_ ?_ final hlen (fun i => e.incoming_guards (idx i)) ?_ ?_
  · simpa only [show idx 0 = ⟨0,e.nonempty⟩ from rfl,e.incoming_first] using e.initial_edge
  · intro i
    have hmode := (e.flow (idx i.castSucc)).1
    have hedge := (e.jump i).property.1
    change ((e.finish (idx i.castSucc)).val.1.val,(e.jump i).val,
      (e.start (idx i.succ)).val.1.val) ∈ T.edges at hedge
    rw [← hmode] at hedge
    simpa only [su,e.incoming_jump i] using hedge
  · intro i c
    have left := e.incoming_reset (idx i.castSucc) c
    have right := e.finish_clock (idx i.castSucc) c
    rw [st] at left right
    rw [su,e.incomingValue_jump i,layout.duration e ⟨i.val,by omega⟩,right,left]
    rfl
  · intro i β l hl
    exact layout.local_holds e initial ready (idx i) β hl

/-- The executed last jump adds one tableau frame at the terminal position,
without adding an interval to the induced partition. -/
theorem recognizes_at_horizon_cut (hf : ∀ s, (T.label s).Finite)
    (closed : ∀ p : Path Clock State, p.run T → (p.trace T.label hf).freeClocks = ∅)
    (initial : ∀ l (q : T.states), (l,q.val) ∈ T.initial → q ∉ T.terminalModes)
    (ready : ∀ i : Fin e.n, ∀ l ∈ T.label (e.start i).val.1.val, l.NormalizedReady)
    {P : IntervalPartition σ.domain} (layout : e.Induces P)
    (atEnd : e.cut = τ) (l : EdgeLabel Clock) (q : T.states)
    (edge : ((e.finish e.last).val.1.val,l,q.val) ∈ T.edges)
    (guard : T.guardsHold l (e.finish e.last).val.2) (final : T.EndGoal q) : T.recognizes hf σ P := by
  let incoming (i : Fin (e.n+1)) := if hi : i.val < e.n then e.incoming ⟨i.val,hi⟩ else l
  let states (i : Fin (e.n+1)) := if hi : i.val < e.n then (e.start ⟨i.val,hi⟩).val.1 else q
  let values (i : Fin (e.n+1)) := if hi : i.val < e.n then e.incomingValue ⟨i.val,hi⟩
    else (e.finish e.last).val.2
  have size := layout.full (atEnd.trans e.horizon.symm)
  have hlen : e.n+1 ≤ P.size+1 := Nat.succ_le_succ size.ge
  refine indexed_trace hf closed incoming states values ?_ ?_ ?_ hlen ?_ ?_ ?_
  · simpa only [incoming,states,Fin.val_zero,dif_pos e.nonempty,e.incoming_first] using e.initial_edge
  · intro i
    simp only [incoming,states,Fin.val_castSucc,Fin.val_succ,dif_pos i.isLt]
    by_cases hi : i.val + 1 < e.n
    · let j : Fin (e.n-1) := ⟨i.val,by omega⟩
      rw [dif_pos hi,dif_pos hi,e.incoming_jump j]
      exact ((e.flow i).1.symm ▸ (e.jump j).property.1)
    · rw [dif_neg hi,dif_neg hi]
      have he : i = e.last := Fin.ext (by change i.val = e.n - 1; omega)
      simpa only [he,(e.flow e.last).1] using edge
  · simpa [states,goalModes] using final.1
  · intro i
    by_cases hi : i.val < e.n
    · simpa only [incoming,values,dif_pos hi] using e.incoming_guards ⟨i.val,hi⟩
    · simpa only [incoming,values,dif_neg hi] using guard
  · intro i c
    rw [layout.duration e i]
    simp only [incoming,values,Fin.val_castSucc,Fin.val_succ,dif_pos i.isLt]
    rw [← e.incoming_reset i c, ← e.finish_clock i c]
    by_cases hi : i.val + 1 < e.n
    · let j : Fin (e.n-1) := ⟨i.val,by omega⟩
      rw [dif_pos hi,e.incomingValue_jump j]
    · rw [dif_neg hi]
      have he : i = e.last := Fin.ext (by change i.val = e.n - 1; omega)
      rw [he]
  · intro i β loc hl
    by_cases hi : i.val < e.n
    · simp only [states,dif_pos hi] at hl
      exact layout.local_holds e initial ready ⟨i.val,hi⟩ β hl
    · simp only [states,dif_neg hi] at hl
      have he : (⟨i.val,by omega⟩ : STLTableau.Judgement.Position P) = ⟨P.size,by omega⟩ :=
        Fin.ext (by have := i.isLt; simp; omega)
      rw [he]
      exact ((T.endGoal_iff q σ P β).1 final).2 loc hl

/-- Used in Lemma 5.5(2). Recognition holds on the partition induced
at the end of an admissible execution that reaches a goal. -/
theorem recognizes (hf : ∀ s, (T.label s).Finite)
    (closed : ∀ p : Path Clock State, p.run T → (p.trace T.label hf).freeClocks = ∅)
    (initial : ∀ l (q : T.states), (l,q.val) ∈ T.initial → q ∉ T.terminalModes)
    (ready : ∀ i : Fin e.n, ∀ l ∈ T.label (e.start i).val.1.val, l.NormalizedReady)
    {P : IntervalPartition σ.domain} (layout : e.Induces P) (goal : e.goal) :
    T.recognizes hf σ P := by
  rcases goal with goal | ⟨atEnd,b,_,step⟩
  · exact e.recognizes_at_ordinary_cut hf closed initial ready layout ((e.flow e.last).1.symm ▸ goal)
  · have time : (e.finish e.last).val.2 T.globalClock = τ :=
      (e.finish_time e.last).trans ((congrArg e.time e.last_succ).trans atEnd)
    obtain ⟨final,l,edge,guard⟩ := T.horizon_step_data h τ _ b step time
    exact e.recognizes_at_horizon_cut hf closed initial ready layout atEnd l b.val.1 edge guard final

end CanonicalExecution

end STLTableau.Section4.Tableau
