import STLTableaux.Automata.Translation.CanonicalTableauCut
import STLTableaux.Automata.Composition.SharedParallelConstruction
import STLTableaux.Automata.Composition.SharedParallelExecution
import STLTableaux.Automata.Recognition.PrelimPartitionConnection
import STLTableaux.Automata.Recognition.ProjectedFlowAssembly

/-! Shared-variable product for the translated automaton with only tableau
clocks and the global clock. A synchronized prefix explicitly gives the
system subflows and the actual labelled property jumps on the same visits.
At the horizon the property can take its final jump while the system idles. -/
namespace STLTableau.Section4.Tableau
open HybridAutomaton
variable {Clock Var State Mode Label : Type*} (T : Tableau Clock Var State)

abbrev CanonicalName := Var ⊕ (T.clocks ⊕ Unit)

def canonicalSystemName : Var ↪ T.CanonicalName := ⟨Sum.inl,Sum.inl_injective⟩

def canonicalMonitorName : T.HAVar ↪ T.CanonicalName where
  toFun := Sum.map Subtype.val id
  inj' := by
    rintro (a | a) (b | b) he
    · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj he))
    · cases he
    · cases he
    · exact congrArg Sum.inr (Sum.inr.inj he)

abbrev CanonicalCompositionVar := JoinedVar T.canonicalSystemName T.canonicalMonitorName

def canonicalSystemCoordinate := leftVar T.canonicalSystemName T.canonicalMonitorName

def canonicalMonitorCoordinate := rightVar T.canonicalSystemName T.canonicalMonitorName

theorem canonical_shared_coordinate (x : T.realVariables) :
    T.canonicalSystemCoordinate x.val = T.canonicalMonitorCoordinate (.inl x) := rfl

def canonicalProduct (H : HybridAutomaton Mode Label Var) (h : T.TranslationReady) (τ : ℝ) :=
  H.parallelOn (T.canonicalAutomaton h τ) T.canonicalSystemName T.canonicalMonitorName

local notation "A" => T.canonicalAutomaton
local notation "B" => T.canonicalProduct

def canonicalSystemState (H : HybridAutomaton Mode Label Var) (h : T.TranslationReady)
    (τ : ℝ) (s : (B H h τ).State) : H.State :=
  H.leftStateOn (A h τ) T.canonicalSystemName T.canonicalMonitorName s

def canonicalMonitorState (H : HybridAutomaton Mode Label Var) (h : T.TranslationReady)
    (τ : ℝ) (s : (B H h τ).State) : (A h τ).State :=
  H.rightStateOn (A h τ) T.canonicalSystemName T.canonicalMonitorName s

def canonicalProductGoal (H : HybridAutomaton Mode Label Var) (h : T.TranslationReady)
    (τ : ℝ) : Set (B H h τ).State :=
  {s | T.canonicalMonitorState H h τ s ∈ T.canonicalGoal h τ}

/-- A genuine product jump with the system label explicitly idle. -/
def canonicalProductPropertyStep (H : HybridAutomaton Mode Label Var) (h : T.TranslationReady)
    (τ : ℝ) (a b : (B H h τ).State) : Prop :=
  ∃ m : {m // m ∈ (B H h τ).edge},
    m.val.1 = a.val.1 ∧ m.val.2.2 = b.val.1 ∧ m.val.2.1.1 = none ∧
      (B H h τ).jump m a.val b.val

def canonicalJoinValue (v : Var → ℝ) (w : T.HAVar → ℝ) :
    T.CanonicalCompositionVar → ℝ :=
  fun x => match x.val with
    | .inl a => v a
    | .inr c => w (.inr c)

@[simp] theorem canonicalJoinValue_system (v : Var → ℝ) (w : T.HAVar → ℝ) (x : Var) :
    T.canonicalJoinValue v w (T.canonicalSystemCoordinate x) = v x := rfl

theorem canonicalJoinValue_monitor (v : Var → ℝ) (w : T.HAVar → ℝ)
    (agree : ∀ x : T.realVariables, v x.val = w (.inl x)) (x : T.HAVar) :
    T.canonicalJoinValue v w (T.canonicalMonitorCoordinate x) = w x := by
  rcases x with x | x
  · exact agree x
  · rfl

variable {T} (H : HybridAutomaton Mode Label Var) (h : T.TranslationReady) (τ : ℝ)

theorem canonicalProductPropertyStep.discreteStep
    {H : HybridAutomaton Mode Label Var} {h : T.TranslationReady} {τ : ℝ}
    {a b : (B H h τ).State} (step : T.canonicalProductPropertyStep H h τ a b) :
    (B H h τ).DiscreteStep a b := by
  obtain ⟨m,src,dst,_,jump⟩ := step
  exact ⟨m,src,dst,jump⟩

theorem canonicalProductPropertyStep.system_idle
    {H : HybridAutomaton Mode Label Var} {h : T.TranslationReady} {τ : ℝ}
    {a b : (B H h τ).State} (step : T.canonicalProductPropertyStep H h τ a b) :
    T.canonicalSystemState H h τ a = T.canonicalSystemState H h τ b := by
  obtain ⟨m,_,_,idle,jump⟩ := step
  have left : H.IdleJump m.val.2.1.1 (T.canonicalSystemState H h τ a).val
      (T.canonicalSystemState H h τ b).val := jump.1
  rw [idle] at left
  exact Subtype.ext left

theorem canonicalProductPropertyStep.monitorStep
    {H : HybridAutomaton Mode Label Var} {h : T.TranslationReady} {τ : ℝ}
    {a b : (B H h τ).State} (step : T.canonicalProductPropertyStep H h τ a b) :
    (A h τ).DiscreteStep (T.canonicalMonitorState H h τ a)
      (T.canonicalMonitorState H h τ b) := by
  obtain ⟨m,_,_,idle,jump⟩ := step
  have right : (A h τ).IdleJump m.val.2.1.2 (T.canonicalMonitorState H h τ a).val
      (T.canonicalMonitorState H h τ b).val := jump.2
  cases active : m.val.2.1.2 with
  | none => exact (m.property.1 (Prod.ext idle active)).elim
  | some l =>
    rw [active] at right
    obtain ⟨f,edge,jump⟩ := right
    exact ⟨f,congrArg Prod.fst edge,congrArg (fun p => p.2.2) edge,jump⟩

def canonicalJoinState (s : H.State) (a : (A h τ).State)
    (agree : ∀ x : T.realVariables, s.val.2 x.val = a.val.2 (.inl x)) : (B H h τ).State := by
  refine ⟨((s.val.1,a.val.1),T.canonicalJoinValue s.val.2 a.val.2), s.property,?_⟩
  change (a.val.1, T.canonicalJoinValue s.val.2 a.val.2 ∘ T.canonicalMonitorCoordinate)
    ∈ (A h τ).invariant
  have eq : T.canonicalJoinValue s.val.2 a.val.2 ∘ T.canonicalMonitorCoordinate = a.val.2 :=
    funext (T.canonicalJoinValue_monitor _ _ agree)
  rw [eq]
  exact a.property

@[simp] theorem canonicalJoinState_system (s : H.State) (a : (A h τ).State) (agree) :
    T.canonicalSystemState H h τ (canonicalJoinState H h τ s a agree) = s := rfl

@[simp] theorem canonicalJoinState_monitor (s : H.State) (a : (A h τ).State) (agree) :
    T.canonicalMonitorState H h τ (canonicalJoinState H h τ s a agree) = a := by
  exact Subtype.ext (Prod.ext rfl (funext (T.canonicalJoinValue_monitor _ _ agree)))

/-- Synchronize an admissible property execution with a prefix of one system
execution that realizes the whole signal. Each property visit is contained
in a system flow, and their curves agree on the shared coordinates. -/
structure CanonicalSynchronization {σ : FiniteSignal Var} (e : T.CanonicalExecution h τ σ) where
  system : H.PrelimExecution σ
  full : system.ReachesHorizon
  direct : system.initialState = system.start ⟨0,system.nonempty⟩
  /-- The system owner is the actual flow containing the left endpoint.
  In particular a singleton at a system jump uses the post-jump value. -/
  owner : Fin e.n → Fin system.count
  bounds : ∀ i : Fin e.n,
    system.boundary (owner i).castSucc ≤ e.time i.castSucc ∧
    e.time i.castSucc < system.boundary (owner i).succ ∧
    e.time i.succ ≤ system.boundary (owner i).succ
  singleJump : ∀ (k : Fin system.count) (live : k.val+1 < system.count),
    H.DiscreteStep (system.finish k) (system.start ⟨k.val+1,live⟩)
  shared : ∀ (i : Fin e.n) (u : Set.Icc (0 : ℝ) (e.duration i)) (x : T.realVariables),
    let k := owner i
    ∃ v : Set.Icc (0 : ℝ) (system.duration k),
      v.val = e.time i.castSucc - system.boundary k.castSucc + u.val ∧
      e.curve i u (.inl x) = system.curve k v x.val

namespace CanonicalSynchronization
variable {τ h H} {σ : FiniteSignal Var} {e : T.CanonicalExecution h τ σ}
variable (d : CanonicalSynchronization H h τ e)

private theorem owner_lower_end (i : Fin e.n) :
    d.system.boundary (d.owner i).castSucc ≤ e.time i.succ :=
  (d.bounds i).1.trans (e.monotone (Fin.castSucc_lt_succ.le))

noncomputable def sysStart (i : Fin e.n) : H.State :=
  d.system.stateAtTime (d.owner i) (e.time i.castSucc) ⟨(d.bounds i).1,(d.bounds i).2.1.le⟩

noncomputable def sysFinish (i : Fin e.n) : H.State :=
  d.system.stateAtTime (d.owner i) (e.time i.succ) ⟨d.owner_lower_end i,(d.bounds i).2.2⟩

theorem sysStart_shared (i : Fin e.n) (x : T.realVariables) :
    (d.sysStart i).val.2 x.val = (e.start i).val.2 (.inl x) := by
  obtain ⟨u,hu,hx⟩ := d.shared i ⟨0,by simp⟩ x
  rw [(e.flow i).2.1] at hx
  refine Eq.trans ?_ hx.symm
  change d.system.curve (d.owner i) _ x.val = d.system.curve (d.owner i) u x.val
  apply congrArg (fun u => d.system.curve (d.owner i) u x.val)
  apply Subtype.ext
  change e.time i.castSucc - d.system.boundary (d.owner i).castSucc = u.val
  change u.val = e.time i.castSucc - d.system.boundary (d.owner i).castSucc + (0 : ℝ) at hu
  rw [hu,add_zero]

theorem sysFinish_shared (i : Fin e.n) (x : T.realVariables) :
    (d.sysFinish i).val.2 x.val = (e.finish i).val.2 (.inl x) := by
  obtain ⟨u,hu,hx⟩ := d.shared i ⟨e.duration i,by simp⟩ x
  rw [(e.flow i).2.2.1] at hx
  refine Eq.trans ?_ hx.symm
  change d.system.curve (d.owner i) _ x.val = d.system.curve (d.owner i) u x.val
  apply congrArg (fun u => d.system.curve (d.owner i) u x.val)
  apply Subtype.ext
  change e.time i.succ - d.system.boundary (d.owner i).castSucc = u.val
  rw [hu]
  change _ = _ + (e.duration i : ℝ)
  rw [e.duration_eq]
  ring

noncomputable def jointStart (i : Fin e.n) : (B H h τ).State :=
  canonicalJoinState H h τ (d.sysStart i) (e.start i) (d.sysStart_shared i)

noncomputable def jointFinish (i : Fin e.n) : (B H h τ).State :=
  canonicalJoinState H h τ (d.sysFinish i) (e.finish i) (d.sysFinish_shared i)

theorem jointInitial : (d.jointStart ⟨0,e.nonempty⟩).val ∈ (B H h τ).initial := by
  apply (H.parallelOn_initial_iff (A h τ) T.canonicalSystemName T.canonicalMonitorName _).2
  change (T.canonicalSystemState H h τ _).val ∈ H.initial ∧
    (T.canonicalMonitorState H h τ _).val ∈ (A h τ).initial
  simp only [jointStart, canonicalJoinState_system,canonicalJoinState_monitor]
  refine ⟨?_,e.initial⟩
  let i : Fin e.n := ⟨0,e.nonempty⟩
  have zero : d.system.boundary (d.owner i).castSucc = 0 := by
    have low := (d.bounds i).1
    have first : e.time i.castSucc = 0 := e.first_zero
    have h := d.system.increasing.monotone (Fin.zero_le (d.owner i).castSucc)
    have atZero : d.system.boundary 0 = 0 := d.system.first_zero
    rw [atZero] at h
    exact le_antisymm (first ▸ low) h
  have owner : d.owner i = ⟨0,d.system.nonempty⟩ := by
    have eq := d.system.increasing.injective (zero.trans d.system.first_zero.symm)
    exact Fin.ext (congrArg (fun j : Fin (d.system.count+1) => j.val) eq)
  have begin : d.sysStart i = d.system.start ⟨0,d.system.nonempty⟩ := by
    have first : e.time i.castSucc = 0 := e.first_zero
    unfold sysStart
    rw [d.system.stateAtTime_start _ _ _ (first.trans zero.symm),owner]
  rw [show d.sysStart ⟨0,e.nonempty⟩ = _ from begin, ← d.direct]
  exact d.system.initial_mem

private theorem sysLink (i : Fin (e.n-1)) :
    let j : Fin e.n := ⟨i.val,by have := i.isLt; omega⟩
    let k : Fin e.n := ⟨i.val+1,by have := i.isLt; omega⟩
    d.sysFinish j = d.sysStart k ∨ H.DiscreteStep (d.sysFinish j) (d.sysStart k) := by
  intro j k
  let a := d.owner j
  let b := d.owner k
  have join : e.time j.succ = e.time k.castSucc := rfl
  have before : d.system.boundary a.castSucc ≤ e.time k.castSucc :=
    join ▸ d.owner_lower_end j
  have after : e.time k.castSucc ≤ d.system.boundary a.succ := join ▸ (d.bounds j).2.2
  have le : a ≤ b := by
    by_contra! he
    have hba : b.succ ≤ a.castSucc := by
      change b.val+1 ≤ a.val
      exact he
    exact ((d.bounds k).2.1.trans_le ((d.system.increasing.monotone hba).trans before)).false
  rcases le_iff_eq_or_lt.mp le with eq | lt
  · left
    exact d.system.stateAtTime_congr _ _ eq join
  · right
    have h : a.succ ≤ b.castSucc := by change a.val+1 ≤ b.val; exact lt
    have time : d.system.boundary a.succ = d.system.boundary b.castSucc :=
      le_antisymm (d.system.increasing.monotone h) ((d.bounds k).1.trans after)
    have eq : a.succ = b.castSucc := d.system.increasing.injective time
    have bi : b.val = a.val+1 := (congrArg Fin.val eq).symm
    have live : a.val+1 < d.system.count := bi ▸ b.isLt
    have endTime : e.time j.succ = d.system.boundary a.succ :=
      join.trans (le_antisymm after (time.symm ▸ (d.bounds k).1))
    have startTime : e.time k.castSucc = d.system.boundary b.castSucc :=
      join.symm.trans (endTime.trans time)
    unfold sysFinish sysStart
    rw [d.system.stateAtTime_finish _ _ _ endTime, d.system.stateAtTime_start _ _ _ startTime]
    exact (Fin.ext bi : b = ⟨a.val+1,live⟩) ▸ d.singleJump a live

/-- A system boundary at a singleton is consumed on entry, never on exit.
Both endpoints of the exit lie in the same right-owned system flow. -/
theorem singletonExit_system_idle (i : Fin (e.n-1))
    (zero : e.duration ⟨i.val,by have := i.isLt; omega⟩ = 0) :
    d.sysFinish ⟨i.val,by have := i.isLt; omega⟩ =
      d.sysStart ⟨i.val+1,by have := i.isLt; omega⟩ := by
  let j : Fin e.n := ⟨i.val,by have := i.isLt; omega⟩
  let k : Fin e.n := ⟨i.val+1,by have := i.isLt; omega⟩
  have join : e.time j.succ = e.time k.castSucc := rfl
  have same := ((e.duration_zero_iff j).1 zero).trans join
  have he : d.owner j = d.owner k := by
    apply le_antisymm
    · by_contra! h
      have h' : (d.owner k).succ ≤ (d.owner j).castSucc := by
        change (d.owner k).val + 1 ≤ (d.owner j).val
        exact h
      exact ((d.bounds k).2.1.trans_le
        ((d.system.increasing.monotone h').trans ((same ▸ (d.bounds j).1)))).false
    · by_contra! h
      have h' : (d.owner j).succ ≤ (d.owner k).castSucc := by
        change (d.owner j).val + 1 ≤ (d.owner k).val
        exact h
      exact ((d.bounds j).2.1.trans_le
        ((d.system.increasing.monotone h').trans ((same.symm ▸ (d.bounds k).1)))).false
  exact d.system.stateAtTime_congr _ _ he join

theorem jointJump (i : Fin (e.n-1)) :
    (B H h τ).DiscreteStep (d.jointFinish ⟨i.val,by have := i.isLt; omega⟩)
      (d.jointStart ⟨i.val+1,by have := i.isLt; omega⟩) := by
  apply (H.parallelOn_discrete_iff (A h τ) T.canonicalSystemName T.canonicalMonitorName _ _).2
  let j : Fin e.n := ⟨i.val,by have := i.isLt; omega⟩
  let k : Fin e.n := ⟨i.val+1,by have := i.isLt; omega⟩
  obtain ⟨m,src,dst,step⟩ := e.discreteStep i
  have edge : m.val = ((e.finish j).val.1,m.val.2.1,(e.start k).val.1) :=
    Prod.ext src (Prod.ext rfl dst)
  change ∃ l₁ l₂, (l₁,l₂) ≠ (none,none) ∧
    H.IdleEdge (T.canonicalSystemState H h τ (d.jointFinish j)).val.1 l₁
      (T.canonicalSystemState H h τ (d.jointStart k)).val.1 ∧
    (A h τ).IdleEdge (T.canonicalMonitorState H h τ (d.jointFinish j)).val.1 l₂
      (T.canonicalMonitorState H h τ (d.jointStart k)).val.1 ∧
    H.IdleJump l₁ (T.canonicalSystemState H h τ (d.jointFinish j)).val
      (T.canonicalSystemState H h τ (d.jointStart k)).val ∧
    (A h τ).IdleJump l₂ (T.canonicalMonitorState H h τ (d.jointFinish j)).val
      (T.canonicalMonitorState H h τ (d.jointStart k)).val
  simp only [jointFinish,jointStart,canonicalJoinState_system,canonicalJoinState_monitor]
  have link : d.sysFinish j = d.sysStart k ∨ H.DiscreteStep (d.sysFinish j) (d.sysStart k) := d.sysLink i
  rcases link with idle | ⟨s,hs,ht,sjump⟩
  · refine ⟨none,some m.val.2.1,by simp,congrArg (fun s : H.State => s.val.1) idle,
      edge ▸ m.property,congrArg Subtype.val idle,⟨m,edge,step⟩⟩
  · have se : s.val = ((d.sysFinish j).val.1,s.val.2.1,(d.sysStart k).val.1) :=
      Prod.ext hs (Prod.ext rfl ht)
    exact ⟨some s.val.2.1,some m.val.2.1,by simp,se ▸ s.property,edge ▸ m.property,
      ⟨s,se,sjump⟩,⟨m,edge,step⟩⟩

theorem jointFlow (i : Fin e.n) (pos : 0 < (e.duration i : ℝ)) :
    ∃ (γ : HybridFlow.Curve T.CanonicalCompositionVar (e.duration i)),
      (B H h τ).ContinuousStep (d.jointStart i) (d.jointFinish i) (e.duration i) γ ∧
      (∀ u x, γ u (T.canonicalMonitorCoordinate x) = e.curve i u x) ∧
      ∀ (t : σ.Time) (u : Set.Icc (0 : ℝ) (e.duration i)),
        e.time i.castSucc + u.val = t.val → u.val < e.duration i →
        ∀ x, γ u (T.canonicalSystemCoordinate x) = σ.value t x := by
  let g := d.system.observedFlow (d.owner i)
  have gt : e.time i.castSucc < e.time i.succ := by
    rw [e.duration_eq] at pos
    exact sub_pos.mp pos
  let bounds : g.beginTime ≤ e.time i.castSucc ∧ e.time i.castSucc < e.time i.succ ∧
      e.time i.succ ≤ g.endTime := ⟨(d.bounds i).1,gt,(d.bounds i).2.2⟩
  let f := g.sliceAt _ _ bounds
  have fs : f.start = d.sysStart i := rfl
  have fe : f.finish = d.sysFinish i := rfl
  have begin : f.beginTime = e.time i.castSucc := g.sliceAt_begin _ _ _
  have endTime : f.endTime = e.time i.succ := g.sliceAt_end _ _ _
  have dur : f.duration = e.duration i := by
    apply Subtype.ext
    have dd := f.duration_eq
    rw [begin,endTime] at dd
    exact dd.trans (e.duration_eq i).symm
  let cast (u : Set.Icc (0 : ℝ) (e.duration i)) : Set.Icc (0 : ℝ) f.duration :=
    ⟨u.val, u.property.1, by rw [dur]; exact u.property.2⟩
  let γ (u : Set.Icc (0 : ℝ) (e.duration i)) :=
    T.canonicalJoinValue (f.curve (cast u)) (e.curve i u)
  have agree (u : Set.Icc (0 : ℝ) (e.duration i)) (x : T.realVariables) :
      f.curve (cast u) x.val = e.curve i u (.inl x) := by
    obtain ⟨v,hv,hx⟩ := d.shared i u x
    refine Eq.trans ?_ hx.symm
    change d.system.curve (d.owner i) _ x.val = _
    apply congrArg (fun w => d.system.curve _ w x.val)
    apply Subtype.ext
    change e.time i.castSucc - d.system.boundary (d.owner i).castSucc + u.val = v.val
    exact hv.symm
  have right (u : Set.Icc (0 : ℝ) (e.duration i)) (x : T.HAVar) :
      γ u (T.canonicalMonitorCoordinate x) = e.curve i u x :=
    T.canonicalJoinValue_monitor _ _ (agree u) x
  refine ⟨γ,?_,right,?_⟩
  swap
  · intro t u time prior x
    have low := (d.bounds i).1
    have high := (d.bounds i).2.2
    have dd := e.duration_eq i
    have range : d.system.boundary (d.owner i).castSucc ≤ t.val ∧
        t.val < d.system.boundary (d.owner i).succ := by
      constructor <;> linarith [u.property.1]
    have hobs := d.system.signal_eq (d.owner i) t range
    change f.curve (cast u) x = σ.value t x
    refine Eq.trans ?_ (congrFun hobs x).symm
    change d.system.curve (d.owner i) _ x = d.system.curve (d.owner i) _ x
    apply congrArg (fun v => d.system.curve (d.owner i) v x)
    apply Subtype.ext
    change e.time i.castSucc - d.system.boundary (d.owner i).castSucc + u.val =
      t.val - d.system.boundary (d.owner i).castSucc
    linarith
  apply (H.parallelOn_continuous_iff (A h τ) T.canonicalSystemName T.canonicalMonitorName).2
  change H.ContinuousStep (T.canonicalSystemState H h τ (d.jointStart i))
      (T.canonicalSystemState H h τ (d.jointFinish i)) _ _ ∧
    (A h τ).ContinuousStep (T.canonicalMonitorState H h τ (d.jointStart i))
      (T.canonicalMonitorState H h τ (d.jointFinish i)) _ _
  simp only [jointStart,jointFinish,canonicalJoinState_system,canonicalJoinState_monitor]
  constructor
  · have step : H.ContinuousStep (d.sysStart i) (d.sysFinish i) (e.duration i)
        (fun u => f.curve (cast u)) := by
      rw [← fs,← fe]
      have generic (r : NNReal) (hr : f.duration = r) :
          H.ContinuousStep f.start f.finish r
            (fun (u : Set.Icc (0 : ℝ) r) => f.curve ⟨u.val,u.property.1,hr.symm ▸ u.property.2⟩) := by
        cases hr
        exact f.step
      exact generic _ dur
    exact step
  · have eq : (fun t x => γ t (rightVar T.canonicalSystemName T.canonicalMonitorName x)) =
        e.curve i := funext (fun t => funext (right t))
    rw [eq]
    exact e.flow i

/-- A final product mode is either the last flow's mode or is entered by
one actual property-only product jump at the horizon. -/
def goalAtEnd : Prop :=
  d.jointFinish e.last ∈ T.canonicalProductGoal H h τ ∨ e.cut = τ ∧
    ∃ b ∈ T.canonicalProductGoal H h τ,
      T.canonicalProductPropertyStep H h τ (d.jointFinish e.last) b

private theorem step_of_monitor_step {a b : (B H h τ).State}
    (idle : T.canonicalSystemState H h τ a = T.canonicalSystemState H h τ b)
    (step : (A h τ).DiscreteStep (T.canonicalMonitorState H h τ a)
      (T.canonicalMonitorState H h τ b)) :
    T.canonicalProductPropertyStep H h τ a b := by
  obtain ⟨m,src,dst,jump⟩ := step
  have edge : m.val = ((T.canonicalMonitorState H h τ a).val.1,
      m.val.2.1,(T.canonicalMonitorState H h τ b).val.1) := Prod.ext src (Prod.ext rfl dst)
  let joint : {m // m ∈ (B H h τ).edge} :=
    ⟨(a.val.1,(none,some m.val.2.1),b.val.1),
      by exact ⟨by simp,congrArg (fun s : H.State => s.val.1) idle,edge ▸ m.property⟩⟩
  exact ⟨joint,rfl,rfl,rfl,congrArg Subtype.val idle,⟨m,edge,jump⟩⟩

/-- The terminal jump is a property-only product edge, with every system
coordinate fixed at the last flow's endpoint. There is no new flow piece. -/
theorem joint_horizon_jump (horizon : e.cut = τ) {b : (A h τ).State}
    (step : (A h τ).DiscreteStep (e.finish e.last) b) :
    ∃ c ∈ T.canonicalProductGoal H h τ,
      T.canonicalProductPropertyStep H h τ (d.jointFinish e.last) c := by
  have time : (e.finish e.last).val.2 T.globalClock = τ :=
    (e.finish_time e.last).trans ((congrArg e.time e.last_succ).trans horizon)
  obtain ⟨target,l,edge,guard⟩ := T.horizon_step_data h τ _ _ step time
  obtain ⟨b',jump,mode,values⟩ := T.horizon_entry h τ _ time l _ edge guard target
  let c := canonicalJoinState H h τ (d.sysFinish e.last) b'
    (fun x => (d.sysFinish_shared e.last x).trans (values x).symm)
  have fixed : T.canonicalSystemState H h τ c = d.sysFinish e.last := rfl
  have monitor : T.canonicalMonitorState H h τ c = b' := by
    simp only [c,canonicalJoinState_monitor]
  refine ⟨c,?_,?_⟩
  · change (T.canonicalMonitorState H h τ c).val.1 ∈ T.goalModes
    rw [monitor,mode]
    exact target.1
  · apply step_of_monitor_step
    · simpa only [jointFinish,canonicalJoinState_system] using fixed.symm
    · simpa only [jointFinish,canonicalJoinState_monitor,monitor] using jump

theorem jointGoal (goal : e.goal) : d.goalAtEnd := by
  rcases goal with ordinary | ⟨horizon,b,_,step⟩
  · left
    change T.canonicalMonitorState H h τ (d.jointFinish e.last) ∈ T.canonicalGoal h τ
    simpa only [jointFinish,canonicalJoinState_monitor] using ordinary
  · obtain ⟨c,final,jump⟩ := d.joint_horizon_jump horizon step
    exact Or.inr ⟨horizon,c,final,jump⟩

theorem monitor_goal_of_jointGoal (goal : d.goalAtEnd) : e.goal := by
  rcases goal with ordinary | ⟨horizon,b,final,step⟩
  · left
    change T.canonicalMonitorState H h τ (d.jointFinish e.last) ∈ T.canonicalGoal h τ at ordinary
    simpa only [jointFinish,canonicalJoinState_monitor] using ordinary
  · have reached : T.canonicalMonitorState H h τ b ∈ T.canonicalGoal h τ := final
    refine Or.inr ⟨horizon,_,reached,?_⟩
    simpa only [jointFinish,canonicalJoinState_monitor] using step.monitorStep

private theorem jointZero (i : Fin e.n) (zero : e.duration i = 0) :
    d.jointStart i = d.jointFinish i := by
  have times := (e.duration_zero_iff i).1 zero
  have sys : d.sysStart i = d.sysFinish i := d.system.stateAtTime_congr _ _ rfl times
  have mon : e.start i = e.finish i := by
    apply Subtype.ext
    refine Prod.ext (e.flow i).1 ?_
    have eq : (⟨(e.duration i : ℝ),by simp⟩ : Set.Icc (0 : ℝ) (e.duration i)) =
        ⟨0,by simp⟩ := Subtype.ext (by simp [zero])
    exact (e.flow i).2.1.symm.trans (eq ▸ (e.flow i).2.2.1)
  apply Subtype.ext
  change (((d.sysStart i).val.1,(e.start i).val.1),
      T.canonicalJoinValue (d.sysStart i).val.2 (e.start i).val.2) =
    (((d.sysFinish i).val.1,(e.finish i).val.1),
      T.canonicalJoinValue (d.sysFinish i).val.2 (e.finish i).val.2)
  rw [sys,mon]

private theorem flowPiece (i : Fin e.n) (pos : 0 < e.duration i) :
    ∃ p : ProjectedFlowPiece (B H h τ) σ T.canonicalSystemCoordinate,
      p.start = d.jointStart i ∧ p.finish = d.jointFinish i ∧
      p.left = e.time i.castSucc ∧ p.left + (p.duration : ℝ) = e.time i.succ := by
  obtain ⟨γ,step,_,observe⟩ := d.jointFlow i pos
  let p : ProjectedFlowPiece (B H h τ) σ T.canonicalSystemCoordinate := {
    left := e.time i.castSucc
    duration := e.duration i
    positive := pos
    start := d.jointStart i
    finish := d.jointFinish i
    curve := γ
    step := step
    observe := observe }
  refine ⟨p,rfl,rfl,rfl,?_⟩
  change e.time i.castSucc + (e.duration i : ℝ) = e.time i.succ
  rw [e.duration_eq]
  ring

/-- Construct a product execution that observes the signal through the cut.
Zero-time visits contribute discrete transitions. A goal jump at the horizon
starts from the last flow endpoint. -/
theorem existsProductPrefix (d : CanonicalSynchronization H h τ e) (goal : d.goalAtEnd) :
    ∃ aug : FiniteSignal T.CanonicalCompositionVar,
      (aug.reindex T.canonicalSystemCoordinate) = σ ∧
      (B H h τ).PrelimReachesStateOrFinalJump aug (T.canonicalProductGoal H h τ) := by
  let i : Fin e.n := ⟨0,e.nonempty⟩
  have assembled : ∃ a, Relation.ReflTransGen (B H h τ).DiscreteStep (d.jointStart i) a ∧
      Nonempty (ProjectedFlowWord (B H h τ) σ T.canonicalSystemCoordinate a
        (e.time 0) (d.jointFinish e.last) e.cut) := by
    refine ProjectedFlowWord.ofVisits e.nonempty d.jointStart d.jointFinish e.time
      ?_ ?_ ?_ e.last_positive
    · intro j live
      exact d.jointJump ⟨j.val,by omega⟩
    · intro j same
      exact d.jointZero j ((e.duration_zero_iff j).2 same)
    · intro j different
      exact d.flowPiece j
        (pos_iff_ne_zero.2 (fun zero => different ((e.duration_zero_iff j).1 zero)))
  obtain ⟨a,lead,⟨word⟩⟩ := assembled
  have time : e.time i.castSucc = 0 := e.first_zero
  obtain ⟨aug,out,horizon,projects,_,_,final,endTime,_,_⟩ := word.toExecution
    (fun v => T.canonicalJoinValue v (fun _ => 0)) (fun _ _ => rfl)
    (d.jointStart i) d.jointInitial time lead (e.horizon.symm ▸ e.stop_le)
  have same : aug.reindex T.canonicalSystemCoordinate = σ := by
    rcases aug with ⟨r,pr,val⟩
    rcases σ with ⟨s,ps,signal⟩
    dsimp only at horizon
    subst r
    dsimp only [FiniteSignal.reindex]
    congr 1
    funext t x
    exact projects t t rfl x
  refine ⟨aug,same,out.reaches_of_goalAtEnd ?_⟩
  rw [final]
  rcases goal with ordinary | ⟨time,b,reached,step⟩
  · exact Or.inl ordinary
  · have atHorizon : out.ReachesHorizon :=
      endTime.trans (time.trans (e.horizon.symm.trans horizon.symm))
    exact Or.inr ⟨atHorizon,b,reached,step.discreteStep⟩

end CanonicalSynchronization

/-- A synchronized goal witness contains an admissible property execution and
a system execution covering the whole signal. The product prefix may stop
early. A goal jump at the horizon is a property-only transition. -/
def CanonicalReaches (H : HybridAutomaton Mode Label Var) (h : T.TranslationReady)
    (σ : FiniteSignal Var) : Prop :=
  ∃ (e : T.CanonicalExecution h σ.horizon σ)
    (d : CanonicalSynchronization H h σ.horizon e),
    d.goalAtEnd

theorem CanonicalReaches.existsProductPrefix {H : HybridAutomaton Mode Label Var}
    {h : T.TranslationReady} {σ : FiniteSignal Var} (goal : T.CanonicalReaches H h σ) :
    ∃ aug : FiniteSignal T.CanonicalCompositionVar,
      aug.reindex T.canonicalSystemCoordinate = σ ∧
      (T.canonicalProduct H h σ.horizon).PrelimReachesStateOrFinalJump aug
        (T.canonicalProductGoal H h σ.horizon) := by
  obtain ⟨e,d,g⟩ := goal
  exact d.existsProductPrefix g

run_elab do
  for decl in #[``CanonicalSynchronization.singletonExit_system_idle,
      ``CanonicalSynchronization.joint_horizon_jump,
      ``CanonicalReaches.existsProductPrefix] do
    for ax in ← Lean.collectAxioms decl do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{decl} uses unexpected axiom {ax}"

end STLTableau.Section4.Tableau
