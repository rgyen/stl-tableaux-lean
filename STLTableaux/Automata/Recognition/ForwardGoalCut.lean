import STLTableaux.Automata.Execution.HybridAutomata

namespace STLTableau.HybridAutomaton
variable {Mode Label Var : Type*} (H : HybridAutomaton Mode Label Var)


/-- Data supplied by a finite sequence of the positive flows and
jumps. Unlike Execution, it requires no stopping state, final jump or
observation at the right endpoint of its last flow. -/
structure ForwardPrefix (σ : FiniteSignal Var) where
  n : ℕ
  hn : 0 < n
  boundary : Fin (n+1) → ℝ
  zero : boundary 0 = 0
  mono : StrictMono boundary
  horizon : boundary (Fin.last n) ≤ σ.horizon
  duration : Fin n → NNReal
  diff : ∀ i, (duration i : ℝ) = boundary i.succ - boundary i.castSucc
  init : H.State
  init_mem : init.val ∈ H.initial
  initial_obs : σ.value ⟨0, le_rfl, σ.horizon_pos⟩ = init.val.2
  start : Fin n → H.State
  finish : Fin n → H.State
  curve : ∀ i, Set.Icc (0 : ℝ) (duration i) → Var → ℝ
  flow : ∀ i, H.ContinuousStep (start i) (finish i) (duration i) (curve i)
  firstSteps : Relation.ReflTransGen H.DiscreteStep init (start ⟨0,hn⟩)
  between : ∀ i (h : i.val+1 < n), Relation.TransGen H.DiscreteStep
    (finish i) (start ⟨i.val+1,h⟩)
  obs : ∀ i (t : σ.Time) (ht : boundary i.castSucc ≤ t.val ∧ t.val < boundary i.succ),
    0 < t.val →
    σ.value t = curve i ⟨t.val - boundary i.castSucc,
      sub_nonneg.mpr ht.1,by linarith [diff i,ht.2]⟩

namespace ForwardPrefix
noncomputable section
variable {H} {σ : FiniteSignal Var} (s : H.ForwardPrefix σ)

def lastFlow : Fin s.n := ⟨s.n-1,by have := s.hn; omega⟩
private def halfEnd : ℝ :=
  (s.boundary s.lastFlow.castSucc + s.boundary (Fin.last s.n)) / 2

private theorem half_bounds :
    s.boundary s.lastFlow.castSucc < s.halfEnd ∧ s.halfEnd < s.boundary (Fin.last s.n) := by
  have h := s.mono (Fin.castSucc_lt_last s.lastFlow)
  unfold halfEnd
  constructor <;> linarith

private def cutBoundary (k : Fin (s.n+1)) : ℝ :=
  if k.val = s.n then s.halfEnd else s.boundary k

private theorem cut_left (i : Fin s.n) : s.cutBoundary i.castSucc = s.boundary i.castSucc := by
  simp [cutBoundary,i.isLt.ne]

private theorem cut_mono : StrictMono s.cutBoundary := by
  intro i j hij
  have hval : i.val < j.val := hij
  have hi : i.val ≠ s.n := by have := j.isLt; omega
  by_cases hj : j.val = s.n
  · have hle : i ≤ s.lastFlow.castSucc := by
      change i.val ≤ s.n-1
      omega
    simpa [cutBoundary,hi,hj] using (s.mono.monotone hle).trans_lt s.half_bounds.1
  · simpa [cutBoundary,hi,hj] using s.mono hij

private theorem cut_right_le (i : Fin s.n) : s.cutBoundary i.succ ≤ s.boundary i.succ := by
  unfold cutBoundary
  split
  next hi =>
    have eq : i.succ = Fin.last s.n := Fin.ext hi
    rw [eq]; exact s.half_bounds.2.le
  next => exact le_rfl

private def cutDur (i : Fin s.n) : NNReal :=
  ⟨s.cutBoundary i.succ - s.cutBoundary i.castSucc,
    sub_nonneg.mpr (s.cut_mono Fin.castSucc_lt_succ).le⟩

private theorem dur_le (i : Fin s.n) : (s.cutDur i : ℝ) ≤ s.duration i := by
  change s.cutBoundary i.succ - s.cutBoundary i.castSucc ≤ _
  rw [s.cut_left,s.diff]
  linarith [s.cut_right_le i]

private def embedTime (i : Fin s.n) (t : Set.Icc (0 : ℝ) (s.cutDur i)) :
    Set.Icc (0 : ℝ) (s.duration i) := ⟨t.val,t.property.1,t.property.2.trans (s.dur_le i)⟩

private def endTime (i : Fin s.n) : Set.Icc (0 : ℝ) (s.duration i) :=
  ⟨s.cutDur i,(s.cutDur i).coe_nonneg,s.dur_le i⟩

private def cutState (i : Fin s.n) : H.State :=
  ⟨((s.start i).val.1,s.curve i (s.endTime i)),((s.flow i).2.2.2 (s.endTime i)).2⟩

private theorem unchanged_before_last (i : Fin s.n) (hi : i.val+1 < s.n) :
    s.cutState i = s.finish i := by
  have hd : (s.cutDur i : ℝ) = s.duration i := by
    change s.cutBoundary i.succ - s.cutBoundary i.castSucc = _
    rw [s.diff,s.cut_left]; simp [cutBoundary,hi.ne]
  apply Subtype.ext
  apply Prod.ext
  · exact (s.flow i).1
  exact (congrArg (s.curve i) (Subtype.ext hd)).trans (s.flow i).2.2.1

/-- Build an actual early-stopping execution from the observed flow/jump
prefix. Only the last flow is shortened. No final_signal_eq premise. -/
def stopInsideLast : H.Execution σ where
  count := s.n
  nonempty := s.hn
  initialState := s.init
  initial_mem := s.init_mem
  initial_signal_eq := s.initial_obs
  start := s.start
  finish := s.cutState
  boundary := s.cutBoundary
  first_zero := by simpa [cutBoundary,s.hn.ne] using s.zero
  increasing := s.cut_mono
  last_le_horizon := by
    change s.cutBoundary (Fin.last s.n) ≤ _
    simpa [cutBoundary] using s.half_bounds.2.le.trans s.horizon
  duration := s.cutDur
  duration_eq := fun _ => rfl
  curve := fun i t => s.curve i (s.embedTime i t)
  continuousStep := fun i =>
    ⟨rfl,(s.flow i).2.1,rfl,fun t => (s.flow i).2.2.2 (s.embedTime i t)⟩
  initialSteps := s.firstSteps
  discreteSteps := by
    intro i h
    rw [s.unchanged_before_last i h]
    exact s.between i h
  finalState := s.cutState s.lastFlow
  finalSteps := .refl
  signal_eq := by
    intro i t ht positive
    have hobs := s.obs i t ⟨(s.cut_left i) ▸ ht.1,ht.2.trans_le (s.cut_right_le i)⟩ positive
    refine hobs.trans (congrArg (s.curve i) (Subtype.ext ?_))
    change t.val - s.boundary i.castSucc = t.val - s.cutBoundary i.castSucc
    rw [s.cut_left]
  final_signal_eq := by
    intro t ht
    have he : t.val = s.halfEnd := by simpa [cutBoundary] using ht
    have hb : s.lastFlow.succ = Fin.last s.n := by
      apply Fin.ext
      change s.n-1+1 = s.n
      have := s.hn; omega
    have hobs := s.obs s.lastFlow t ⟨he ▸ s.half_bounds.1.le,
      (he.trans_lt s.half_bounds.2).trans_eq (congrArg s.boundary hb.symm)⟩ (by
        have hz := s.mono.monotone (show (0 : Fin (s.n+1)) ≤ s.lastFlow.castSucc from Fin.zero_le _)
        rw [s.zero] at hz
        linarith [s.half_bounds.1])
    refine hobs.trans (congrArg (s.curve s.lastFlow) (Subtype.ext ?_))
    change t.val - s.boundary s.lastFlow.castSucc =
      s.cutBoundary s.lastFlow.succ - s.cutBoundary s.lastFlow.castSucc
    rw [he,hb,s.cut_left]; simp [cutBoundary]

theorem reaches_if_last_goal (goal : Set Mode) (hg : (s.start s.lastFlow).val.1 ∈ goal) :
    H.Reaches σ goal := ⟨s.stopInsideLast,hg⟩

end
end ForwardPrefix
end STLTableau.HybridAutomaton
