import STLTableaux.Automata.Translation.CanonicalTableauExecution

/-! A goal may be visited before the end of an execution. Cutting within a
positive visit retains exactly the same earlier visits and their edge labels. -/

namespace STLTableau.Section4.Tableau.CanonicalExecution
open Section3

variable {Clock Var State : Type*} {T : Tableau Clock Var State}
variable {h : T.TranslationReady} {τ : ℝ} {σ : FiniteSignal Var}
variable (e : T.CanonicalExecution h τ σ)

private def atVisit (i : Fin e.n) (j : Fin (i.val + 1)) : Fin e.n :=
  ⟨j.val, by have := j.isLt; have := i.isLt; omega⟩

private noncomputable def atTime (i : Fin e.n) (r : NNReal) (j : Fin (i.val + 2)) : ℝ :=
  if hj : j.val < i.val + 1 then e.time ⟨j.val, by have := i.isLt; omega⟩
  else e.time i.castSucc + r

private theorem atTime_castSucc (i : Fin e.n) (r : NNReal) (j : Fin (i.val + 1)) :
    e.atTime i r j.castSucc = e.time (e.atVisit i j).castSucc :=
  dif_pos j.isLt

private theorem atTime_succ (i : Fin e.n) (r : NNReal) (j : Fin (i.val + 1))
    (hj : j.val < i.val) :
    e.atTime i r j.succ = e.time (e.atVisit i j).succ :=
  dif_pos (by change j.val + 1 < i.val + 1; omega)

private theorem atTime_last (i : Fin e.n) (r : NNReal) :
    e.atTime i r (Fin.last (i.val + 1)) = e.time i.castSucc + r :=
  dif_neg (by change ¬ i.val + 1 < i.val + 1; omega)

private def atDuration (i : Fin e.n) (r : NNReal) (j : Fin (i.val + 1)) : NNReal :=
  if j.val = i.val then r else e.duration (e.atVisit i j)

private theorem atDuration_le (i : Fin e.n) (r : NNReal) (hr : r ≤ e.duration i)
    (j : Fin (i.val + 1)) : e.atDuration i r j ≤ e.duration (e.atVisit i j) := by
  unfold atDuration
  split_ifs with he
  · rwa [show e.atVisit i j = i from Fin.ext he]
  · exact le_rfl

private theorem atDuration_eq (i : Fin e.n) (r : NNReal) (j : Fin (i.val + 1)) :
    (e.atDuration i r j : ℝ) = e.atTime i r j.succ - e.atTime i r j.castSucc := by
  rw [e.atTime_castSucc]
  unfold atDuration
  split_ifs with he
  · have h₁ : j.succ = Fin.last (i.val + 1) := Fin.ext (by change j.val + 1 = i.val + 1; omega)
    rw [h₁, e.atTime_last, show e.atVisit i j = i from Fin.ext he]
    ring
  · have := j.isLt
    rw [e.atTime_succ i r j (by omega)]
    exact e.duration_eq _

private def atFinish (i : Fin e.n) (r : NNReal) (hr : r ≤ e.duration i) (j : Fin (i.val + 1)) :
    (T.canonicalAutomaton h τ).State :=
  (e.flow (e.atVisit i j)).stateAt
    ⟨e.atDuration i r j, (e.atDuration i r j).coe_nonneg, e.atDuration_le i r hr j⟩

private theorem atFinish_before (i : Fin e.n) (r : NNReal) (hr : r ≤ e.duration i)
    (j : Fin (i.val + 1)) (hj : j.val < i.val) :
    e.atFinish i r hr j = e.finish (e.atVisit i j) := by
  apply Subtype.ext
  change ((e.start (e.atVisit i j)).val.1, e.curve (e.atVisit i j) _) = _
  refine Prod.ext ?_ ?_
  · exact (e.flow (e.atVisit i j)).1
  have hh : (⟨(e.atDuration i r j : ℝ), (e.atDuration i r j).coe_nonneg,
        e.atDuration_le i r hr j⟩ : Set.Icc (0 : ℝ) (e.duration (e.atVisit i j))) =
      ⟨e.duration (e.atVisit i j), by simp⟩ := by
    apply Subtype.ext
    simp [atDuration, hj.ne]
  rw [hh]
  exact (e.flow (e.atVisit i j)).2.2.1

/-- End the witness in any positive part of visit `i`. Neither the earlier
jumps nor the left marker inferred at any retained visit are changed. -/
noncomputable def truncate (i : Fin e.n) (r : NNReal) (pos : 0 < r) (hr : r ≤ e.duration i) :
    T.CanonicalExecution h τ σ where
  n := i.val + 1
  nonempty := Nat.succ_pos _
  time := e.atTime i r
  first_zero := (e.atTime_castSucc i r 0).trans e.first_zero
  monotone := by
    apply Fin.monotone_iff_le_succ.mpr
    intro j
    have hd := (e.atDuration i r j).coe_nonneg
    rw [e.atDuration_eq i r j] at hd
    exact sub_nonneg.mp hd
  isolated := by
    intro j hj he
    let k := e.atVisit i j
    let j' : Fin (i.val+1) := ⟨j.val + 1,hj⟩
    have jk : j.val < i.val := by omega
    change e.atTime i r j.castSucc = e.atTime i r j.succ at he
    rw [e.atTime_castSucc, e.atTime_succ _ _ _ jk] at he
    change e.atTime i r j'.castSucc ≠ e.atTime i r j'.succ
    by_cases last : j'.val = i.val
    · have hd : e.atDuration i r j' = r := if_pos last
      have hp : (0 : ℝ) < (e.atDuration i r j' : ℝ) := by rw [hd]; exact pos
      rw [e.atDuration_eq] at hp
      exact (sub_pos.mp hp).ne
    · have hj' : j'.val < i.val := by have := j'.isLt; omega
      rw [e.atTime_castSucc, e.atTime_succ _ _ _ hj']
      exact e.isolated k (by dsimp [k,atVisit]; have := i.isLt; omega) he
  last_positive := by
    intro j hj
    have eq : j.val = i.val := by omega
    have hd : e.atDuration i r j = r := if_pos eq
    have hp : (0 : ℝ) < (e.atDuration i r j : ℝ) := by rw [hd]; exact pos
    rw [e.atDuration_eq] at hp
    exact (sub_pos.mp hp).ne
  stop_le := by
    rw [e.atTime_last]
    calc
      _ ≤ e.time i.succ := by
        have hh : (r : ℝ) ≤ e.duration i := hr
        rw [e.duration_eq] at hh
        linarith
      _ ≤ τ := (e.monotone (Fin.le_last _)).trans e.stop_le
  horizon := e.horizon
  start j := e.start (e.atVisit i j)
  finish := e.atFinish i r hr
  initial := e.initial
  initialLabel := e.initialLabel
  initialValue := e.initialValue
  initial_edge := e.initial_edge
  initial_guard := e.initial_guard
  initial_reset := e.initial_reset
  initial_observation := e.initial_observation
  duration := e.atDuration i r
  duration_eq := e.atDuration_eq i r
  curve j := HybridFlow.prefixCurve (e.curve (e.atVisit i j)) _ (e.atDuration_le i r hr j)
  flow j := (e.flow (e.atVisit i j)).prefixStep _ (e.atDuration_le i r hr j)
  jump j := by
    have hlt := j.isLt
    change j.val < i.val + 1 - 1 at hlt
    let j' : Fin (e.n-1) := ⟨j.val, by have := i.isLt; omega⟩
    let k : Fin (i.val+1) := ⟨j.val, by omega⟩
    have hj : k.val < i.val := by dsimp [k]; omega
    refine ⟨(e.jump j').val, ?_⟩
    dsimp only
    rw [e.atFinish_before i r hr k hj]
    exact (e.jump j').property
  compatible := by
    intro j m hm
    have he := e.compatible (e.atVisit i j) m hm
    change m = IntervalPartition.singletonMarkers (e.atTime i r) j.castSucc
    rcases j with ⟨_ | j, hj⟩
    · simpa only [Fin.castSucc_mk, atVisit, IntervalPartition.singletonMarkers_first] using he
    · change j + 1 < i.val + 1 at hj
      let k : Fin (i.val+1) := ⟨j, by omega⟩
      let k' : Fin e.n := e.atVisit i k
      change _ = IntervalPartition.singletonMarkers e.time ⟨k'.val+1, by omega⟩ at he
      change _ = IntervalPartition.singletonMarkers (e.atTime i r) ⟨k.val+1, by omega⟩
      rw [IntervalPartition.singletonMarkers_succ e.time k'] at he
      rw [IntervalPartition.singletonMarkers_succ (e.atTime i r) k]
      change m = if e.atTime i r k.castSucc = e.atTime i r k.succ then ○ else ●
      rw [e.atTime_castSucc, e.atTime_succ i r k (by dsimp [k]; omega)]
      exact he
  singleton_exit := by
    intro j x zero
    have hlt := j.isLt
    change j.val < i.val + 1 - 1 at hlt
    let j' : Fin (e.n-1) := ⟨j.val, by have := i.isLt; omega⟩
    let k : Fin (i.val+1) := ⟨j.val, by omega⟩
    have hj : k.val < i.val := by dsimp [k]; omega
    change e.atDuration i r k = 0 at zero
    rw [show e.atDuration i r k = e.duration (e.atVisit i k) from if_neg hj.ne] at zero
    change (e.atFinish i r hr k).val.2 _ = _
    rw [e.atFinish_before i r hr k hj]
    exact e.singleton_exit j' x zero
  observes := by
    intro j t ht positive x
    change e.atTime i r j.castSucc ≤ t.val ∧ t.val < e.atTime i r j.succ at ht
    have low : e.time (e.atVisit i j).castSucc ≤ t.val := (e.atTime_castSucc i r j) ▸ ht.1
    have high : t.val < e.time (e.atVisit i j).succ := by
      have hd : (e.atDuration i r j : ℝ) ≤ e.duration (e.atVisit i j) := e.atDuration_le i r hr j
      rw [e.atDuration_eq, e.atTime_castSucc, e.duration_eq] at hd
      linarith [ht.2]
    rw [e.observes (e.atVisit i j) t ⟨low,high⟩ positive x]
    unfold HybridFlow.prefixCurve
    apply congrArg (fun u => e.curve (e.atVisit i j) u (.inl x))
    apply Subtype.ext
    change t.val - e.time (e.atVisit i j).castSucc = t.val - e.atTime i r j.castSucc
    rw [e.atTime_castSucc]

theorem prefix_finish (i : Fin e.n) (r : NNReal) (pos : 0 < r) (hr : r ≤ e.duration i) :
    (e.truncate i r pos hr).finish (e.truncate i r pos hr).last =
      (e.flow i).stateAt ⟨r, r.coe_nonneg, hr⟩ := by
  have he : e.atVisit i (e.truncate i r pos hr).last = i := Fin.ext (by
    simp [truncate,last,TableauExecution.last,atVisit])
  have hd : e.atDuration i r (e.truncate i r pos hr).last = r := by
    simp [truncate,last,TableauExecution.last,atDuration]
  let j := e.atVisit i (e.truncate i r pos hr).last
  apply Subtype.ext
  change ((e.start j).val.1, e.curve j _) = ((e.start i).val.1, e.curve i _)
  refine Prod.ext (congrArg (fun k => (e.start k).val.1) he) ?_
  let t : Set.Icc (0 : ℝ) (e.duration j) :=
    ⟨e.atDuration i r (e.truncate i r pos hr).last,
      (e.atDuration i r (e.truncate i r pos hr).last).coe_nonneg, e.atDuration_le i r hr _⟩
  let t' : Set.Icc (0 : ℝ) (e.duration i) := ⟨r, r.coe_nonneg, hr⟩
  change e.curve j t = e.curve i t'
  suffices step : ∀ (k l : Fin e.n) (u : Set.Icc (0 : ℝ) (e.duration k))
      (v : Set.Icc (0 : ℝ) (e.duration l)), k = l → u.val = v.val → e.curve k u = e.curve l v by
    exact step j i t t' he (congrArg NNReal.toReal hd)
  intro k l u v hkl huv
  subst l
  exact congrArg (e.curve k) (Subtype.ext huv)

private theorem prefix_cut (i : Fin e.n) (r : NNReal) (pos : 0 < r) (hr : r ≤ e.duration i) :
    (e.truncate i r pos hr).cut = e.time i.castSucc + r := by
  change e.atTime i r (Fin.last (i.val + 1)) = _
  exact e.atTime_last i r

/-- Test an ordinary state visit, or take a final step if that very state
is the endpoint at τ. In the latter case no flow follows the jump. -/
def VisitsGoal : Prop :=
  ∃ (i : Fin e.n) (r : NNReal) (hr : r ≤ e.duration i),
    (T.canonicalAutomaton h τ).GoalAtEnd (T.canonicalGoal h τ)
      ((e.flow i).stateAt ⟨r, r.coe_nonneg, hr⟩) (e.time i.castSucc + r = τ)

theorem visitsGoal_of_end (goal : e.goal) : e.VisitsGoal := by
  refine ⟨e.last,e.duration e.last,le_rfl,?_⟩
  have state : (e.flow e.last).stateAt ⟨e.duration e.last,by simp⟩ = e.finish e.last :=
    Subtype.ext (Prod.ext (e.flow e.last).1 (e.flow e.last).2.2.1)
  have time : e.time e.last.castSucc + (e.duration e.last : ℝ) = e.cut := by
    rw [e.duration_eq,e.last_succ]
    change e.time e.last.castSucc + (e.cut - e.time e.last.castSucc) = e.cut
    ring
  rw [state,time]
  exact goal

/-- Keep the cut explicit: different visits to a goal may induce different
partitions of the same signal. -/
def GoalInduces (P : IntervalPartition σ.domain) : Prop :=
  ∃ (i : Fin e.n) (r : NNReal) (pos : 0 < r) (hr : r ≤ e.duration i),
    let pre := e.truncate i r pos hr
    pre.goal ∧ pre.Induces P

theorem visitsGoal_iff_cut
    (final_successor : ∀ (a b : T.states) (l : EdgeLabel Clock),
      a ∈ T.goalModes → (a.val,l,b.val) ∈ T.edges → b ∈ T.goalModes) :
    e.VisitsGoal ↔
      ∃ (i : Fin e.n) (r : NNReal) (pos : 0 < r) (hr : r ≤ e.duration i),
        (e.truncate i r pos hr).goal := by
  have atStart (i : Fin e.n) (hr : (0 : NNReal) ≤ e.duration i) :
      (e.flow i).stateAt ⟨(0 : NNReal), by simp, hr⟩ = e.start i := by
    apply Subtype.ext
    exact Prod.ext rfl (e.flow i).2.1
  have cut_of_final (i : Fin e.n) (goal : (e.start i).val.1 ∈ T.goalModes)
      (pos : 0 < e.duration i) :
      (e.truncate i (e.duration i) pos le_rfl).goal := by
    rw [CanonicalExecution.goal, e.prefix_finish]
    exact Or.inl goal
  constructor
  · rintro ⟨i,r,hr,goal⟩
    rcases eq_zero_or_pos r with rfl | pos
    · rw [atStart i hr] at goal
      have goal : (e.start i).val.1 ∈ T.goalModes := by
        rcases goal with goal | ⟨late, _⟩
        · exact goal
        · change e.time i.castSucc + 0 = τ at late
          rw [add_zero] at late
          exact ((e.starts_before_horizon i).ne late).elim
      rcases eq_zero_or_pos (e.duration i) with zero | pos
      · have eq := (e.duration_zero_iff i).mp zero
        have next : i.val+1 < e.n := by
          have := i.isLt
          by_contra! last
          exact e.last_positive i (by omega) eq
        let j : Fin e.n := ⟨i.val+1,next⟩
        have pos : 0 < e.duration j := pos_iff_ne_zero.mpr
          (fun hzero => e.isolated i next eq ((e.duration_zero_iff j).mp hzero))
        let k : Fin (e.n-1) := ⟨i.val,by omega⟩
        have edge := (e.jump k).property.1
        change ((e.finish i).val.1.val, (e.jump k).val, (e.start j).val.1.val) ∈ T.edges at edge
        rw [← (e.flow i).1] at edge
        have gj := final_successor _ _ _ goal edge
        exact ⟨j,e.duration j,pos,le_rfl,cut_of_final j gj pos⟩
      · exact ⟨i,e.duration i,pos,le_rfl,cut_of_final i goal pos⟩
    · exact ⟨i,r,pos,hr,by rwa [CanonicalExecution.goal, e.prefix_finish,e.prefix_cut]⟩
  · rintro ⟨i,r,pos,hr,goal⟩
    rw [CanonicalExecution.goal,e.prefix_finish,e.prefix_cut] at goal
    exact ⟨i,r,hr,goal⟩

end STLTableau.Section4.Tableau.CanonicalExecution
