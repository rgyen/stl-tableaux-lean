import STLTableaux.Automata.Execution.ObservedFlowSubdivision

/-! Refine actual component executions on chosen common time boundaries.
The result is positive observed cells with RTG connectors. Artificial cuts
are idles; original jump blocks are retained. Do not normalize the components
independently before pasting, since that would erase their common cuts. -/
namespace STLTableau.HybridAutomaton
variable {M L V : Type*} {H : HybridAutomaton M L V} {σ : FiniteSignal V}

namespace PrelimExecution
variable (e : H.PrelimExecution σ)

def observedFlow (i : Fin e.count) : ObservedFlow H σ where
  start := e.start i
  finish := e.finish i
  beginTime := e.boundary i.castSucc
  endTime := e.boundary i.succ
  duration := e.duration i
  positive := e.duration_pos i
  duration_eq := e.duration_eq i
  curve := e.curve i
  step := e.continuousStep i
  observe := e.signal_eq i

variable {k : ℕ} {b : Fin (k + 1) → ℝ}
variable (r : RefinesBoundaries e.boundary b) (hb : StrictMono b)

noncomputable def refinedFlow (j : Fin k) : ObservedFlow H σ :=
  (e.observedFlow (r.cell hb j)).sliceAt (b j.castSucc) (b j.succ)
    ⟨r.cell_left hb j, hb (by simp), r.cell_right hb j⟩

theorem refinedFlow_begin (j : Fin k) : (e.refinedFlow r hb j).beginTime = b j.castSucc :=
  (e.observedFlow _).sliceAt_begin _ _ _

theorem refinedFlow_end (j : Fin k) : (e.refinedFlow r hb j).endTime = b j.succ :=
  (e.observedFlow _).sliceAt_end _ _ _

theorem refinedFlow_first_start (hk : 0 < k) :
    (e.refinedFlow r hb ⟨0, hk⟩).start = e.start ⟨0, e.nonempty⟩ := by
  have first : r.cell hb ⟨0, hk⟩ = ⟨0, e.nonempty⟩ :=
    Fin.ext (r.cell_first e.increasing hb hk)
  have start := (e.observedFlow (r.cell hb ⟨0, hk⟩)).sliceAt_start
    (b (⟨0, hk⟩ : Fin k).castSucc) (b (⟨0, hk⟩ : Fin k).succ)
    ⟨r.cell_left hb _, hb (by change (0 : ℕ) < 1; omega), r.cell_right hb _⟩
    (by
      change b 0 = e.boundary (r.cell hb ⟨0, hk⟩).castSucc
      rw [first]
      exact r.first)
  change (e.refinedFlow r hb ⟨0, hk⟩).start = e.start (r.cell hb ⟨0, hk⟩) at start
  exact start.trans (congrArg e.start first)

theorem refinedFlow_initial (hk : 0 < k) :
    Relation.ReflTransGen H.DiscreteStep e.initialState (e.refinedFlow r hb ⟨0, hk⟩).start :=
  (e.refinedFlow_first_start r hb hk).symm ▸ e.initialSteps

theorem refinedFlow_final (hk : 0 < k) :
    (e.refinedFlow r hb ⟨k - 1, by omega⟩).finish = e.finalState := by
  let j : Fin k := ⟨k - 1, by omega⟩
  have last : r.cell hb j = e.lastIndex := by
    apply Fin.ext
    have bound := r.cell_last e.increasing hb hk
    change (r.cell hb j).val + 1 = e.count at bound
    change (r.cell hb j).val = e.count - 1
    omega
  have time : j.succ = Fin.last k := Fin.ext (by dsimp [j]; omega)
  have finish := (e.observedFlow (r.cell hb j)).sliceAt_finish (b j.castSucc) (b j.succ)
    ⟨r.cell_left hb _, hb (by simp), r.cell_right hb _⟩ (by
      rw [time, r.last]
      change e.boundary (Fin.last e.count) = e.boundary (r.cell hb j).succ
      rw [last]
      congr 1
      apply Fin.ext
      dsimp [lastIndex]
      have := e.nonempty
      omega)
  exact finish.trans (congrArg e.finish last)

theorem refinedFlow_connector (j : Fin k) (hj : j.val + 1 < k) :
    Relation.ReflTransGen H.DiscreteStep (e.refinedFlow r hb j).finish
      (e.refinedFlow r hb ⟨j.val + 1, hj⟩).start := by
  rcases r.cell_next e.increasing hb j hj with same | ⟨next, time⟩
  · have start : (e.refinedFlow r hb ⟨j.val + 1, hj⟩).start =
        (e.refinedFlow r hb j).finish := by
      exact ((e.observedFlow (r.cell hb j)).sliceAt_join_of_eq
        (e.observedFlow (r.cell hb ⟨j.val + 1, hj⟩)) (congrArg e.observedFlow same)
        (b j.castSucc) (b j.succ) (b (⟨j.val + 1, hj⟩ : Fin k).succ)
        ⟨r.cell_left hb _, hb (by simp), r.cell_right hb _⟩
        ⟨r.cell_left hb _, hb (by change j.val + 1 < j.val + 1 + 1; omega),
          r.cell_right hb _⟩).symm
    exact start.symm ▸ Relation.ReflTransGen.refl
  · let i := r.cell hb j
    let l := r.cell hb ⟨j.val + 1, hj⟩
    have live : i.val + 1 < e.count := next.symm ▸ l.isLt
    have nextIndex : l = ⟨i.val + 1, live⟩ := Fin.ext next
    have finish := (e.observedFlow i).sliceAt_finish (b j.castSucc) (b j.succ)
      ⟨r.cell_left hb _, hb (by simp), r.cell_right hb _⟩ time
    have start := (e.observedFlow l).sliceAt_start (b j.succ)
      (b (⟨j.val + 1, hj⟩ : Fin k).succ)
      ⟨r.cell_left hb _, hb (by change j.val + 1 < j.val + 1 + 1; omega),
        r.cell_right hb _⟩ (by
        change b j.succ = e.boundary l.castSucc
        rw [time]
        exact congrArg e.boundary (Fin.ext next.symm))
    change (e.refinedFlow r hb j).finish = e.finish i at finish
    change (e.refinedFlow r hb ⟨j.val + 1, hj⟩).start = e.start l at start
    rw [finish, start, nextIndex]
    exact (e.discreteSteps i live).to_reflTransGen

/-- Cutting does not lose any point on an original CLOSED flow, including its
right endpoint. In particular, a continuous goal visit survives subdivision. -/
theorem refinedFlow_covers (i : Fin e.count) {s : H.State}
    (visit : (e.observedFlow i).VisitsState s) :
    ∃ j, (e.refinedFlow r hb j).VisitsState s := by
  obtain ⟨t, state⟩ := visit
  have bound : t.val ≤ (e.duration i : ℝ) := t.property.2
  have duration : (e.duration i : ℝ) = e.boundary i.succ - e.boundary i.castSucc :=
    e.duration_eq i
  have inside : e.boundary i.castSucc ≤ e.boundary i.castSucc + t.val ∧
      e.boundary i.castSucc + t.val ≤ e.boundary i.succ := by
    constructor <;> linarith [t.property.1, bound, duration]
  obtain ⟨j, owner, lower, upper⟩ := r.covers_old_cell e.increasing hb i inside
  have bounds : (e.observedFlow i).beginTime ≤ b j.castSucc ∧
      b j.castSucc < b j.succ ∧ b j.succ ≤ (e.observedFlow i).endTime := by
    change e.boundary i.castSucc ≤ b j.castSucc ∧
      b j.castSucc < b j.succ ∧ b j.succ ≤ e.boundary i.succ
    simpa only [owner] using
      And.intro (r.cell_left hb j) (And.intro (hb (by simp)) (r.cell_right hb j))
  have observed := (e.observedFlow i).visits_sliceAt (b j.castSucc) (b j.succ) bounds t
    ⟨lower, upper⟩
  have stateEq : (e.observedFlow i).step.stateAt t = s := Subtype.ext state.symm
  rw [stateEq] at observed
  have flowEq := (e.observedFlow (r.cell hb j)).sliceAt_congr (e.observedFlow i)
    (congrArg e.observedFlow owner) (b j.castSucc) (b j.succ)
    ⟨r.cell_left hb j, hb (by simp), r.cell_right hb j⟩ bounds
  have equal : e.refinedFlow r hb j =
      (e.observedFlow i).sliceAt (b j.castSucc) (b j.succ) bounds := flowEq
  exact ⟨j, equal.symm ▸ observed⟩

/-- Every original interflow jump block still occurs at a refined boundary,
with exactly the same endpoint states. Its intermediate goal visits are thus
available without choosing new jumps or contracting the old block. -/
theorem refinedFlow_old_boundary (i : Fin e.count) (hi : i.val + 1 < e.count) :
    ∃ (j : Fin k) (hj : j.val + 1 < k),
      (e.refinedFlow r hb j).finish = e.finish i ∧
      (e.refinedFlow r hb ⟨j.val + 1, hj⟩).start = e.start ⟨i.val + 1, hi⟩ := by
  obtain ⟨j, owner, _, lower⟩ := r.covers_old_cell e.increasing hb i
    ⟨(e.increasing (show i.castSucc < i.succ by simp)).le, le_rfl⟩
  have time : b j.succ = e.boundary i.succ :=
    le_antisymm (by simpa only [owner] using r.cell_right hb j) lower
  have jNext : j.val + 1 < k := by
    have earlier : b j.succ < b (Fin.last k) := by
      rw [time, r.last]
      exact e.increasing (by change i.val + 1 < e.count; exact hi)
    exact hb.lt_iff_lt.mp earlier
  have next : r.cell hb ⟨j.val + 1, jNext⟩ = ⟨i.val + 1, hi⟩ := by
    apply r.cell_eq e.increasing hb
    · change e.boundary i.succ ≤ b j.succ
      exact time.ge
    · change b j.succ < e.boundary (⟨i.val + 1, hi⟩ : Fin e.count).succ
      rw [time]
      exact e.increasing (by change i.val + 1 < i.val + 1 + 1; omega)
  have finish := (e.observedFlow (r.cell hb j)).sliceAt_finish (b j.castSucc) (b j.succ)
    ⟨r.cell_left hb j, hb (by simp), r.cell_right hb j⟩
    (by change b j.succ = e.boundary (r.cell hb j).succ; rw [owner]; exact time)
  have start := (e.observedFlow (r.cell hb ⟨j.val + 1, jNext⟩)).sliceAt_start
    (b j.succ) (b (⟨j.val + 1, jNext⟩ : Fin k).succ)
    ⟨r.cell_left hb _, hb (by change j.val + 1 < j.val + 1 + 1; omega),
      r.cell_right hb _⟩ (by
        change b j.succ = e.boundary (r.cell hb ⟨j.val + 1, jNext⟩).castSucc
        rw [next]
        exact time)
  exact ⟨j, jNext, finish.trans (congrArg e.finish owner), start.trans (congrArg e.start next)⟩

/-- Every state visit of the given execution remains represented in the
refined cells or the unchanged initial/interflow discrete blocks. -/
theorem refinedFlow_preserves_visit (hk : 0 < k) {s : H.State} (visit : e.VisitsState s) :
    (∃ j, (e.refinedFlow r hb j).VisitsState s) ∨
    (Relation.ReflTransGen H.DiscreteStep e.initialState s ∧
      Relation.ReflTransGen H.DiscreteStep s (e.refinedFlow r hb ⟨0, hk⟩).start) ∨
    ∃ (j : Fin k) (hj : j.val + 1 < k),
      Relation.ReflTransGen H.DiscreteStep (e.refinedFlow r hb j).finish s ∧
      Relation.ReflTransGen H.DiscreteStep s (e.refinedFlow r hb ⟨j.val + 1, hj⟩).start := by
  rcases visit with ⟨i, u, state⟩ | ⟨before, after⟩ | ⟨i, hi, before, after⟩
  · exact Or.inl (e.refinedFlow_covers r hb i ⟨u, state⟩)
  · exact Or.inr (Or.inl ⟨before, (e.refinedFlow_first_start r hb hk).symm ▸ after⟩)
  · obtain ⟨j, hj, finish, start⟩ := e.refinedFlow_old_boundary r hb i hi
    exact Or.inr (Or.inr ⟨j, hj, finish.symm ▸ before, start.symm ▸ after⟩)

theorem exists_common_refined_flows
    {N K W : Type*} {G : HybridAutomaton N K W} {ρ : FiniteSignal W}
    (out : G.PrelimExecution ρ) (full : e.ReachesHorizon) (outFull : out.ReachesHorizon)
    (horizon : σ.horizon = ρ.horizon) :
    ∃ (k : ℕ) (b : Fin (k + 1) → ℝ) (hb : StrictMono b)
      (r₁ : RefinesBoundaries e.boundary b) (r₂ : RefinesBoundaries out.boundary b),
      0 < k ∧ b 0 = 0 ∧ b (Fin.last k) = σ.horizon ∧
      (∀ j, (e.refinedFlow r₁ hb j).beginTime = (out.refinedFlow r₂ hb j).beginTime ∧
        (e.refinedFlow r₁ hb j).endTime = (out.refinedFlow r₂ hb j).endTime) := by
  obtain ⟨k, b, hb, r₁, r₂, _⟩ := exists_common_time_boundaries e.boundary out.boundary
    e.increasing out.increasing (e.first_zero.trans out.first_zero.symm)
    (full.trans (horizon.trans outFull.symm))
  have zero : b 0 = 0 := r₁.first.trans e.first_zero
  have last : b (Fin.last k) = σ.horizon := r₁.last.trans full
  have positive : 0 < k := by
    by_contra nonpos
    have empty : k = 0 := by omega
    have indices : (Fin.last k : Fin (k + 1)) = 0 := Fin.ext (by simp [empty])
    have positive := σ.horizon_pos
    rw [indices, zero] at last
    linarith
  refine ⟨k, b, hb, r₁, r₂, positive, zero, last, ?_⟩
  intro j
  exact ⟨(e.refinedFlow_begin r₁ hb j).trans (out.refinedFlow_begin r₂ hb j).symm,
    (e.refinedFlow_end r₁ hb j).trans (out.refinedFlow_end r₂ hb j).symm⟩

run_elab do
  for name in #[``refinedFlow, ``refinedFlow_first_start, ``refinedFlow_initial,
      ``refinedFlow_final, ``refinedFlow_connector, ``refinedFlow_covers,
      ``refinedFlow_old_boundary, ``refinedFlow_preserves_visit,
      ``exists_common_refined_flows] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name} uses unexpected axiom {ax}"

end PrelimExecution
end STLTableau.HybridAutomaton
