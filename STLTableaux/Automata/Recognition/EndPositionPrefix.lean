import STLTableaux.Automata.Translation.EndPositionTranslation

namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ)
local notation "New" => T.endPositionAutomaton h τ
local notation "Old" => T.typedAutomaton h τ

theorem end_jump_global {a b : (New).State} (hj : (New).DiscreteStep a b) :
    b.val.2 (.inl T.globalClock) = a.val.2 (.inl T.globalClock) := by
  obtain ⟨_,_,_,_,_,_,_,hg,_⟩ := hj
  exact hg

theorem end_chain_global {a b : (New).State}
    (hs : Relation.ReflTransGen (New).DiscreteStep a b) :
    b.val.2 (.inl T.globalClock) = a.val.2 (.inl T.globalClock) := by
  induction hs with
  | refl => rfl
  | tail _ hj ih => exact (T.end_jump_global h τ hj).trans ih

theorem end_flow_global {σ : FiniteSignal T.TypedVar} (e : (New).Execution σ)
    (i : Fin e.count) : (e.finish i).val.2 (.inl T.globalClock) =
      (e.start i).val.2 (.inl T.globalClock) + e.duration i := by
  let u : Set.Icc (0 : ℝ) (e.duration i) := ⟨e.duration i,by simp⟩
  have hc := e.continuousStep i
  have hv := ((hc.2.2.2 u).1).2.1
  rw [show e.curve i u = (e.finish i).val.2 from hc.2.2.1] at hv
  exact hv

theorem end_entry_time {σ : FiniteSignal T.TypedVar} (e : (New).Execution σ)
    (i : Fin e.count) : (e.start i).val.2 (.inl T.globalClock) = e.boundary i.castSucc := by
  obtain ⟨k,hk⟩ := i
  induction k with
  | zero =>
    obtain ⟨_,_,_,_,hv,_,_⟩ := e.initial_mem
    have hg := congrFun hv T.globalClock
    change e.initialState.val.2 (.inl T.globalClock) = 0 at hg
    exact (T.end_chain_global h τ e.initialSteps).trans (hg.trans e.first_zero.symm)
  | succ k ih =>
    let j : Fin e.count := ⟨k, by omega⟩
    have hg := T.end_chain_global h τ (e.discreteSteps j hk).to_reflTransGen
    have hf := T.end_flow_global h τ e j
    have hd := e.duration_eq j
    have hp := ih j.isLt
    change (e.start ⟨k+1,hk⟩).val.2 (.inl T.globalClock) =
      e.boundary ⟨k+1,by omega⟩
    rw [hg,hf,hp,hd]
    change e.boundary j.castSucc + (e.boundary j.succ - e.boundary j.castSucc) =
      e.boundary j.succ
    ring

theorem end_finish_time {σ : FiniteSignal T.TypedVar} (e : (New).Execution σ)
    (i : Fin e.count) : (e.finish i).val.2 (.inl T.globalClock) = e.boundary i.succ := by
  rw [T.end_flow_global h τ e i,T.end_entry_time h τ e i,e.duration_eq]
  change e.boundary i.castSucc + (e.boundary i.succ-e.boundary i.castSucc) = _
  ring

theorem end_final_time {σ : FiniteSignal T.TypedVar} (e : (New).Execution σ) :
    e.finalState.val.2 (.inl T.globalClock) = e.boundary ⟨e.count,by omega⟩ := by
  let i : Fin e.count := ⟨e.count-1,by have := e.nonempty; omega⟩
  have eq : i.succ = (⟨e.count,by omega⟩ : Fin (e.count+1)) := by
    apply Fin.ext
    change e.count-1+1=e.count
    have := e.nonempty
    omega
  exact (T.end_chain_global h τ e.finalSteps).trans ((T.end_finish_time h τ e i).trans
    (congrArg e.boundary eq))

theorem end_refl_chain_before {a b : (New).State}
    (chain : Relation.ReflTransGen (New).DiscreteStep a b)
    (hb : b.val.2 (.inl T.globalClock) < τ) :
    Relation.ReflTransGen (Old).DiscreteStep a b := by
  induction chain with
  | refl => exact .refl
  | tail _ step ih =>
    have hmid := (T.end_jump_global h τ step) ▸ hb
    exact .tail (ih hmid) ((T.step_before_iff h τ hb).1 step)

theorem end_trans_chain_before {a b : (New).State}
    (chain : Relation.TransGen (New).DiscreteStep a b)
    (hb : b.val.2 (.inl T.globalClock) < τ) :
    Relation.TransGen (Old).DiscreteStep a b := by
  obtain ⟨z,pre,step⟩ := Relation.TransGen.tail'_iff.mp chain
  exact Relation.TransGen.tail'
    (T.end_refl_chain_before h τ pre ((T.end_jump_global h τ step) ▸ hb))
    ((T.step_before_iff h τ hb).1 step)

theorem end_start_before {σ : FiniteSignal T.TypedVar} (e : (New).Execution σ)
    (hh : σ.horizon = τ) (i : Fin e.count) :
    (e.start i).val.2 (.inl T.globalClock) < τ := by
  rw [T.end_entry_time h τ e i]
  exact (e.increasing Fin.castSucc_lt_succ).trans_le
    ((e.increasing.monotone (Fin.le_last i.succ)).trans (e.last_le_horizon.trans_eq hh))

/-- Transfer the signal, times, and transitions before the horizon to
`typedAutomaton`. At the horizon, the transferred execution ends with
the last continuous transition. -/
noncomputable def oldPrefix {σ : FiniteSignal T.TypedVar} (e : (New).Execution σ)
    (hh : σ.horizon = τ) : (Old).Execution σ where
  count := e.count
  nonempty := e.nonempty
  initialState := e.initialState
  initial_mem := e.initial_mem
  initial_signal_eq := e.initial_signal_eq
  start := e.start
  finish := e.finish
  boundary := e.boundary
  first_zero := e.first_zero
  increasing := e.increasing
  last_le_horizon := e.last_le_horizon
  duration := e.duration
  duration_eq := e.duration_eq
  curve := e.curve
  continuousStep := e.continuousStep
  initialSteps := T.end_refl_chain_before h τ e.initialSteps (T.end_start_before h τ e hh _)
  discreteSteps := fun i hi =>
    T.end_trans_chain_before h τ (e.discreteSteps i hi) (T.end_start_before h τ e hh _)
  finalState := if e.boundary ⟨e.count,by omega⟩ < τ then e.finalState
    else e.finish ⟨e.count-1,by have := e.nonempty; omega⟩
  finalSteps := by
    split
    · rename_i he
      exact T.end_refl_chain_before h τ e.finalSteps ((T.end_final_time h τ e).trans_lt he)
    · exact .refl
  final_signal_eq := by
    intro t ht
    have he : e.boundary ⟨e.count,by omega⟩ < τ := ht ▸ (t.property.2.trans_eq hh)
    rw [if_pos he]
    exact e.final_signal_eq t ht
  signal_eq := e.signal_eq

theorem oldPrefix_early_final {σ : FiniteSignal T.TypedVar} (e : (New).Execution σ)
    (hh : σ.horizon = τ) (he : e.boundary ⟨e.count,by omega⟩ < τ) :
    (T.oldPrefix h τ e hh).finalState = e.finalState := if_pos he

theorem oldPrefix_horizon_final {σ : FiniteSignal T.TypedVar} (e : (New).Execution σ)
    (hh : σ.horizon = τ) (he : e.boundary ⟨e.count,by omega⟩ = τ) :
    (T.oldPrefix h τ e hh).finalState =
      e.finish ⟨e.count-1,by have := e.nonempty; omega⟩ := if_neg (not_lt_of_ge he.ge)

/-- The actual terminal tail at the horizon is empty or is a single
bookkeeping jump. This describes that tail, not its erasure or contraction. -/
theorem end_horizon_chain {a b : (New).State}
    (chain : Relation.ReflTransGen (New).DiscreteStep a b)
    (atHorizon : a.val.2 (.inl T.globalClock) = τ) :
    b = a ∨ (New).DiscreteStep a b ∧ T.EndGoal b.val.1 ∧ 0 < a.val.2 T.dwell := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp chain with eq | nonempty
  · exact Or.inl eq
  · obtain ⟨z,step,tail⟩ := Relation.TransGen.head'_iff.mp nonempty
    obtain ⟨goal,pos,no⟩ := T.horizon_step_last h τ step atHorizon
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp tail with eq | tail'
    · subst b
      exact Or.inr ⟨step,goal,pos⟩
    · obtain ⟨x,bad,_⟩ := Relation.TransGen.head'_iff.mp tail'
      exact (no x bad).elim

run_elab do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for n in #[``end_final_time,``end_trans_chain_before,``oldPrefix,
      ``oldPrefix_early_final,``oldPrefix_horizon_final,``end_horizon_chain] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do throwError "{n} uses unexpected axiom {ax}"
end STLTableau.Section4.Tableau
