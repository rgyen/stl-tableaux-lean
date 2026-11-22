import STLTableaux.Automata.Recognition.NormalizedInputFinalLabelSemantics
import STLTableaux.Automata.Recognition.IndexedRecognition
import STLTableaux.Automata.Recognition.NormalizedInputMarkerPartition

/-! Arbitrarily many positive flows with direct interflow and final jumps.
The chosen execution, not arbitrary zero-time blocks, supplies the path. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

/-- The shared clock/path construction for early and horizon termination.
The supplied partition must match actual flow durations and all labels. -/
theorem inputTableau_recognizes_direct_flows_on_partition
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var}
    (hgoal : e.finalState.val.1.val ∈ (inputTableau X root).final)
    (hinit : (e.start ⟨0, e.nonempty⟩).val ∈
      ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).initial)
    (hj : ∀ (i : Fin e.count) (hi : i.val + 1 < e.count),
      ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).DiscreteStep
        (e.finish i) (e.start ⟨i.val + 1, hi⟩))
    (hlast : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).DiscreteStep
      (e.finish ⟨e.count - 1, by have := e.nonempty; omega⟩) e.finalState)
    (P : IntervalPartition ρ.domain) (hlen : e.count ≤ P.size)
    (hflows : ∀ i : Fin e.count, ∀ β : ClockValuation Clock,
      ∀ l ∈ (inputTableau X root).label (e.start i).val.1.val,
        l.holds ρ P β ⟨i.val, by have := i.isLt; omega⟩)
    (hfinals : ∀ β : ClockValuation Clock,
      ∀ l ∈ (inputTableau X root).label e.finalState.val.1.val,
        l.holds ρ P β ⟨e.count, by omega⟩)
    (hd : ∀ i : Fin e.count,
      STLTableau.Judgement.duration P ⟨i.val, by have := i.isLt; omega⟩ = e.duration i) :
    (inputTableau (Clock := Clock) X root).recognizes JudgementTableau.labels_finite ρ P := by
  classical
  let T := inputTableau (Clock := Clock) X root
  let a := fun j : ℕ => if hj : j < e.count then e.start ⟨j, hj⟩ else e.finalState
  have ha (j : ℕ) (hj : j < e.count) : a j = e.start ⟨j, hj⟩ := dif_pos hj
  have haf : a e.count = e.finalState := dif_neg (by omega)
  have hjump (i : Fin e.count) :
      (T.toAutomaton h σ.horizon σ.horizon_pos).DiscreteStep (e.finish i) (a (i.val + 1)) := by
    by_cases hi : i.val + 1 < e.count
    · rw [ha _ hi]
      exact hj i hi
    · have heq : i.val + 1 = e.count := by omega
      rw [heq, haf]
      have hi' : i = ⟨e.count - 1, by have := e.nonempty; omega⟩ :=
        Fin.ext (by change i.val = e.count - 1; omega)
      rw [hi']
      exact hlast
  choose edge hedge hguard hreset hbound using
    fun i => (T.discreteStep_iff h σ.horizon σ.horizon_pos).mp (hjump i)
  obtain ⟨l₀, hi₀, v₀, hg₀, hr₀⟩ := hinit
  let incoming : ℕ → EdgeLabel Clock
    | 0 => l₀
    | j + 1 => if hj : j < e.count then edge ⟨j, hj⟩ else l₀
  let v : ℕ → T.HAVar → ℝ
    | 0 => v₀
    | j + 1 => if hj : j < e.count then (e.finish ⟨j, hj⟩).val.2 else v₀
  have hin (j : ℕ) (hj : j < e.count) : incoming (j + 1) = edge ⟨j, hj⟩ := dif_pos hj
  have hv (j : ℕ) (hj : j < e.count) : v (j + 1) = (e.finish ⟨j, hj⟩).val.2 := dif_pos hj
  have hentry (j : ℕ) (hj : j < e.count) (c : T.clocks) :
      (e.start ⟨j, hj⟩).val.2 (.inr (.inl c)) =
        T.reset (incoming j).resets (v j) (.inr (.inl c)) := by
    cases j with
    | zero => rw [hr₀]; rfl
    | succ j =>
      have hj' : j < e.count := by omega
      have heq := hreset ⟨j, hj'⟩
      rw [ha _ hj] at heq
      rw [heq, hin j hj', hv j hj']
  apply finiteRootTableau_recognizes_of_real_coordinates X root.val e.count
    incoming (fun j => (a j).val.1.val) ?_ ?_ ?_ ?_ ρ P hlen v ?_ ?_ ?_
  · intro j _
    exact (a j).val.1.property
  · intro j hj
    rw [ha j hj, hin j hj]
    have hm := congrArg Subtype.val (e.continuousStep ⟨j, hj⟩).1
    rw [hm]
    exact hedge ⟨j, hj⟩
  · rw [ha 0 e.nonempty]
    exact hi₀
  · rw [haf]
    exact hgoal
  · intro j hj
    cases j with
    | zero => exact hg₀
    | succ j =>
      have hj' : j < e.count := by omega
      rw [hin j hj', hv j hj']
      exact hguard ⟨j, hj'⟩
  · intro j hj c
    rw [hv j hj, hd ⟨j, hj⟩]
    have hf := ((e.continuousStep ⟨j, hj⟩).2.2.2 ⟨e.duration ⟨j, hj⟩, by simp⟩).1.1 c
    rw [(e.continuousStep ⟨j, hj⟩).2.2.1, hentry j hj c] at hf
    exact hf
  · intro j hj β
    by_cases hj' : j < e.count
    · rw [ha j hj']
      exact hflows ⟨j, hj'⟩ β
    · have heq : j = e.count := by omega
      subst j
      rw [haf]
      exact hfinals β

/-- Early-stop specialization: append the observed final singleton and an
unlabelled suffix, preserving all positive flow durations. -/
theorem inputTableau_recognizes_direct_flows
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : (inputTableau X root).ProjectsTo σ ρ)
    (hearly : e.boundary ⟨e.count, by omega⟩ < σ.horizon)
    (hgoal : e.finalState.val.1.val ∈ (inputTableau X root).final)
    (hinit : (e.start ⟨0, e.nonempty⟩).val ∈
      ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).initial)
    (hj : ∀ (i : Fin e.count) (hi : i.val + 1 < e.count),
      ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).DiscreteStep
        (e.finish i) (e.start ⟨i.val + 1, hi⟩))
    (hlast : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).DiscreteStep
      (e.finish ⟨e.count - 1, by have := e.nonempty; omega⟩) e.finalState)
    (hfirst : Local.marker ○ ∉
      (inputTableau X root).label (e.start ⟨0, e.nonempty⟩).val.1.val)
    (hconsistent : ∀ i : Fin e.count, ¬ (
      Local.marker ○ ∈ (inputTableau X root).label (e.start i).val.1.val ∧
      Local.marker ● ∈ (inputTableau X root).label (e.start i).val.1.val))
    (hfinal : Local.marker ○ ∉ (inputTableau X root).label e.finalState.val.1.val) :
    ∃ P : IntervalPartition ρ.domain,
      (inputTableau (Clock := Clock) X root).recognizes JudgementTableau.labels_finite ρ P := by
  obtain ⟨P, hsize, hflows, hfinals, hd⟩ :=
    inputTableau_exists_flow_and_final_partition X root h e hp hearly hfirst hconsistent hfinal
  exact ⟨P, inputTableau_recognizes_direct_flows_on_partition X root h e
    hgoal hinit hj hlast P (by omega) hflows hfinals hd⟩

omit [DecidableEq Clock] [Infinite Clock] in
/-- At the terminal position, exactly `*` and the closed marker can hold.
In particular even a `true` predicate cannot label that position. -/
theorem local_holds_terminal_iff (ρ : FiniteSignal Var) (P : IntervalPartition ρ.domain)
    (β : ClockValuation Clock) (l : Local Clock Var) :
    l.holds ρ P β ⟨P.size, by omega⟩ ↔ l = .terminal ∨ l = .marker ● := by
  cases l with
  | terminal => simp [Local.holds, Local.toJudgement, Section3.Judgement.holds]
  | marker m =>
    simp [Local.holds, Local.toJudgement, Section3.Judgement.holds]
  | predicate p => simp [Local.holds, Local.toJudgement, Section3.Judgement.holds]

/-- Horizon-stop specialization. Final-label compatibility is explicit and
is not inferred merely from membership in terminal modes. No singleton at
the excluded horizon and no suffix is inserted. -/
theorem inputTableau_recognizes_direct_flows_at_horizon
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : (inputTableau X root).ProjectsTo σ ρ)
    (hexhaust : e.boundary ⟨e.count, by omega⟩ = σ.horizon)
    (hgoal : e.finalState.val.1.val ∈ (inputTableau X root).final)
    (hinit : (e.start ⟨0, e.nonempty⟩).val ∈
      ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).initial)
    (hj : ∀ (i : Fin e.count) (hi : i.val + 1 < e.count),
      ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).DiscreteStep
        (e.finish i) (e.start ⟨i.val + 1, hi⟩))
    (hlast : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).DiscreteStep
      (e.finish ⟨e.count - 1, by have := e.nonempty; omega⟩) e.finalState)
    (hfirst : Local.marker ○ ∉
      (inputTableau X root).label (e.start ⟨0, e.nonempty⟩).val.1.val)
    (hconsistent : ∀ i : Fin e.count, ¬ (
      Local.marker ○ ∈ (inputTableau X root).label (e.start i).val.1.val ∧
      Local.marker ● ∈ (inputTableau X root).label (e.start i).val.1.val))
    (hfinal : ∀ l ∈ (inputTableau X root).label e.finalState.val.1.val,
      l = .terminal ∨ l = .marker ●) :
    ∃ P : IntervalPartition ρ.domain, P.size = e.count ∧
      (inputTableau (Clock := Clock) X root).recognizes JudgementTableau.labels_finite ρ P := by
  obtain ⟨P, hsize, hflows, hd⟩ := inputTableau_exists_flow_label_partition_with_duration
    X root h e hp hexhaust hfirst hconsistent
  refine ⟨P, hsize, inputTableau_recognizes_direct_flows_on_partition X root h e
    hgoal hinit hj hlast P (by omega) hflows ?_ hd⟩
  intro β l hl
  have hk : (⟨e.count, by omega⟩ : STLTableau.Judgement.Position P) =
      ⟨P.size, by omega⟩ := Fin.ext hsize.symm
  rw [hk]
  exact (local_holds_terminal_iff ρ P β l).mpr (hfinal l hl)

end STLTableau.Section4.Finiteness
