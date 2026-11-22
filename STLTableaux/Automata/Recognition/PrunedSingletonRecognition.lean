import STLTableaux.Automata.Recognition.SingletonRecognition
import STLTableaux.Automata.Execution.TerminalPruning
import STLTableaux.Automata.Recognition.PrunedDwellGeometry

/-! Horizon recognition for the pruned translation. Terminal compatibility and
nonterminal intermediate labels follow from graph membership, not assumptions.
The observed path, boundaries and marker alignment still have to be supplied. -/
namespace STLTableau.Section4.Finiteness
open Section3 IntervalPartition
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

theorem inputTableau_pruned_recognizes_singleton_path_at_horizon
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toPrunedAutomaton h
      σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : (inputTableau X root).ProjectsTo σ ρ)
    (n : ℕ) (b : Fin (n + 1) → ℝ) (hb : Monotone b)
    (m : Fin (n + 1) → Marker) (hz : SingletonCompatible b m)
    (hfirst : m ⟨0, by omega⟩ = ●) (hlast : m ⟨n, by omega⟩ = ●)
    (hstart : b ⟨0, by omega⟩ = 0) (hend : b ⟨n, by omega⟩ = ρ.horizon)
    (incoming : ℕ → EdgeLabel Clock) (states : ℕ → Section3.TransitionForm Clock Var)
    (hs : ∀ i ≤ n, states i ∈ (inputTableau X root).pruneTerminal.states)
    (he : ∀ i < n, (states i, incoming (i + 1), states (i + 1)) ∈
      (inputTableau X root).pruneTerminal.edges)
    (hi : (incoming 0, states 0) ∈ (inputTableau X root).pruneTerminal.initial)
    (hf : states n ∈ (inputTableau X root).pruneTerminal.final)
    (hobs : ∀ i : Fin n,
      (inputTableau X root).pruneTerminal.ExecutionObservedPiece
        ((inputTableau X root).pruneTerminal_translationReady h)
        σ.horizon σ.horizon_pos e
        (states i.val) (b ⟨i.val, by omega⟩) (b ⟨i.val + 1, by omega⟩))
    (hm : ∀ (i : Fin n) mark,
      Local.marker mark ∈ (inputTableau X root).label (states i.val) →
        m ⟨i.val, by omega⟩ = mark)
    (ht : Local.terminal ∈ (inputTableau X root).label (states n))
    (v : ℕ → (inputTableau (Clock := Clock) X root).HAVar → ℝ)
    (hg : ∀ i ≤ n, (inputTableau X root).guardsHold (incoming i) (v i))
    (hstep : ∀ (i : ℕ) (hi : i < n), ∀ c : (inputTableau (Clock := Clock) X root).clocks,
      v (i + 1) (.inr (.inl c)) =
        (inputTableau X root).reset (incoming i).resets (v i) (.inr (.inl c)) +
          (b ⟨i + 1, by omega⟩ - b ⟨i, by omega⟩)) :
    ∃ P : IntervalPartition ρ.domain, P.size = n ∧
      (inputTableau (Clock := Clock) X root).pruneTerminal.recognizes
        JudgementTableau.labels_finite ρ P := by
  have hready : ∀ i ≤ n, (states i).NormalizedReady := by
    intro i
    induction i with
    | zero => exact fun _ => inputTableau_initial_normalizedReady X root hi.1
    | succ i ih =>
      intro hin
      exact inputTableau_edge_normalizedReady X root (he i (by omega)).1 (ih (by omega))
  obtain ⟨P, hsize, _, hl, hd⟩ := execution_labels_hold_on_marked_partition
    (inputTableau X root).pruneTerminal
    ((inputTableau X root).pruneTerminal_translationReady h) e hp b hb m hz
    hfirst hlast hstart hend (fun i => states i.val) hobs
    (fun i l hl => (hready i.val (by have := i.isLt; omega)).1 l hl.1)
    (fun i => (he i.val i.isLt).2.2.2) hm
  refine ⟨P, hsize, ((inputTableau X root).pruneTerminal_recognizes_iff
    JudgementTableau.labels_finite ρ P).mpr ?_⟩
  apply finiteRootTableau_recognizes_of_real_coordinates X root.val n incoming states
    (fun i hi => (hs i hi).1) (fun i hi => (he i hi).1) hi.1 hf.1 ρ P
    (by omega) v hg ?_ ?_
  · intro i hin c
    rw [hd ⟨i, hin⟩]
    exact hstep i hin c
  · intro i hin β l hlabel
    by_cases hlt : i < n
    · exact hl ⟨i, hlt⟩ β l hlabel
    · have heq : i = n := by omega
      subst i
      have hpos : (⟨n, by omega⟩ : STLTableau.Judgement.Position P) =
          ⟨P.size, by omega⟩ := Fin.ext hsize.symm
      rw [hpos]
      exact (local_holds_terminal_iff ρ P β l).mpr ((hs n le_rfl).2 ht l hlabel)

/-- Actual pruned dwells/jumps supply all incoming guards and clock updates.
Only the choice of observed pieces and their geometric marker alignment remain. -/
theorem inputTableau_pruned_recognizes_observed_dwells_at_horizon
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toPrunedAutomaton h
      σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : (inputTableau X root).ProjectsTo σ ρ)
    (n : ℕ) (b : Fin (n + 1) → ℝ) (hisolated : IsolatedSingletons b)
    (hstart : b ⟨0, by omega⟩ = 0) (hend : b ⟨n, by omega⟩ = ρ.horizon)
    (entry finish : ℕ →
      ((inputTableau X root).toPrunedAutomaton h σ.horizon σ.horizon_pos).State)
    (d : ℕ → NNReal)
    (hinit : (entry 0).val ∈
      ((inputTableau X root).toPrunedAutomaton h σ.horizon σ.horizon_pos).initial)
    (hd : ∀ i < n, (inputTableau X root).pruneTerminal.DwellStep
      ((inputTableau X root).pruneTerminal_translationReady h)
      σ.horizon σ.horizon_pos (entry i) (finish i) (d i))
    (hj : ∀ i < n,
      ((inputTableau X root).toPrunedAutomaton h σ.horizon σ.horizon_pos).DiscreteStep
        (finish i) (entry (i + 1)))
    (hgoal : (entry n).val.1.val ∈ (inputTableau X root).pruneTerminal.final)
    (hduration : ∀ i : Fin n, (d i.val : ℝ) = b ⟨i.val + 1, by omega⟩ - b ⟨i.val, by omega⟩)
    (hobs : ∀ i : Fin n,
      (inputTableau X root).pruneTerminal.ExecutionObservedPiece
        ((inputTableau X root).pruneTerminal_translationReady h)
        σ.horizon σ.horizon_pos e
        (entry i.val).val.1.val (b ⟨i.val, by omega⟩) (b ⟨i.val + 1, by omega⟩))
    (hm : ∀ (i : Fin n) mark,
      Local.marker mark ∈ (inputTableau X root).label (entry i.val).val.1.val →
        singletonMarkers b ⟨i.val, by omega⟩ = mark) :
    ∃ P : IntervalPartition ρ.domain, P.size = n ∧
      (inputTableau (Clock := Clock) X root).pruneTerminal.recognizes
        JudgementTableau.labels_finite ρ P := by
  have hb := Tableau.dwell_boundaries_monotone b d hduration
  have hbefore := Tableau.pruned_dwell_boundaries_lt_horizon (inputTableau X root) h
    σ.horizon σ.horizon_pos n entry finish d hinit hd hj b hstart hduration
  have hlast : ∀ i : Fin n, i.val + 1 = n →
      b ⟨i.val, by omega⟩ ≠ b ⟨i.val + 1, by omega⟩ := by
    intro i hi he
    have hind : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := Fin.ext hi
    rw [hind, hend, ← hp.1] at he
    exact (ne_of_lt (hbefore i)) he
  have ht : Local.terminal ∈ (inputTableau X root).label (entry n).val.1.val := by
    have hn : 0 < n := by
      by_contra hnon
      have heq : n = 0 := by omega
      subst n
      have hz : ρ.horizon = 0 := hend.symm.trans hstart
      have := ρ.horizon_pos
      linarith
    have hclock := Tableau.dwell_entry_globalClock (inputTableau X root).pruneTerminal
      ((inputTableau X root).pruneTerminal_translationReady h)
      σ.horizon σ.horizon_pos n entry finish d hinit hd hj b hstart hduration n le_rfl
    rw [hend, ← hp.1] at hclock
    by_contra hnot
    have hjlast := hj (n - 1) (by omega)
    have heq : n - 1 + 1 = n := by omega
    rw [heq] at hjlast
    have hlt := (inputTableau X root).pruneTerminal.nonterminal_entry_lt_horizon
      ((inputTableau X root).pruneTerminal_translationReady h)
      σ.horizon σ.horizon_pos hjlast hnot
    rw [hclock] at hlt
    exact (lt_irrefl _ hlt)
  obtain ⟨incoming, v, hi, he, hg, hstep⟩ :=
    Tableau.exists_dwell_schedule (inputTableau X root).pruneTerminal
      ((inputTableau X root).pruneTerminal_translationReady h)
      σ.horizon σ.horizon_pos n entry finish d hinit hd hj
  apply inputTableau_pruned_recognizes_singleton_path_at_horizon X root h e hp
    n b hb (singletonMarkers b) (singletonMarkers_compatible b hisolated)
    (singletonMarkers_first b) (singletonMarkers_last b hlast)
    hstart hend incoming (fun i => (entry i).val.1.val)
    (fun i _ => (entry i).val.1.property) he hi hgoal hobs hm ht v hg
  intro i hi c
  rw [← hduration ⟨i, hi⟩]
  exact hstep i hi c

end STLTableau.Section4.Finiteness
