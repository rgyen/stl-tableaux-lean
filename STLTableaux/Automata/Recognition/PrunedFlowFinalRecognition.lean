import STLTableaux.Automata.Recognition.PrunedSingletonRecognition
import STLTableaux.Automata.Recognition.PrunedExecutionEndpoint

/-! Acceptance in the last observed interval itself, including atomic final
states. No terminal frame or final jump is added. Actual observations supply
boundary monotonicity, final positive width and nonterminal labels. -/
namespace STLTableau.Section4.Finiteness
open Section3 IntervalPartition
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

theorem inputTableau_pruned_recognizes_final_observed_interval
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toPrunedAutomaton h
      σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : (inputTableau X root).ProjectsTo σ ρ)
    (n : ℕ) (b : Fin (n + 2) → ℝ) (hisolated : IsolatedSingletons b)
    (hstart : b ⟨0, by omega⟩ = 0) (hend : b ⟨n + 1, by omega⟩ = ρ.horizon)
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
    (hduration : ∀ i : Fin n, (d i.val : ℝ) =
      b ⟨i.val + 1, by omega⟩ - b ⟨i.val, by omega⟩)
    (hobs : ∀ i : Fin (n + 1),
      (inputTableau X root).pruneTerminal.ExecutionObservedPiece
        ((inputTableau X root).pruneTerminal_translationReady h)
        σ.horizon σ.horizon_pos e
        (entry i.val).val.1.val (b ⟨i.val, by omega⟩) (b ⟨i.val + 1, by omega⟩))
    (hm : ∀ (i : Fin (n + 1)) mark,
      Local.marker mark ∈ (inputTableau X root).label (entry i.val).val.1.val →
        singletonMarkers b ⟨i.val, by omega⟩ = mark) :
    ∃ P : IntervalPartition ρ.domain, P.size = n + 1 ∧
      (inputTableau (Clock := Clock) X root).pruneTerminal.recognizes
        JudgementTableau.labels_finite ρ P := by
  let T := inputTableau (Clock := Clock) X root
  let hpT := T.pruneTerminal_translationReady h
  have hb : Monotone b := Fin.monotone_iff_le_succ.mpr fun i =>
    (hobs i).left_le_right T.pruneTerminal hpT _ _ e
  have hlast : ∀ i : Fin (n + 1), i.val + 1 = n + 1 →
      b ⟨i.val, by omega⟩ ≠ b ⟨i.val + 1, by omega⟩ := by
    intro i hi he
    have hind : (⟨i.val + 1, by omega⟩ : Fin (n + 2)) = ⟨n + 1, by omega⟩ := Fin.ext hi
    rw [hind, hend, ← hp.1] at he
    exact (ne_of_lt ((hobs i).left_lt_horizon T.pruneTerminal hpT _ _ e)) he
  obtain ⟨incoming, v, hi, he, hg, hstep⟩ := Tableau.exists_dwell_schedule
    T.pruneTerminal hpT σ.horizon σ.horizon_pos n entry finish d hinit hd hj
  have hready : ∀ i ≤ n, (entry i).val.1.val.NormalizedReady := by
    intro i
    induction i with
    | zero => exact fun _ => inputTableau_initial_normalizedReady X root hi.1
    | succ i ih =>
      intro hin
      exact inputTableau_edge_normalizedReady X root (he i (by omega)).1 (ih (by omega))
  obtain ⟨P, hsize, _, hl, hwidth⟩ := execution_labels_hold_on_isolated_singleton_partition
    T.pruneTerminal hpT e hp b hb hisolated hlast hstart hend
    (fun i => (entry i.val).val.1.val) hobs
    (fun i l hl => (hready i.val (by have := i.isLt; omega)).1 l hl.1)
    (fun i => pruned_execution_observed_nonterminal X root h e (hobs i)) hm
  refine ⟨P, hsize, (T.pruneTerminal_recognizes_iff
    JudgementTableau.labels_finite ρ P).mpr ?_⟩
  apply finiteRootTableau_recognizes_of_real_coordinates X root.val n incoming
    (fun i => (entry i).val.1.val) (fun i _ => (entry i).val.1.property.1)
    (fun i hi => (he i hi).1) hi.1 hgoal.1 ρ P (by omega) v hg ?_ ?_
  · intro i hin c
    rw [hwidth ⟨i, by omega⟩, ← hduration ⟨i, hin⟩]
    exact hstep i hin c
  · intro i hin β
    exact hl ⟨i, by omega⟩ β

end STLTableau.Section4.Finiteness
