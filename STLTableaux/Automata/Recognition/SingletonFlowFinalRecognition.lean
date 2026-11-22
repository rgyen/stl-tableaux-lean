import STLTableaux.Automata.Recognition.SingletonRecognition

/-! Horizon acceptance in the final positive/observed interval itself.
Unlike the terminal-tail theorem, the accepting final frame may contain atoms.
No terminal frame or final jump is manufactured. -/
namespace STLTableau.Section4.Finiteness
open Section3 IntervalPartition
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

theorem inputTableau_recognizes_final_observed_interval
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : (inputTableau X root).ProjectsTo σ ρ)
    (n : ℕ) (b : Fin (n + 2) → ℝ) (hb : Monotone b)
    (m : Fin (n + 2) → Marker) (hz : SingletonCompatible b m)
    (hfirst : m ⟨0, by omega⟩ = ●) (hlast : m ⟨n + 1, by omega⟩ = ●)
    (hstart : b ⟨0, by omega⟩ = 0) (hend : b ⟨n + 1, by omega⟩ = ρ.horizon)
    (entry finish : ℕ →
      ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).State)
    (d : ℕ → NNReal)
    (hinit : (entry 0).val ∈
      ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).initial)
    (hd : ∀ i < n, (inputTableau X root).DwellStep h σ.horizon σ.horizon_pos
      (entry i) (finish i) (d i))
    (hj : ∀ i < n, ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).DiscreteStep
      (finish i) (entry (i + 1)))
    (hgoal : (entry n).val.1.val ∈ (inputTableau X root).final)
    (hduration : ∀ i : Fin n, (d i.val : ℝ) =
      b ⟨i.val + 1, by omega⟩ - b ⟨i.val, by omega⟩)
    (hobs : ∀ i : Fin (n + 1),
      (inputTableau X root).ExecutionObservedPiece h σ.horizon σ.horizon_pos e
        (entry i.val).val.1.val (b ⟨i.val, by omega⟩) (b ⟨i.val + 1, by omega⟩))
    (hm : ∀ (i : Fin (n + 1)) mark,
      Local.marker mark ∈ (inputTableau X root).label (entry i.val).val.1.val →
        m ⟨i.val, by omega⟩ = mark)
    (hright : ∀ i : Fin (n + 1), b ⟨i.val, by omega⟩ ≠ b ⟨i.val + 1, by omega⟩ →
      m ⟨i.val + 1, by omega⟩ = ●) :
    ∃ P : IntervalPartition ρ.domain, P.size = n + 1 ∧
      (inputTableau (Clock := Clock) X root).recognizes
        JudgementTableau.labels_finite ρ P := by
  let T := inputTableau (Clock := Clock) X root
  let bpre : Fin (n + 1) → ℝ := fun i => b i.castSucc
  have hpre : ∀ i : Fin n, (d i.val : ℝ) =
      bpre ⟨i.val + 1, by omega⟩ - bpre ⟨i.val, by omega⟩ := hduration
  have hninitial : (entry 0).val.1 ∉ T.terminalModes := by
    obtain ⟨l, hl, _⟩ := hinit
    exact finiteRootTableau_initial_nonterminal X root.val (l, (entry 0).val.1.val) hl
  have hn (i : Fin (n + 1)) : Local.terminal ∉ T.label (entry i.val).val.1.val := by
    apply T.dwell_entry_nonterminal h _ _ n entry finish d hinit hninitial hd hj
      bpre hstart hpre i.val (by have := i.isLt; omega)
    have hlt := singletonCompatible_boundary_lt_last b hb m hz hlast i
    rw [hend, ← hp.1] at hlt
    exact hlt
  obtain ⟨incoming, v, hi, he, hg, hstep⟩ :=
    Tableau.exists_dwell_schedule T h σ.horizon σ.horizon_pos
      n entry finish d hinit hd hj
  have hready : ∀ i ≤ n, (entry i).val.1.val.NormalizedReady := by
    intro i
    induction i with
    | zero => exact fun _ => inputTableau_initial_normalizedReady X root hi
    | succ i ih =>
      intro hin
      exact inputTableau_edge_normalizedReady X root (he i (by omega)) (ih (by omega))
  obtain ⟨P, hsize, _, hl, hwidth⟩ := execution_labels_hold_on_singleton_partition
    T h e hp b hb m hz hfirst hlast hstart hend (fun i => (entry i.val).val.1.val)
    hobs (fun i l hl => (hready i.val (by have := i.isLt; omega)).1 l hl.1)
    hn hm hright
  refine ⟨P, hsize, ?_⟩
  apply finiteRootTableau_recognizes_of_real_coordinates X root.val n incoming
    (fun i => (entry i).val.1.val) (fun i _ => (entry i).val.1.property) he hi
    hgoal ρ P (by omega) v hg ?_ ?_
  · intro i hin c
    rw [hwidth ⟨i, by omega⟩, ← hduration ⟨i, hin⟩]
    exact hstep i hin c
  · intro i hin β
    exact hl ⟨i, by omega⟩ β

end STLTableau.Section4.Finiteness
