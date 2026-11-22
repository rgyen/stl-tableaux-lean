import STLTableaux.Automata.Recognition.SingletonRecognition
import STLTableaux.Semantics.Partitions.PointSuffixPartition

/-! Early acceptance with retained singleton frames. The final observed point
is followed by an unlabelled open suffix; no invariant is required there.
Selection of the dwell path and compatible markers remains explicit. -/
namespace STLTableau.Section4.Finiteness
open Section3 IntervalPartition
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

theorem inputTableau_recognizes_observed_dwells_early
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : (inputTableau X root).ProjectsTo σ ρ)
    (n : ℕ) (b : Fin (n + 1) → ℝ) (hb : Monotone b)
    (m : Fin (n + 1) → Marker) (hz : SingletonCompatible b m)
    (hfirst : m ⟨0, by omega⟩ = ●) (hlast : m ⟨n, by omega⟩ = ●)
    (hstart : b ⟨0, by omega⟩ = 0)
    (hstop : b ⟨n, by omega⟩ = e.boundary ⟨e.count, by omega⟩)
    (hearly : b ⟨n, by omega⟩ < ρ.horizon)
    (entry finish : ℕ →
      ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).State)
    (d : ℕ → NNReal)
    (hinit : (entry 0).val ∈
      ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).initial)
    (hd : ∀ i < n, (inputTableau X root).DwellStep h σ.horizon σ.horizon_pos
      (entry i) (finish i) (d i))
    (hj : ∀ i < n, ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).DiscreteStep
      (finish i) (entry (i + 1)))
    (hfinal : entry n = e.finalState)
    (hgoal : e.finalState.val.1.val ∈ (inputTableau X root).final)
    (hduration : ∀ i : Fin n, (d i.val : ℝ) = b ⟨i.val + 1, by omega⟩ - b ⟨i.val, by omega⟩)
    (hobs : ∀ i : Fin n,
      (inputTableau X root).ExecutionObservedPiece h σ.horizon σ.horizon_pos e
        (entry i.val).val.1.val (b ⟨i.val, by omega⟩) (b ⟨i.val + 1, by omega⟩))
    (hm : ∀ (i : Fin n) mark,
      Local.marker mark ∈ (inputTableau X root).label (entry i.val).val.1.val →
        m ⟨i.val, by omega⟩ = mark)
    (hright : ∀ i : Fin n, b ⟨i.val, by omega⟩ ≠ b ⟨i.val + 1, by omega⟩ →
      m ⟨i.val + 1, by omega⟩ = ●)
    (hfinalMarker : Local.marker ○ ∉ (inputTableau X root).label e.finalState.val.1.val) :
    ∃ P : IntervalPartition ρ.domain, ∃ hsize : P.size = n + 2,
      P.interval ⟨n, by omega⟩ =
        ⟨e.boundary ⟨e.count, by omega⟩, e.boundary ⟨e.count, by omega⟩, ●, ●⟩ ∧
      P.interval ⟨n + 1, by omega⟩ =
        ⟨e.boundary ⟨e.count, by omega⟩, ρ.horizon, ○, ○⟩ ∧
      (inputTableau (Clock := Clock) X root).recognizes
        JudgementTableau.labels_finite ρ P := by
  let T := inputTableau (Clock := Clock) X root
  have hninitial : (entry 0).val.1 ∉ T.terminalModes := by
    obtain ⟨l, hl, _⟩ := hinit
    exact finiteRootTableau_initial_nonterminal X root.val (l, (entry 0).val.1.val) hl
  have hn (i : ℕ) (hi : i < n) : Local.terminal ∉ T.label (entry i).val.1.val := by
    apply T.dwell_entry_nonterminal h _ _ n entry finish d hinit hninitial hd hj b
      hstart hduration i (by omega)
    have hlt := (singletonCompatible_boundary_lt_last b hb m hz hlast ⟨i, hi⟩).trans hearly
    rw [← hp.1] at hlt
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
  let Q := ofSingletonBoundaries b hb m hz hfirst hlast
  have hqsize : Q.size = n := rfl
  have hrightQ : ∀ i, (Q.interval i).right ≤ b ⟨n, by omega⟩ := by
    intro i
    exact hb (show (⟨i.val + 1, by omega⟩ : Fin (n + 1)) ≤
      ⟨n, by omega⟩ by change i.val + 1 ≤ n; have := i.isLt; omega)
  let R := Q.appendPointSuffix (hb (by simp)) hearly hrightQ
  let P : IntervalPartition ρ.domain :=
    { R with covers := by simpa only [hstart, FiniteSignal.domain] using R.covers }
  have hsize : P.size = n + 2 := rfl
  have hold (i : Fin n) : P.interval ⟨i.val, by rw [hsize]; omega⟩ =
      markedBoundaryPiece b m i := appendPointSuffix_old Q (hb (by simp)) hearly hrightQ i
  have hpoint : P.interval ⟨n, by rw [hsize]; omega⟩ =
      ⟨e.boundary ⟨e.count, by omega⟩, e.boundary ⟨e.count, by omega⟩, ●, ●⟩ := by
    change (Q.appendPointSuffix (hb (by simp)) hearly hrightQ).interval
      ⟨Q.size, by change Q.size < Q.size + 2; omega⟩ = _
    rw [appendPointSuffix_point, hstop]
  have hsuffix : P.interval ⟨n + 1, by rw [hsize]; omega⟩ =
      ⟨e.boundary ⟨e.count, by omega⟩, ρ.horizon, ○, ○⟩ := by
    change (Q.appendPointSuffix (hb (by simp)) hearly hrightQ).interval
      ⟨Q.size + 1, by change Q.size + 1 < Q.size + 2; omega⟩ = _
    rw [appendPointSuffix_suffix, hstop]
  refine ⟨P, hsize, hpoint, hsuffix, ?_⟩
  apply finiteRootTableau_recognizes_of_real_coordinates X root.val n incoming
    (fun i => (entry i).val.1.val) (fun i _ => (entry i).val.1.property) he hi
    (by rw [hfinal]; exact hgoal) ρ P (by omega) v hg ?_ ?_
  · intro i hin c
    have hwidth : (STLTableau.Judgement.duration P ⟨i, by omega⟩ : ℝ) = d i := by
      change (P.interval _).right - (P.interval _).left = _
      rw [hold ⟨i, hin⟩]
      exact (hduration ⟨i, hin⟩).symm
    rw [hwidth]
    exact hstep i hin c
  · intro i hin β
    by_cases hlt : i < n
    · apply (normalizedReady_labels_hold_iff T (entry i).val.1.val
        (fun l hl => (hready i hin).1 l hl.1) ρ P β ⟨i, by omega⟩
        (by change i < P.size; omega)).mpr
      refine ⟨hn i hlt, ?_, ?_⟩
      · intro mark hmark
        rw [hold ⟨i, hlt⟩]
        exact hm ⟨i, hlt⟩ mark hmark
      · intro a ha u hu
        rw [hold ⟨i, hlt⟩] at hu
        exact (hobs ⟨i, hlt⟩).raw_atom T h _ _ e hp b ⟨i, hlt⟩ a ha u
          (markedBoundaryPiece_subset_raw b m ⟨i, hlt⟩ (hright ⟨i, hlt⟩) hu)
    · have heq : i = n := by omega
      subst i
      rw [hfinal]
      apply (inputTableau_final_singleton_labels_iff X root h e hp
        (by rw [← hstop, hp.1]; exact hearly) P ⟨n, by omega⟩
        (by change n < P.size; omega) hpoint β).mpr
      exact hfinalMarker

end STLTableau.Section4.Finiteness
