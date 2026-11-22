import STLTableaux.Automata.Recognition.SingletonLabelPartition
import STLTableaux.Automata.Recognition.DirectFlowRecognition
import STLTableaux.Automata.Recognition.TableauDwellSchedule

/-! Recognition for an execution-observed singleton/flow path at the horizon.
This assembles one supplied graph path, observations and real clock equations;
it does not assert that an arbitrary accepting execution supplies such a path.
Intermediate singleton frames are retained, not bypassed by shortcut edges. -/
namespace STLTableau.Section4.Finiteness
open Section3 IntervalPartition
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

theorem inputTableau_recognizes_singleton_path_at_horizon
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : (inputTableau X root).ProjectsTo σ ρ)
    (n : ℕ) (b : Fin (n + 1) → ℝ) (hb : Monotone b)
    (m : Fin (n + 1) → Marker) (hz : SingletonCompatible b m)
    (hfirst : m ⟨0, by omega⟩ = ●) (hlast : m ⟨n, by omega⟩ = ●)
    (hstart : b ⟨0, by omega⟩ = 0) (hend : b ⟨n, by omega⟩ = ρ.horizon)
    (incoming : ℕ → EdgeLabel Clock) (states : ℕ → Section3.TransitionForm Clock Var)
    (hs : ∀ i ≤ n, states i ∈ (inputTableau X root).states)
    (he : ∀ i < n,
      (states i, incoming (i + 1), states (i + 1)) ∈ (inputTableau X root).edges)
    (hi : (incoming 0, states 0) ∈ (inputTableau X root).initial)
    (hf : states n ∈ (inputTableau X root).final)
    (hobs : ∀ i : Fin n,
      (inputTableau X root).ExecutionObservedPiece h σ.horizon σ.horizon_pos e
        (states i.val) (b ⟨i.val, by omega⟩) (b ⟨i.val + 1, by omega⟩))
    (hn : ∀ i < n, Local.terminal ∉ (inputTableau X root).label (states i))
    (hm : ∀ (i : Fin n) mark,
      Local.marker mark ∈ (inputTableau X root).label (states i.val) →
        m ⟨i.val, by omega⟩ = mark)
    (hright : ∀ i : Fin n, b ⟨i.val, by omega⟩ ≠ b ⟨i.val + 1, by omega⟩ →
      m ⟨i.val + 1, by omega⟩ = ●)
    (hterminal : ∀ l ∈ (inputTableau X root).label (states n),
      l = .terminal ∨ l = .marker ●)
    (v : ℕ → (inputTableau (Clock := Clock) X root).HAVar → ℝ)
    (hg : ∀ i ≤ n, (inputTableau X root).guardsHold (incoming i) (v i))
    (hstep : ∀ (i : ℕ) (hi : i < n), ∀ c : (inputTableau (Clock := Clock) X root).clocks,
      v (i + 1) (.inr (.inl c)) =
        (inputTableau X root).reset (incoming i).resets (v i) (.inr (.inl c)) +
          (b ⟨i + 1, by omega⟩ - b ⟨i, by omega⟩)) :
    ∃ P : IntervalPartition ρ.domain, P.size = n ∧
      (inputTableau (Clock := Clock) X root).recognizes JudgementTableau.labels_finite ρ P := by
  have hready : ∀ i ≤ n, (states i).NormalizedReady := by
    intro i
    induction i with
    | zero => exact fun _ => inputTableau_initial_normalizedReady X root hi
    | succ i ih =>
      intro hin
      exact inputTableau_edge_normalizedReady X root (he i (by omega)) (ih (by omega))
  obtain ⟨P, hsize, _, hl, hd⟩ := execution_labels_hold_on_singleton_partition
    (inputTableau X root) h e hp b hb m hz hfirst hlast hstart hend
    (fun i => states i.val) hobs
    (fun i l hl => (hready i.val (by have := i.isLt; omega)).1 l hl.1)
    (fun i => hn i.val i.isLt) hm hright
  refine ⟨P, hsize, ?_⟩
  apply finiteRootTableau_recognizes_of_real_coordinates X root.val n incoming states
    hs he hi hf ρ P (by omega) v hg ?_ ?_
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
      exact (local_holds_terminal_iff ρ P β l).mpr (hterminal l hlabel)

/-- Actual selected dwell states and jumps discharge the guard/reset premises
of the preceding theorem. Singleton observations have zero dwell and are
retained as frames. Selection and terminal-label compatibility remain explicit. -/
theorem inputTableau_recognizes_observed_dwells_at_horizon
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : (inputTableau X root).ProjectsTo σ ρ)
    (n : ℕ) (b : Fin (n + 1) → ℝ) (hb : Monotone b)
    (m : Fin (n + 1) → Marker) (hz : SingletonCompatible b m)
    (hfirst : m ⟨0, by omega⟩ = ●) (hlast : m ⟨n, by omega⟩ = ●)
    (hstart : b ⟨0, by omega⟩ = 0) (hend : b ⟨n, by omega⟩ = ρ.horizon)
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
    (hduration : ∀ i : Fin n, (d i.val : ℝ) = b ⟨i.val + 1, by omega⟩ - b ⟨i.val, by omega⟩)
    (hobs : ∀ i : Fin n,
      (inputTableau X root).ExecutionObservedPiece h σ.horizon σ.horizon_pos e
        (entry i.val).val.1.val (b ⟨i.val, by omega⟩) (b ⟨i.val + 1, by omega⟩))
    (hm : ∀ (i : Fin n) mark,
      Local.marker mark ∈ (inputTableau X root).label (entry i.val).val.1.val →
        m ⟨i.val, by omega⟩ = mark)
    (hright : ∀ i : Fin n, b ⟨i.val, by omega⟩ ≠ b ⟨i.val + 1, by omega⟩ →
      m ⟨i.val + 1, by omega⟩ = ●)
    (hterminal : ∀ l ∈ (inputTableau X root).label (entry n).val.1.val,
      l = .terminal ∨ l = .marker ●) :
    ∃ P : IntervalPartition ρ.domain, P.size = n ∧
      (inputTableau (Clock := Clock) X root).recognizes JudgementTableau.labels_finite ρ P := by
  have hninitial : (entry 0).val.1 ∉ (inputTableau X root).terminalModes := by
    obtain ⟨l, hl, _⟩ := hinit
    exact finiteRootTableau_initial_nonterminal X root.val (l, (entry 0).val.1.val) hl
  have hn (i : ℕ) (hi : i < n) :
      Local.terminal ∉ (inputTableau X root).label (entry i).val.1.val := by
    apply Tableau.dwell_entry_nonterminal (inputTableau X root) h _ _ n entry finish d
      hinit hninitial hd hj b hstart hduration i (by omega)
    have hlt := singletonCompatible_boundary_lt_last b hb m hz hlast ⟨i, hi⟩
    rw [hend, ← hp.1] at hlt
    exact hlt
  obtain ⟨incoming, v, hi, he, hg, hstep⟩ :=
    Tableau.exists_dwell_schedule (inputTableau X root) h σ.horizon σ.horizon_pos
      n entry finish d hinit hd hj
  apply inputTableau_recognizes_singleton_path_at_horizon X root h e hp n b hb m hz
    hfirst hlast hstart hend incoming (fun i => (entry i).val.1.val)
    (fun i _ => (entry i).val.1.property) he hi hgoal hobs hn hm hright hterminal v hg
  intro i hi c
  rw [← hduration ⟨i, hi⟩]
  exact hstep i hi c

end STLTableau.Section4.Finiteness
