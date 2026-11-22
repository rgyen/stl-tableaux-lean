import STLTableaux.Finiteness.Correctness.RootTraceClockIndependence
import STLTableaux.Automata.Recognition.IndexedPath
import STLTableaux.Automata.Recognition.TableauRealClockSchedule

/-! Recognition from one indexed sequence. All graph, label and clock
premises refer to that same sequence; no representative-selection claim. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

/-- Assemble graph validity, real guard checks and local-label validity into
recognition. The last frame may be terminal. The real initial clocks can be
negative: closure of the actual root run supplies independence from them. -/
theorem finiteRootTableau_indexed_trace_holds
    (X : Set Var) (root : Formula Var) (n : ℕ)
    (incoming : Fin (n + 1) → EdgeLabel Clock)
    (states : Fin (n + 1) → Section3.TransitionForm Clock Var)
    (hs : ∀ i, states i ∈ (finiteRootTableau X root).states)
    (he : ∀ i : Fin n,
      (states i.castSucc, incoming i.succ, states i.succ) ∈ (finiteRootTableau X root).edges)
    (hi : (incoming 0, states 0) ∈ (finiteRootTableau X root).initial)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (hlen : n ≤ P.size)
    (ν : ℕ → Clock → ℝ)
    (hg : ∀ i : Fin (n + 1), ∀ g ∈ (incoming i).guards,
      Tableau.realComparison g.relation (ν i.val g.clock) g.bound)
    (hn : ∀ i : Fin n, ν (i.val + 1) = fun c =>
      Trace.realReset (incoming i.castSucc).resets (ν i.val) c +
        STLTableau.Judgement.duration P ⟨i.val, by have := i.isLt; omega⟩)
    (hl : ∀ (i : Fin (n + 1)) (β : ClockValuation Clock),
      ∀ l ∈ JudgementTableau.labels (states i),
        l.holds σ P β ⟨i.val, by have := i.isLt; omega⟩) :
    ∀ α, ((Path.ofIndexed n incoming states).trace
      JudgementTableau.labels JudgementTableau.labels_finite).holds σ P α ⟨0, by omega⟩ := by
  let p := Path.ofIndexed n incoming states
  let t := p.trace JudgementTableau.labels JudgementTableau.labels_finite
  have ht : t.length = n + 1 := Path.ofIndexed_trace_length _ _ _ _ _
  have ht' : (p.trace JudgementTableau.labels JudgementTableau.labels_finite).length =
      n + 1 := ht
  have hframe (j : Fin t.length) : t.frameAt j =
      ⟨(incoming ⟨j.val, by omega⟩).guards,
        (incoming ⟨j.val, by omega⟩).guards_finite,
        (incoming ⟨j.val, by omega⟩).resets,
        JudgementTableau.labels (states ⟨j.val, by omega⟩),
        JudgementTableau.labels_finite (states ⟨j.val, by omega⟩)⟩ :=
    Path.ofIndexed_trace_frameAt _ _ n incoming states ⟨j.val, by omega⟩
  apply finiteRootTableau_given_trace_holds_of_realGuards X root p
    (Path.ofIndexed_run _ _ _ _ hs he hi)
    σ P (ν 0) (by omega)
  · apply Trace.realGuardsHold_of_schedule σ P t ν ⟨0, by omega⟩
      (by change 0 + t.length ≤ P.size + 1; omega)
    · intro j
      simpa only [hframe] using hg ⟨j.val, by omega⟩
    · intro j hj
      rw [hframe]
      convert hn ⟨j.val, by omega⟩ using 1
      simp
  · intro j β
    change ∀ l ∈ (t.frameAt j).locals, _
    rw [hframe]
    exact hl ⟨j.val, by omega⟩ β

/-- The witness is the unchanged indexed path. -/
theorem finiteRootTableau_recognizes_of_indexed_schedule
    (X : Set Var) (root : Formula Var) (n : ℕ)
    (incoming : Fin (n + 1) → EdgeLabel Clock)
    (states : Fin (n + 1) → Section3.TransitionForm Clock Var)
    (hs : ∀ i, states i ∈ (finiteRootTableau X root).states)
    (he : ∀ i : Fin n,
      (states i.castSucc, incoming i.succ, states i.succ) ∈ (finiteRootTableau X root).edges)
    (hi : (incoming 0, states 0) ∈ (finiteRootTableau X root).initial)
    (hf : states (Fin.last n) ∈ (finiteRootTableau X root).final)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (hlen : n ≤ P.size)
    (ν : ℕ → Clock → ℝ)
    (hg : ∀ i : Fin (n + 1), ∀ g ∈ (incoming i).guards,
      Tableau.realComparison g.relation (ν i.val g.clock) g.bound)
    (hn : ∀ i : Fin n, ν (i.val + 1) = fun c =>
      Trace.realReset (incoming i.castSucc).resets (ν i.val) c +
        STLTableau.Judgement.duration P ⟨i.val, by have := i.isLt; omega⟩)
    (hl : ∀ (i : Fin (n + 1)) (β : ClockValuation Clock),
      ∀ l ∈ JudgementTableau.labels (states i),
        l.holds σ P β ⟨i.val, by have := i.isLt; omega⟩) :
    (finiteRootTableau (Clock := Clock) X root).recognizes JudgementTableau.labels_finite σ P := by
  exact ⟨Path.ofIndexed n incoming states,
    Path.ofIndexed_run _ _ _ _ hs he hi,
    Path.ofIndexed_accepting _ _ _ _ hs he hf,
    finiteRootTableau_indexed_trace_holds X root n incoming states hs he hi
      σ P hlen ν hg hn hl⟩

/-- Use actual automaton coordinates instead of assuming a full clock
schedule. Only declared-coordinate reset/flow equations are needed; values
of undeclared clocks are extended consistently by recursion. -/
theorem finiteRootTableau_given_trace_holds_of_real_coordinates
    (X : Set Var) (root : Formula Var) (n : ℕ)
    (incoming : ℕ → EdgeLabel Clock) (states : ℕ → Section3.TransitionForm Clock Var)
    (hs : ∀ i ≤ n, states i ∈ (finiteRootTableau X root).states)
    (he : ∀ i < n,
      (states i, incoming (i + 1), states (i + 1)) ∈ (finiteRootTableau X root).edges)
    (hi : (incoming 0, states 0) ∈ (finiteRootTableau X root).initial)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (hlen : n ≤ P.size)
    (v : ℕ → (finiteRootTableau (Clock := Clock) X root).HAVar → ℝ)
    (hg : ∀ i ≤ n, (finiteRootTableau X root).guardsHold (incoming i) (v i))
    (hstep : ∀ (i : ℕ) (hi : i < n), ∀ c : (finiteRootTableau (Clock := Clock) X root).clocks,
      v (i + 1) (.inr (.inl c)) =
        (finiteRootTableau X root).reset (incoming i).resets (v i) (.inr (.inl c)) +
          STLTableau.Judgement.duration P ⟨i, by omega⟩)
    (hl : ∀ (i : ℕ) (hi : i ≤ n) (β : ClockValuation Clock),
      ∀ l ∈ JudgementTableau.labels (states i),
        l.holds σ P β ⟨i, by omega⟩) :
    ∀ α, ((Path.ofIndexed n (fun i => incoming i.val) (fun i => states i.val)).trace
      JudgementTableau.labels JudgementTableau.labels_finite).holds σ P α ⟨0, by omega⟩ := by
  let T := finiteRootTableau (Clock := Clock) X root
  let duration : ℕ → NNReal := fun i =>
    if hi : i < P.size then STLTableau.Judgement.duration P ⟨i, hi⟩ else 0
  have hd (i : ℕ) (hi : i < n) : duration i =
      STLTableau.Judgement.duration P ⟨i, by omega⟩ := dif_pos (by omega)
  have hrec : ∀ i < n, ∀ c : T.clocks, v (i + 1) (.inr (.inl c)) =
      T.reset (incoming i).resets (v i) (.inr (.inl c)) + duration i := by
    intro i hi c
    rw [hd i hi]
    exact hstep i hi c
  apply finiteRootTableau_indexed_trace_holds X root n
    (fun i => incoming i.val) (fun i => states i.val)
    (fun i => hs i.val (by have := i.isLt; omega))
    (fun i => he i.val i.isLt) hi σ P hlen
    (T.realClockSchedule incoming duration (v 0))
  · intro i
    exact T.realClockSchedule_guards n incoming duration v hrec hg i.val
      (by have := i.isLt; omega)
  · intro i
    rw [T.realClockSchedule_succ, hd i.val i.isLt]
    rfl
  · intro i β
    exact hl i.val (by have := i.isLt; omega) β

/-- Goal membership makes the same trace an accepting witness. -/
theorem finiteRootTableau_recognizes_of_real_coordinates
    (X : Set Var) (root : Formula Var) (n : ℕ)
    (incoming : ℕ → EdgeLabel Clock) (states : ℕ → Section3.TransitionForm Clock Var)
    (hs : ∀ i ≤ n, states i ∈ (finiteRootTableau X root).states)
    (he : ∀ i < n,
      (states i, incoming (i + 1), states (i + 1)) ∈ (finiteRootTableau X root).edges)
    (hi : (incoming 0, states 0) ∈ (finiteRootTableau X root).initial)
    (hf : states n ∈ (finiteRootTableau X root).final)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (hlen : n ≤ P.size)
    (v : ℕ → (finiteRootTableau (Clock := Clock) X root).HAVar → ℝ)
    (hg : ∀ i ≤ n, (finiteRootTableau X root).guardsHold (incoming i) (v i))
    (hstep : ∀ (i : ℕ) (hi : i < n), ∀ c : (finiteRootTableau (Clock := Clock) X root).clocks,
      v (i + 1) (.inr (.inl c)) =
        (finiteRootTableau X root).reset (incoming i).resets (v i) (.inr (.inl c)) +
          STLTableau.Judgement.duration P ⟨i, by omega⟩)
    (hl : ∀ (i : ℕ) (hi : i ≤ n) (β : ClockValuation Clock),
      ∀ l ∈ JudgementTableau.labels (states i),
        l.holds σ P β ⟨i, by omega⟩) :
    (finiteRootTableau (Clock := Clock) X root).recognizes JudgementTableau.labels_finite σ P := by
  refine ⟨Path.ofIndexed n (fun i => incoming i.val) (fun i => states i.val),
    Path.ofIndexed_run _ _ _ _ ?_ ?_ hi,
    Path.ofIndexed_accepting _ _ _ _ ?_ ?_ hf, ?_⟩
  · intro i; exact hs i.val (by have := i.isLt; omega)
  · intro i; exact he i.val i.isLt
  · intro i; exact hs i.val (by have := i.isLt; omega)
  · intro i; exact he i.val i.isLt
  · exact finiteRootTableau_given_trace_holds_of_real_coordinates X root n incoming states
      hs he hi σ P hlen v hg hstep hl

end STLTableau.Section4.Finiteness
