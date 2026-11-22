import STLTableaux.Automata.Recognition.ExecutionObservedAtoms
import STLTableaux.Semantics.Partitions.SingletonMarkerAssignment

/-! Interval assignment for the boundary forms of Definition E.1. With a
closed left marker a positive visit gives `[l,r)` and a zero-time visit
gives `{l}`. A positive visit after a singleton opens its left endpoint. -/
namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*}

noncomputable def executionInterval (l r : ℝ) (m : Marker) : MarkedInterval :=
  ⟨l, r, m, if l = r then ● else ○⟩

@[simp] theorem executionInterval_leftBoundary (l r : ℝ) (m : Marker) :
    (executionInterval l r m).leftBoundary = m := rfl

theorem executionInterval_closed_carrier (l r : ℝ) :
    (executionInterval l r ●).carrier = if l = r then {l} else Set.Ico l r := by
  by_cases he : l = r
  · subst r
    simp [executionInterval, MarkedInterval.carrier_eq]
  · simp [executionInterval, he, MarkedInterval.carrier_eq]

theorem executionInterval_subset_raw (l r : ℝ) (m : Marker) :
    (executionInterval l r m).carrier ⊆ (executionInterval l r ●).carrier := by
  intro x hx
  exact ⟨by
    rcases hx.1 with hlt | ⟨he, _⟩
    · exact Or.inl hlt
    · exact Or.inr ⟨he, trivial⟩, hx.2⟩

theorem executionInterval_nonempty_iff (l r : ℝ) (m : Marker) (hlr : l ≤ r) :
    (executionInterval l r m).carrier.Nonempty ↔ l < r ∨ m = ● := by
  rw [MarkedInterval.nonempty_iff]
  by_cases he : l = r
  · subst r
    cases m <;> simp [executionInterval, Marker.conj]
  · have hlt := lt_of_le_of_ne hlr he
    simp [executionInterval, he, hlt, MarkedLT]

/-- With the marker after a singleton chosen open, the literal left-only
operation agrees with the established boundary partition construction.
No right endpoint is changed by this identification. -/
theorem executionInterval_eq_singletonBoundaryPiece {n : ℕ}
    (b : Fin (n + 1) → ℝ) (i : Fin n) :
    executionInterval (b ⟨i.val, by omega⟩) (b ⟨i.val + 1, by omega⟩)
      (IntervalPartition.singletonMarkers b ⟨i.val, by omega⟩) =
      IntervalPartition.markedBoundaryPiece b (IntervalPartition.singletonMarkers b) i := by
  unfold executionInterval IntervalPartition.markedBoundaryPiece
  rw [IntervalPartition.singletonMarkers_succ]
  split_ifs <;> rfl

/-- The assigned intervals form a partition when zero-width pieces are
isolated and the last piece is not a singleton at the excluded endpoint.
The marker array is computed, not an input. This is geometric: agreement of
these markers with a tableau path is not asserted. -/
theorem exists_executionInterval_partition {n : ℕ}
    (b : Fin (n + 1) → ℝ) (hb : Monotone b)
    (hz : IntervalPartition.IsolatedSingletons b)
    (hlast : ∀ i : Fin n, i.val + 1 = n →
      b ⟨i.val, by omega⟩ ≠ b ⟨i.val + 1, by omega⟩) :
    ∃ P : IntervalPartition (Set.Ico (b ⟨0, by omega⟩) (b ⟨n, by omega⟩)),
      ∃ hsize : P.size = n, ∀ i : Fin n,
        P.interval ⟨i.val, by rw [hsize]; exact i.isLt⟩ =
          executionInterval (b ⟨i.val, by omega⟩) (b ⟨i.val + 1, by omega⟩)
            (IntervalPartition.singletonMarkers b ⟨i.val, by omega⟩) := by
  refine ⟨IntervalPartition.ofIsolatedSingletons b hb hz hlast, rfl, ?_⟩
  intro i
  exact (executionInterval_eq_singletonBoundaryPiece b i).symm

/-- Entry times come from the actual extracted residence times; changing
endpoint ownership changes neither endpoints nor the clock increment. -/
noncomputable def assignedExecutionInterval (l : ℝ) (ds : List NNReal)
    (i : Fin ds.length) (m : Marker) : MarkedInterval :=
  executionInterval (l + residenceBoundary ds i.val)
    (l + residenceBoundary ds (i.val + 1)) m

theorem assignedExecutionInterval_duration (l : ℝ) (ds : List NNReal)
    (i : Fin ds.length) (m : Marker) :
    (assignedExecutionInterval l ds i m).right -
      (assignedExecutionInterval l ds i m).left = (ds[i.val] : ℝ) := by
  change (l + residenceBoundary ds (i.val + 1)) -
    (l + residenceBoundary ds i.val) = _
  linarith [residenceBoundary_step ds i.val i.isLt]

theorem residenceBoundary_eq_next_iff (ds : List NNReal)
    (i : ℕ) (hi : i < ds.length) :
    residenceBoundary ds i = residenceBoundary ds (i + 1) ↔ ds[i] = 0 := by
  have hstep := residenceBoundary_step ds i hi
  constructor
  · intro he
    have hz : (ds[i] : ℝ) = 0 := by linarith
    exact_mod_cast hz
  · intro hz
    rw [hz] at hstep
    simp only [NNReal.coe_zero] at hstep
    linarith

/-- The boundary immediately after a zero residence is open; after a positive
residence it is closed. The initial boundary is always closed by
`singletonMarkers_first`. This describes the constructed markers, not the
markers required by an arbitrary tableau label. -/
theorem singletonMarkers_residence_succ (ds : List NNReal) (i : Fin ds.length) :
    IntervalPartition.singletonMarkers
      (fun j : Fin (ds.length + 1) => residenceBoundary ds j.val)
      ⟨i.val + 1, by omega⟩ = if ds[i.val] = 0 then ○ else ● := by
  rw [IntervalPartition.singletonMarkers_succ]
  simp only [residenceBoundary_eq_next_iff ds i.val i.isLt]

/-- The exact local meaning of the constructed open marker: it follows a
zero-duration piece. In particular, the initial marker cannot be open. -/
theorem singletonMarkers_residence_open_iff (ds : List NNReal)
    (j : Fin (ds.length + 1)) :
    IntervalPartition.singletonMarkers
      (fun k : Fin (ds.length + 1) => residenceBoundary ds k.val) j = ○ ↔
      ∃ i : Fin ds.length, j = i.succ ∧ ds[i.val] = 0 := by
  induction j using Fin.cases with
  | zero =>
    simp [IntervalPartition.singletonMarkers]
    intro i he
    have hv := congrArg Fin.val he
    simp only [Fin.val_zero, Fin.val_succ] at hv
    omega
  | succ i =>
    rw [show i.succ = (⟨i.val + 1, by omega⟩ : Fin (ds.length + 1)) from rfl,
      singletonMarkers_residence_succ]
    change (if ds[i.val] = 0 then ○ else ●) = ○ ↔
      ∃ k : Fin ds.length, i.succ = k.succ ∧ ds[k.val] = 0
    by_cases hz : ds[i.val] = 0 <;> simp [hz]

/-- Apply the interval assignment directly to residence times.
Monotonicity is automatic because the durations are nonnegative. The two
remaining geometric hypotheses are explicit: zero durations are isolated,
and the last piece is not a singleton at the excluded right endpoint.
Neither hypothesis nor agreement with label markers is asserted for an
arbitrary extracted execution. -/
theorem exists_assignedExecutionInterval_partition (l : ℝ) (ds : List NNReal)
    (hisolated : ∀ (i : Fin ds.length) (hi : i.val + 1 < ds.length),
      ds[i.val] = 0 → ds[i.val + 1] ≠ 0)
    (hlast : ∀ i : Fin ds.length, i.val + 1 = ds.length → ds[i.val] ≠ 0) :
    ∃ P : IntervalPartition (Set.Ico l (l + (ds.sum : ℝ))),
      ∃ hsize : P.size = ds.length, ∀ i : Fin ds.length,
        P.interval ⟨i.val, by rw [hsize]; exact i.isLt⟩ =
          assignedExecutionInterval l ds i
            (IntervalPartition.singletonMarkers
              (fun j : Fin (ds.length + 1) => l + residenceBoundary ds j.val)
              ⟨i.val, by omega⟩) := by
  let b : Fin (ds.length + 1) → ℝ := fun j => l + residenceBoundary ds j.val
  have hb : Monotone b := by
    intro i j hij
    dsimp [b]
    linarith [residenceBoundary_monotone ds hij]
  have hz : IntervalPartition.IsolatedSingletons b := by
    intro i hi he he'
    have hzero : ds[i.val] = 0 :=
      (residenceBoundary_eq_next_iff ds i.val i.isLt).mp (add_left_cancel he)
    have hnext : ds[i.val + 1] = 0 :=
      (residenceBoundary_eq_next_iff ds (i.val + 1) hi).mp (add_left_cancel he')
    exact hisolated i hi hzero hnext
  have hn : ∀ i : Fin ds.length, i.val + 1 = ds.length →
      b ⟨i.val, by omega⟩ ≠ b ⟨i.val + 1, by omega⟩ := by
    intro i hi he
    exact hlast i hi
      ((residenceBoundary_eq_next_iff ds i.val i.isLt).mp (add_left_cancel he))
  obtain ⟨P, hsize, hpieces⟩ := exists_executionInterval_partition b hb hz hn
  refine ⟨{ P with covers := ?_ }, hsize, hpieces⟩
  simpa only [b, residenceBoundary_zero, residenceBoundary_last, add_zero] using P.covers

/-- The subset argument for atoms, on the literal assigned interval.
This proves no partition existence and assumes no atomic satisfaction. -/
theorem ObservedPath.atom_on_executionInterval
    (T : Tableau Clock Var State) (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {σ : FiniteSignal T.HAVar} (e : (T.toAutomaton h τ hτ).Execution σ)
    {p l r ds} (hp : T.ObservedPath h τ hτ e p l r ds)
    (hf : ∀ s, (T.label s).Finite)
    {ρ : FiniteSignal Var} (hproj : T.ProjectsTo σ ρ)
    (i : Fin (p.trace T.label hf).length) (m : Marker)
    (a : AtomicProposition Var)
    (ha : Section3.Local.predicate (.plain (.atom a)) ∈
      ((p.trace T.label hf).frameAt i).locals)
    (u : ρ.Time)
    (hu : u.val ∈ (executionInterval (l + residenceBoundary ds i.val)
      (l + residenceBoundary ds (i.val + 1)) m).carrier) :
    a.Holds (ρ.value u) := by
  apply hp.frame_atom T h τ hτ e hf hproj i a ha u
  exact ⟨MarkedInterval.left_le_of_mem hu, MarkedInterval.le_right_of_mem hu⟩

end STLTableau.Section4.Tableau
