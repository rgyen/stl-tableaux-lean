import STLTableaux.Semantics.Partitions.SingletonBoundaryPartition
import STLTableaux.Automata.Recognition.NormalizedInputLabelSemantics
import STLTableaux.Automata.Recognition.ExecutionObservedPiece
import STLTableaux.Semantics.Partitions.SingletonMarkerAssignment
import STLTableaux.Automata.Execution.TerminalPruning

/-! Label satisfaction for the singleton/open-piece construction.
The selected states, raw atomic observations and marker compatibility remain
explicit premises. This does not assert that every execution supplies them. -/
namespace STLTableau.Section4.Finiteness
open Section3 IntervalPartition
variable {Clock Var State : Type*}

theorem labels_hold_on_singleton_partition
    (T : Tableau Clock Var State) (σ : FiniteSignal Var)
    {n : ℕ} (b : Fin (n + 1) → ℝ) (hb : Monotone b)
    (m : Fin (n + 1) → Marker) (hz : SingletonCompatible b m)
    (hfirst : m ⟨0, by omega⟩ = ●) (hlast : m ⟨n, by omega⟩ = ●)
    (hstart : b ⟨0, by omega⟩ = 0) (hend : b ⟨n, by omega⟩ = σ.horizon)
    (s : Fin n → State)
    (hready : ∀ i l, l ∈ T.label (s i) → l.NormalizedReady)
    (hn : ∀ i, Local.terminal ∉ T.label (s i))
    (hm : ∀ i mark, Local.marker mark ∈ T.label (s i) → m ⟨i.val, by omega⟩ = mark)
    (hright : ∀ i : Fin n, b ⟨i.val, by omega⟩ ≠ b ⟨i.val + 1, by omega⟩ →
      m ⟨i.val + 1, by omega⟩ = ●)
    (hatoms : ∀ i a, Local.predicate (.plain (.atom a)) ∈ T.label (s i) →
      ∀ t : σ.Time, t.val ∈ rawBoundaryPiece b i → a.Holds (σ.value t)) :
    ∃ P : IntervalPartition σ.domain, ∃ hsize : P.size = n,
      (∀ i : Fin n, P.interval ⟨i.val, by rw [hsize]; exact i.isLt⟩ = markedBoundaryPiece b m i) ∧
      (∀ i : Fin n, ∀ α : ClockValuation Clock, ∀ l ∈ T.label (s i),
        l.holds σ P α ⟨i.val, by rw [hsize]; omega⟩) := by
  let Q := ofSingletonBoundaries b hb m hz hfirst hlast
  let P : IntervalPartition σ.domain :=
    { Q with covers := by simpa only [hstart, hend, FiniteSignal.domain] using Q.covers }
  refine ⟨P, rfl, fun _ => rfl, ?_⟩
  intro i α
  apply (normalizedReady_labels_hold_iff T (s i) (hready i) σ P α
    ⟨i.val, by change i.val < n + 1; omega⟩ (by exact i.isLt)).mpr
  refine ⟨hn i, hm i, ?_⟩
  intro a ha t ht
  exact hatoms i a ha t (markedBoundaryPiece_subset_raw b m i (hright i) ht)

/-- Unlike the raw half-open construction, this version allows either
adjacent piece to own a flow endpoint. Its atoms follow from the execution,
so no right-openness premise is needed. The supplied states stay unchanged. -/
theorem execution_labels_hold_on_marked_partition
    (T : Tableau Clock Var State) (h : T.TranslationReady)
    {σ : FiniteSignal T.HAVar}
    (e : (T.toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : T.ProjectsTo σ ρ)
    {n : ℕ} (b : Fin (n + 1) → ℝ) (hb : Monotone b)
    (m : Fin (n + 1) → Marker) (hz : SingletonCompatible b m)
    (hfirst : m ⟨0, by omega⟩ = ●) (hlast : m ⟨n, by omega⟩ = ●)
    (hstart : b ⟨0, by omega⟩ = 0) (hend : b ⟨n, by omega⟩ = ρ.horizon)
    (s : Fin n → State)
    (hobs : ∀ i : Fin n, T.ExecutionObservedPiece h σ.horizon σ.horizon_pos e
      (s i) (b ⟨i.val, by omega⟩) (b ⟨i.val + 1, by omega⟩))
    (hready : ∀ i l, l ∈ T.label (s i) → l.NormalizedReady)
    (hn : ∀ i, Local.terminal ∉ T.label (s i))
    (hm : ∀ i mark, Local.marker mark ∈ T.label (s i) → m ⟨i.val, by omega⟩ = mark) :
    ∃ P : IntervalPartition ρ.domain, ∃ hsize : P.size = n,
      (∀ i : Fin n, P.interval ⟨i.val, by rw [hsize]; exact i.isLt⟩ = markedBoundaryPiece b m i) ∧
      (∀ i : Fin n, ∀ α : ClockValuation Clock, ∀ l ∈ T.label (s i),
        l.holds ρ P α ⟨i.val, by rw [hsize]; omega⟩) ∧
      (∀ i : Fin n,
        (STLTableau.Judgement.duration P ⟨i.val, by rw [hsize]; exact i.isLt⟩ : ℝ) =
          b ⟨i.val + 1, by omega⟩ - b ⟨i.val, by omega⟩) := by
  let Q := ofSingletonBoundaries b hb m hz hfirst hlast
  let P : IntervalPartition ρ.domain :=
    { Q with covers := by simpa only [hstart, hend, FiniteSignal.domain] using Q.covers }
  refine ⟨P, rfl, fun _ => rfl, ?_, fun _ => rfl⟩
  intro i α
  apply (normalizedReady_labels_hold_iff T (s i) (hready i) ρ P α
    ⟨i.val, by change i.val < n + 1; omega⟩ (by exact i.isLt)).mpr
  refine ⟨hn i, hm i, ?_⟩
  intro a ha t ht
  exact (hobs i).closed_atom T h _ _ e hp a ha t
    (markedBoundaryPiece_subset_closed b m i ht)

/-- Raw half-open variant, retained for callers using the initial
assignment before opening left endpoints. -/
theorem execution_labels_hold_on_singleton_partition
    (T : Tableau Clock Var State) (h : T.TranslationReady)
    {σ : FiniteSignal T.HAVar}
    (e : (T.toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : T.ProjectsTo σ ρ)
    {n : ℕ} (b : Fin (n + 1) → ℝ) (hb : Monotone b)
    (m : Fin (n + 1) → Marker) (hz : SingletonCompatible b m)
    (hfirst : m ⟨0, by omega⟩ = ●) (hlast : m ⟨n, by omega⟩ = ●)
    (hstart : b ⟨0, by omega⟩ = 0) (hend : b ⟨n, by omega⟩ = ρ.horizon)
    (s : Fin n → State)
    (hobs : ∀ i : Fin n, T.ExecutionObservedPiece h σ.horizon σ.horizon_pos e
      (s i) (b ⟨i.val, by omega⟩) (b ⟨i.val + 1, by omega⟩))
    (hready : ∀ i l, l ∈ T.label (s i) → l.NormalizedReady)
    (hn : ∀ i, Local.terminal ∉ T.label (s i))
    (hm : ∀ i mark, Local.marker mark ∈ T.label (s i) → m ⟨i.val, by omega⟩ = mark)
    (hright : ∀ i : Fin n, b ⟨i.val, by omega⟩ ≠ b ⟨i.val + 1, by omega⟩ →
      m ⟨i.val + 1, by omega⟩ = ●) :
    ∃ P : IntervalPartition ρ.domain, ∃ hsize : P.size = n,
      (∀ i : Fin n, P.interval ⟨i.val, by rw [hsize]; exact i.isLt⟩ = markedBoundaryPiece b m i) ∧
      (∀ i : Fin n, ∀ α : ClockValuation Clock, ∀ l ∈ T.label (s i),
        l.holds ρ P α ⟨i.val, by rw [hsize]; omega⟩) ∧
      (∀ i : Fin n,
        (STLTableau.Judgement.duration P ⟨i.val, by rw [hsize]; exact i.isLt⟩ : ℝ) =
          b ⟨i.val + 1, by omega⟩ - b ⟨i.val, by omega⟩) := by
  obtain ⟨P, hsize, hi, hl⟩ := labels_hold_on_singleton_partition T ρ b hb m hz
    hfirst hlast hstart hend s hready hn hm hright
    (fun i a ha u hu => (hobs i).raw_atom T h _ _ e hp b i a ha u hu)
  refine ⟨P, hsize, hi, hl, ?_⟩
  intro i
  change (P.interval _).right - (P.interval _).left = _
  rw [hi]
  rfl

/-- Marker choice is computed from the selected time boundaries. Only the
agreement of actual label requirements with that computed choice remains. -/
theorem execution_labels_hold_on_isolated_singleton_partition
    (T : Tableau Clock Var State) (h : T.TranslationReady)
    {σ : FiniteSignal T.HAVar}
    (e : (T.toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : T.ProjectsTo σ ρ)
    {n : ℕ} (b : Fin (n + 1) → ℝ) (hb : Monotone b)
    (hisolated : IsolatedSingletons b)
    (hlast : ∀ i : Fin n, i.val + 1 = n →
      b ⟨i.val, by omega⟩ ≠ b ⟨i.val + 1, by omega⟩)
    (hstart : b ⟨0, by omega⟩ = 0) (hend : b ⟨n, by omega⟩ = ρ.horizon)
    (s : Fin n → State)
    (hobs : ∀ i : Fin n, T.ExecutionObservedPiece h σ.horizon σ.horizon_pos e
      (s i) (b ⟨i.val, by omega⟩) (b ⟨i.val + 1, by omega⟩))
    (hready : ∀ i l, l ∈ T.label (s i) → l.NormalizedReady)
    (hn : ∀ i, Local.terminal ∉ T.label (s i))
    (hm : ∀ i mark, Local.marker mark ∈ T.label (s i) →
      singletonMarkers b ⟨i.val, by omega⟩ = mark) :
    ∃ P : IntervalPartition ρ.domain, ∃ hsize : P.size = n,
      (∀ i : Fin n, P.interval ⟨i.val, by rw [hsize]; exact i.isLt⟩ =
        markedBoundaryPiece b (singletonMarkers b) i) ∧
      (∀ i : Fin n, ∀ α : ClockValuation Clock, ∀ l ∈ T.label (s i),
        l.holds ρ P α ⟨i.val, by rw [hsize]; omega⟩) ∧
      (∀ i : Fin n,
        (STLTableau.Judgement.duration P ⟨i.val, by rw [hsize]; exact i.isLt⟩ : ℝ) =
          b ⟨i.val + 1, by omega⟩ - b ⟨i.val, by omega⟩) :=
  execution_labels_hold_on_singleton_partition T h e hp b hb (singletonMarkers b)
    (singletonMarkers_compatible b hisolated) (singletonMarkers_first b)
    (singletonMarkers_last b hlast) hstart hend s hobs hready hn hm (singletonMarkers_right b)

/-- Build the partition and its markers together from local label and
singleton requirements. No marker array or pre-existing partition is supplied. -/
theorem execution_labels_hold_on_required_partition
    (T : Tableau Clock Var State) (h : T.TranslationReady)
    {σ : FiniteSignal T.HAVar}
    (e : (T.toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : T.ProjectsTo σ ρ)
    {n : ℕ} (hnpos : 0 < n) (b : Fin (n + 1) → ℝ) (hb : Monotone b)
    (hstart : b ⟨0, by omega⟩ = 0) (hend : b ⟨n, by omega⟩ = ρ.horizon)
    (s : Fin n → State)
    (hobs : ∀ i : Fin n, T.ExecutionObservedPiece h σ.horizon σ.horizon_pos e
      (s i) (b ⟨i.val, by omega⟩) (b ⟨i.val + 1, by omega⟩))
    (hready : ∀ i l, l ∈ T.label (s i) → l.NormalizedReady)
    (hn : ∀ i, Local.terminal ∉ T.label (s i))
    (hfirst : ○ ∉ singletonRequirements b
      (fun i => {mark | Local.marker mark ∈ T.label (s i)}) ⟨0, hnpos⟩)
    (hconsistent : ∀ i, ¬ (○ ∈ singletonRequirements b
      (fun i => {mark | Local.marker mark ∈ T.label (s i)}) i ∧
      ● ∈ singletonRequirements b (fun i => {mark | Local.marker mark ∈ T.label (s i)}) i))
    (hlast : ∀ i : Fin n, i.val + 1 = n →
      b ⟨i.val, by omega⟩ ≠ b ⟨i.val + 1, by omega⟩) :
    ∃ P : IntervalPartition ρ.domain, ∃ hsize : P.size = n,
      (∀ i : Fin n, ∀ α : ClockValuation Clock, ∀ l ∈ T.label (s i),
        l.holds ρ P α ⟨i.val, by rw [hsize]; omega⟩) ∧
      (∀ i : Fin n,
        (STLTableau.Judgement.duration P ⟨i.val, by rw [hsize]; exact i.isLt⟩ : ℝ) =
          b ⟨i.val + 1, by omega⟩ - b ⟨i.val, by omega⟩) := by
  obtain ⟨m, hm0, hmn, hz, hm⟩ := exists_markers_of_singleton_requirements hnpos b
    (fun i => {mark | Local.marker mark ∈ T.label (s i)}) hfirst hconsistent hlast
  obtain ⟨P, hsize, _, hl, hd⟩ := execution_labels_hold_on_marked_partition T h e hp
    b hb m hz hm0 hmn hstart hend s hobs hready hn hm
  exact ⟨P, hsize, hl, hd⟩

end STLTableau.Section4.Finiteness
