import STLTableaux.Automata.Recognition.ExecutionFlowPartition
import STLTableaux.Semantics.Partitions.PointSuffixPartition

/-! Complete an early-terminating execution's flow partition with one suffix.
No flow, state label or invariant is assigned to that unexecuted suffix. -/
namespace STLTableau.HybridAutomaton.Execution
variable {Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
    {σ : FiniteSignal Var} (e : H.Execution σ)

def extendedBoundary (i : Fin (e.count + 2)) : ℝ :=
  if hi : i.val < e.count + 1 then e.boundary ⟨i.val, hi⟩ else σ.horizon

theorem extendedBoundary_strictMono
    (he : e.boundary ⟨e.count, by omega⟩ < σ.horizon) : StrictMono e.extendedBoundary := by
  intro i j hij
  have hv : i.val < j.val := hij
  unfold extendedBoundary
  split_ifs with hi hj
  · exact e.increasing hv
  · exact (e.increasing.monotone (by change i.val ≤ e.count; omega)).trans_lt he
  · omega
  · omega

/-- A full signal-domain partition, without requiring the execution to reach
the horizon. The extra piece is not a new execution segment. -/
def completedFlowPartition (he : e.boundary ⟨e.count, by omega⟩ < σ.horizon) :
    IntervalPartition σ.domain :=
  { IntervalPartition.ofBoundaries e.extendedBoundary (e.extendedBoundary_strictMono he) with
    covers := by
      rw [(IntervalPartition.ofBoundaries e.extendedBoundary
        (e.extendedBoundary_strictMono he)).covers]
      simp only [extendedBoundary, show 0 < e.count + 1 by omega, dif_pos,
        show ¬ e.count + 1 < e.count + 1 by omega, e.first_zero]
      rfl }

theorem completedFlowPartition_old_piece
    (he : e.boundary ⟨e.count, by omega⟩ < σ.horizon) (i : Fin e.count) :
    (e.completedFlowPartition he).interval ⟨i.val, by change i.val < e.count + 1; omega⟩ =
      e.flowPartition.interval i := by
  simp only [completedFlowPartition, IntervalPartition.ofBoundaries,
    flowPartition, extendedBoundary, show i.val < e.count + 1 by omega,
    show i.val + 1 < e.count + 1 by omega, dif_pos]

theorem completedFlowPartition_suffix
    (he : e.boundary ⟨e.count, by omega⟩ < σ.horizon) :
    ((e.completedFlowPartition he).interval ⟨e.count, by change e.count < e.count + 1; omega⟩).carrier =
      Set.Ico (e.boundary ⟨e.count, by omega⟩) σ.horizon := by
  simp only [completedFlowPartition, IntervalPartition.ofBoundaries, extendedBoundary,
    show e.count < e.count + 1 by omega, dif_pos,
    show ¬ e.count + 1 < e.count + 1 by omega, MarkedInterval.carrier_eq]
  rfl

/-- The raw positive-flow partition always extends to the whole signal domain.
The old pieces are unchanged; early termination adds exactly one suffix.
This does not assign intervals to zero-time intermediate tableau frames. -/
theorem exists_completed_raw_flow_partition :
    ∃ (P : IntervalPartition σ.domain) (hcount : e.count ≤ P.size),
      (∀ i : Fin e.count,
        P.interval ⟨i.val, lt_of_lt_of_le i.isLt hcount⟩ = e.flowPartition.interval i) ∧
      (e.boundary ⟨e.count, by omega⟩ = σ.horizon → P.size = e.count) ∧
      (e.boundary ⟨e.count, by omega⟩ < σ.horizon →
        ∃ hlast : e.count < P.size, P.size = e.count + 1 ∧
          (P.interval ⟨e.count, hlast⟩).carrier =
            Set.Ico (e.boundary ⟨e.count, by omega⟩) σ.horizon) := by
  rcases lt_or_eq_of_le e.last_le_horizon with he | he
  · refine ⟨e.completedFlowPartition he, by change e.count ≤ e.count + 1; omega,
      ?_, ?_, ?_⟩
    · intro i
      exact e.completedFlowPartition_old_piece he i
    · intro heq
      exact (ne_of_lt he heq).elim
    · intro _
      exact ⟨by change e.count < e.count + 1; omega, rfl,
        e.completedFlowPartition_suffix he⟩
  · refine ⟨e.fullFlowPartition he, le_refl _, ?_, ?_, ?_⟩
    · intro i
      rfl
    · intro _
      rfl
    · intro hlt
      exact (ne_of_lt hlt he).elim

theorem completedFlowPartition_mem_old_piece
    (he : e.boundary ⟨e.count, by omega⟩ < σ.horizon) (i : Fin e.count) (t : σ.Time)
    (ht : t.val ∈ ((e.completedFlowPartition he).interval
      ⟨i.val, by change i.val < e.count + 1; omega⟩).carrier) :
    t.val ∈ (e.flowPartition.interval i).carrier := by
  rwa [e.completedFlowPartition_old_piece he i] at ht

/-- Extend the boundary markers by a closed final sentinel. If the old final
marker is closed, it becomes the left-closed marker of the unexecuted suffix. -/
def extendedMarkers (m : Fin (e.count + 1) → Marker) (j : Fin (e.count + 2)) : Marker :=
  if hj : j.val < e.count + 1 then m ⟨j.val, hj⟩ else ●

def completedMarkedFlowPartition
    (he : e.boundary ⟨e.count, by omega⟩ < σ.horizon)
    (m : Fin (e.count + 1) → Marker)
    (hfirst : m ⟨0, by omega⟩ = ●) :
    IntervalPartition σ.domain :=
  { IntervalPartition.ofMarkedBoundaries e.extendedBoundary (e.extendedBoundary_strictMono he)
      (e.extendedMarkers m)
      (by simpa [extendedMarkers] using hfirst)
      (by simp [extendedMarkers]) with
    covers := by
      rw [(IntervalPartition.ofMarkedBoundaries e.extendedBoundary
        (e.extendedBoundary_strictMono he) (e.extendedMarkers m)
        (by simpa [extendedMarkers] using hfirst) (by simp [extendedMarkers])).covers]
      simp only [extendedBoundary, show 0 < e.count + 1 by omega, dif_pos,
        show ¬ e.count + 1 < e.count + 1 by omega, e.first_zero]
      rfl }

theorem completedMarkedFlowPartition_old_piece
    (he : e.boundary ⟨e.count, by omega⟩ < σ.horizon)
    (m : Fin (e.count + 1) → Marker)
    (hfirst : m ⟨0, by omega⟩ = ●) (hlast : m ⟨e.count, by omega⟩ = ●)
    (i : Fin e.count) :
    (e.completedMarkedFlowPartition he m hfirst).interval
      ⟨i.val, by change i.val < e.count + 1; omega⟩ =
      (e.markedFlowPartition m hfirst hlast).interval i := by
  simp only [completedMarkedFlowPartition, markedFlowPartition,
    IntervalPartition.ofMarkedBoundaries, IntervalPartition.markedBoundaryPiece,
    extendedBoundary, extendedMarkers, show i.val < e.count + 1 by omega,
    show i.val + 1 < e.count + 1 by omega, dif_pos]

theorem completedMarkedFlowPartition_duration
    (he : e.boundary ⟨e.count, by omega⟩ < σ.horizon)
    (m : Fin (e.count + 1) → Marker)
    (hfirst : m ⟨0, by omega⟩ = ●) (hlast : m ⟨e.count, by omega⟩ = ●)
    (i : Fin e.count) :
    ((e.completedMarkedFlowPartition he m hfirst).interval
      ⟨i.val, by change i.val < e.count + 1; omega⟩).right -
    ((e.completedMarkedFlowPartition he m hfirst).interval
      ⟨i.val, by change i.val < e.count + 1; omega⟩).left = e.duration i := by
  rw [e.completedMarkedFlowPartition_old_piece he m hfirst hlast i]
  exact e.markedFlowPartition_duration m hfirst hlast i

theorem completedMarkedFlowPartition_suffix
    (he : e.boundary ⟨e.count, by omega⟩ < σ.horizon)
    (m : Fin (e.count + 1) → Marker)
    (hfirst : m ⟨0, by omega⟩ = ●) (hlast : m ⟨e.count, by omega⟩ = ●) :
    ((e.completedMarkedFlowPartition he m hfirst).interval
      ⟨e.count, by change e.count < e.count + 1; omega⟩).carrier =
      Set.Ico (e.boundary ⟨e.count, by omega⟩) σ.horizon := by
  simp only [completedMarkedFlowPartition, IntervalPartition.ofMarkedBoundaries,
    IntervalPartition.markedBoundaryPiece, extendedBoundary, extendedMarkers,
    show e.count < e.count + 1 by omega, dif_pos,
    show ¬ e.count + 1 < e.count + 1 by omega, hlast, MarkedInterval.carrier_eq]
  rfl

/-- A geometric refinement exposing an early stopping time as its own point.
All earlier flow pieces are also split into points and interiors. This is not
a claim that the same tableau path gains extra next steps. -/
def completedPointOpenFlowPartition
    (he : e.boundary ⟨e.count, by omega⟩ < σ.horizon) :
    IntervalPartition σ.domain :=
  { IntervalPartition.pointOpenPartition e.extendedBoundary
      (e.extendedBoundary_strictMono he) with
    covers := by
      rw [(IntervalPartition.pointOpenPartition e.extendedBoundary
        (e.extendedBoundary_strictMono he)).covers]
      simp only [extendedBoundary, show 0 < e.count + 1 by omega, dif_pos,
        show ¬ e.count + 1 < e.count + 1 by omega, e.first_zero]
      rfl }

theorem completedPointOpenFlowPartition_stop
    (he : e.boundary ⟨e.count, by omega⟩ < σ.horizon) :
    (e.completedPointOpenFlowPartition he).interval
      ⟨2 * e.count, by change 2 * e.count < 2 * (e.count + 1); omega⟩ =
      ⟨e.boundary ⟨e.count, by omega⟩, e.boundary ⟨e.count, by omega⟩, ●, ●⟩ := by
  simp [completedPointOpenFlowPartition, IntervalPartition.pointOpenPartition,
    IntervalPartition.pointOpenPiece, extendedBoundary]

/-- Preserve the marked flow pieces verbatim and append only the observed
stopping point and the unexecuted open suffix. -/
def completedMarkedPointFlowPartition
    (he : e.boundary ⟨e.count, by omega⟩ < σ.horizon)
    (m : Fin (e.count + 1) → Marker)
    (hfirst : m ⟨0, by omega⟩ = ●) (hlast : m ⟨e.count, by omega⟩ = ●) :
    IntervalPartition σ.domain :=
  (e.markedFlowPartition m hfirst hlast).appendPointSuffix
    (by rw [← e.first_zero]; exact e.increasing.monotone (by change 0 ≤ e.count; omega))
    he (by
      intro i
      have hi : i.val < e.count := i.isLt
      change e.boundary ⟨i.val + 1, by omega⟩ ≤ e.boundary ⟨e.count, by omega⟩
      exact e.increasing.monotone (by change i.val + 1 ≤ e.count; omega))

theorem completedMarkedPointFlowPartition_old_piece
    (he : e.boundary ⟨e.count, by omega⟩ < σ.horizon)
    (m : Fin (e.count + 1) → Marker)
    (hfirst : m ⟨0, by omega⟩ = ●) (hlast : m ⟨e.count, by omega⟩ = ●)
    (i : Fin e.count) :
    (e.completedMarkedPointFlowPartition he m hfirst hlast).interval
      ⟨i.val, by change i.val < e.count + 2; omega⟩ =
      (e.markedFlowPartition m hfirst hlast).interval i := by
  apply IntervalPartition.appendPointSuffix_old

theorem completedMarkedPointFlowPartition_stop
    (he : e.boundary ⟨e.count, by omega⟩ < σ.horizon)
    (m : Fin (e.count + 1) → Marker)
    (hfirst : m ⟨0, by omega⟩ = ●) (hlast : m ⟨e.count, by omega⟩ = ●) :
    (e.completedMarkedPointFlowPartition he m hfirst hlast).interval
      ⟨e.count, by change e.count < e.count + 2; omega⟩ =
      ⟨e.boundary ⟨e.count, by omega⟩, e.boundary ⟨e.count, by omega⟩, ●, ●⟩ := by
  apply IntervalPartition.appendPointSuffix_point

theorem completedMarkedPointFlowPartition_duration
    (he : e.boundary ⟨e.count, by omega⟩ < σ.horizon)
    (m : Fin (e.count + 1) → Marker)
    (hfirst : m ⟨0, by omega⟩ = ●) (hlast : m ⟨e.count, by omega⟩ = ●)
    (i : Fin e.count) :
    ((e.completedMarkedPointFlowPartition he m hfirst hlast).interval
      ⟨i.val, by change i.val < e.count + 2; omega⟩).right -
    ((e.completedMarkedPointFlowPartition he m hfirst hlast).interval
      ⟨i.val, by change i.val < e.count + 2; omega⟩).left = e.duration i := by
  rw [e.completedMarkedPointFlowPartition_old_piece he m hfirst hlast i]
  exact e.markedFlowPartition_duration m hfirst hlast i

end STLTableau.HybridAutomaton.Execution

namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)

/-- Start from the execution's flow partition, not its expanded discrete path.
Every actual flow keeps its original interval, duration and numerical labels.
Early stopping adds at most one unexecuted suffix; no atom assertion is made
on that suffix. Arbitrary internal jump blocks require no extra hypotheses.
This result does not identify the flow indices with tableau trace indices. -/
theorem exists_projected_flow_partition
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {σ : FiniteSignal T.HAVar} (e : (T.toAutomaton h τ hτ).Execution σ)
    {ρ : FiniteSignal Var} (hproj : T.ProjectsTo σ ρ) :
    ∃ (P : IntervalPartition ρ.domain) (hcount : e.count ≤ P.size),
      P.size ≤ e.count + 1 ∧
      (∀ i : Fin e.count,
        P.interval ⟨i.val, lt_of_lt_of_le i.isLt hcount⟩ = e.flowPartition.interval i) ∧
      (∀ i : Fin e.count,
        STLTableau.Judgement.duration P ⟨i.val, lt_of_lt_of_le i.isLt hcount⟩ =
          e.duration i) ∧
      ∀ (i : Fin e.count) (a : AtomicProposition Var),
        Section3.Local.predicate (.plain (.atom a)) ∈ T.label (e.start i).val.1.val →
        ∀ u : ρ.Time,
          u.val ∈ (P.interval ⟨i.val, lt_of_lt_of_le i.isLt hcount⟩).carrier →
          a.Holds (ρ.value u) := by
  obtain ⟨P, hcount, hpieces, hfull, hearly⟩ := e.exists_completed_raw_flow_partition
  have hcover : (⋃ i, (P.interval i).carrier) = ρ.domain := by
    simpa only [FiniteSignal.domain, hproj.1] using P.covers
  let Q : IntervalPartition ρ.domain := { P with covers := hcover }
  have hbound : P.size ≤ e.count + 1 := by
    rcases lt_or_eq_of_le e.last_le_horizon with he | he
    · obtain ⟨_, hsize, _⟩ := hearly he
      omega
    · have := hfull he
      omega
  refine ⟨Q, hcount, hbound, hpieces, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    change (P.interval _).right - (P.interval _).left = (e.duration i : ℝ)
    rw [hpieces i]
    exact (e.duration_eq i).symm
  · intro i a ha u hu
    have hu' : u.val ∈ (e.flowPartition.interval i).carrier := by
      change u.val ∈ (P.interval _).carrier at hu
      rwa [hpieces i] at hu
    let t : σ.Time := ⟨u.val, u.property.1, hproj.1.symm ▸ u.property.2⟩
    exact T.flowPartition_projected_atom h τ hτ e hproj i t u rfl hu' a ha

end STLTableau.Section4.Tableau
