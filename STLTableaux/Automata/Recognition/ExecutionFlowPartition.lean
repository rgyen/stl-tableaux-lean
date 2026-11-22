import STLTableaux.Semantics.Partitions.BoundaryPartition
import STLTableaux.Semantics.Partitions.PointOpenPartition
import STLTableaux.Semantics.Partitions.MarkedBoundaryPartition
import STLTableaux.Automata.Recognition.TableauSignalProjection

/-! Geometric time cells for the executed prefix. Their coverage includes
zero, but does not assign its valuation to the first positive flow: the
initial state owns zero. Zero-time visits are represented separately. -/
namespace STLTableau.HybridAutomaton.Execution
variable {Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
    {σ : FiniteSignal Var} (e : H.Execution σ)

def flowPartition : IntervalPartition
    (Set.Ico (0 : ℝ) (e.boundary ⟨e.count, by omega⟩)) :=
  { IntervalPartition.ofBoundaries e.boundary e.increasing with
    covers := by
      rw [(IntervalPartition.ofBoundaries e.boundary e.increasing).covers, e.first_zero] }

@[simp] theorem mem_flowPartition (i : Fin e.count) (t : ℝ) :
    t ∈ (e.flowPartition.interval i).carrier ↔
      e.boundary ⟨i.val, by omega⟩ ≤ t ∧
      t < e.boundary ⟨i.val + 1, by omega⟩ := by
  rw [MarkedInterval.carrier_eq]
  rfl

/-- Early termination does not silently create coverage of the suffix. -/
theorem flowPartition_covers_signal_iff :
    (⋃ i, (e.flowPartition.interval i).carrier) = σ.domain ↔
      e.boundary ⟨e.count, by omega⟩ = σ.horizon := by
  rw [e.flowPartition.covers]
  constructor
  · intro he
    apply le_antisymm e.last_le_horizon
    by_contra hn
    have ht : e.boundary ⟨e.count, by omega⟩ < σ.horizon := lt_of_not_ge hn
    have hnonneg : 0 ≤ e.boundary ⟨e.count, by omega⟩ := by
      rw [← e.first_zero]
      exact e.increasing.monotone (by change 0 ≤ e.count; omega)
    have hm : e.boundary ⟨e.count, by omega⟩ ∈ σ.domain := ⟨hnonneg, ht⟩
    rw [← he] at hm
    exact (lt_irrefl _) hm.2
  · intro he
    rw [he]
    rfl

/-- Full-domain use requires an explicit exhaustion proof. -/
def fullFlowPartition (he : e.boundary ⟨e.count, by omega⟩ = σ.horizon) :
    IntervalPartition σ.domain :=
  { e.flowPartition with covers := (e.flowPartition_covers_signal_iff).mpr he }

/-- Boundary points occur once; interiors exclude both endpoints. This is a
geometric partition, not an assignment of all intermediate jump modes. -/
def pointOpenFlowPartition : IntervalPartition
    (Set.Ico (0 : ℝ) (e.boundary ⟨e.count, by omega⟩)) :=
  { IntervalPartition.pointOpenPartition e.boundary e.increasing with
    covers := by
      rw [(IntervalPartition.pointOpenPartition e.boundary e.increasing).covers, e.first_zero] }

theorem pointOpenFlowPartition_finer : e.pointOpenFlowPartition.FinerThan e.flowPartition :=
  IntervalPartition.pointOpenPartition_finer e.boundary e.increasing

/-- Reassign internal boundary points according to chosen left markers, without
changing flow boundaries or adding pieces. The final endpoint remains excluded.
This still partitions only the executed prefix, not an unexecuted suffix. -/
def markedFlowPartition (m : Fin (e.count + 1) → Marker)
    (hfirst : m ⟨0, by omega⟩ = ●) (hlast : m ⟨e.count, by omega⟩ = ●) :
    IntervalPartition (Set.Ico (0 : ℝ) (e.boundary ⟨e.count, by omega⟩)) :=
  { IntervalPartition.ofMarkedBoundaries e.boundary e.increasing m hfirst hlast with
    covers := by
      rw [(IntervalPartition.ofMarkedBoundaries e.boundary e.increasing m hfirst hlast).covers,
        e.first_zero] }

theorem markedFlowPartition_leftMarker (m : Fin (e.count + 1) → Marker)
    (hfirst : m ⟨0, by omega⟩ = ●) (hlast : m ⟨e.count, by omega⟩ = ●)
    (i : Fin e.count) :
    ((e.markedFlowPartition m hfirst hlast).interval i).leftBoundary =
      m ⟨i.val, by omega⟩ := rfl

theorem markedFlowPartition_duration (m : Fin (e.count + 1) → Marker)
    (hfirst : m ⟨0, by omega⟩ = ●) (hlast : m ⟨e.count, by omega⟩ = ●)
    (i : Fin e.count) :
    ((e.markedFlowPartition m hfirst hlast).interval i).right -
      ((e.markedFlowPartition m hfirst hlast).interval i).left = e.duration i :=
  (e.duration_eq i).symm

end STLTableau.HybridAutomaton.Execution

namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {σ : FiniteSignal T.HAVar} (e : (T.toAutomaton h τ hτ).Execution σ)

theorem flowPartition_projected_atom {ρ : FiniteSignal Var} (hp : T.ProjectsTo σ ρ)
    (i : Fin e.count) (t : σ.Time) (u : ρ.Time) (htu : t.val = u.val)
    (ht : t.val ∈ (e.flowPartition.interval i).carrier)
    (a : AtomicProposition Var)
    (ha : Section3.Local.predicate (.plain (.atom a)) ∈ T.label (e.start i).val.1.val) :
    a.Holds (ρ.value u) :=
  T.execution_projected_atom h τ hτ e hp i t u htu
    ((e.mem_flowPartition i t.val).mp ht) a ha

theorem pointOpenFlowPartition_projected_atom {ρ : FiniteSignal Var}
    (hp : T.ProjectsTo σ ρ) (j : Fin (2 * e.count))
    (t : σ.Time) (u : ρ.Time) (htu : t.val = u.val)
    (ht : t.val ∈ (e.pointOpenFlowPartition.interval j).carrier)
    (a : AtomicProposition Var)
    (ha : Section3.Local.predicate (.plain (.atom a)) ∈
      T.label (e.start ⟨j.val / 2, by omega⟩).val.1.val) :
    a.Holds (ρ.value u) := by
  apply T.execution_projected_atom h τ hτ e hp ⟨j.val / 2, by omega⟩ t u htu _ a ha
  exact IntervalPartition.pointOpenPiece_subset_parent e.boundary e.increasing j ht

/-- Every flow-mode atom remains valid after reassigning internal boundary
points. The closed-interval result handles internal right endpoints; the final
piece excludes its right endpoint, so no suffix/terminal value is assumed. -/
theorem markedFlowPartition_projected_atom {ρ : FiniteSignal Var}
    (hp : T.ProjectsTo σ ρ) (m : Fin (e.count + 1) → Marker)
    (hfirst : m ⟨0, by omega⟩ = ●) (hlast : m ⟨e.count, by omega⟩ = ●)
    (i : Fin e.count) (t : σ.Time) (u : ρ.Time) (htu : t.val = u.val)
    (ht : t.val ∈ ((e.markedFlowPartition m hfirst hlast).interval i).carrier)
    (a : AtomicProposition Var)
    (ha : Section3.Local.predicate (.plain (.atom a)) ∈ T.label (e.start i).val.1.val) :
    a.Holds (ρ.value u) := by
  by_cases hi : i.val + 1 < e.count
  · exact T.execution_projected_closed_atom h τ hτ e hp i hi t u htu
      (IntervalPartition.markedBoundaryPiece_subset_closed e.boundary m i ht) a ha
  · exact T.execution_projected_atom h τ hτ e hp i t u htu
      (IntervalPartition.markedBoundaryPiece_last_subset_halfOpen
        e.boundary m hlast i (by omega) ht) a ha

end STLTableau.Section4.Tableau
