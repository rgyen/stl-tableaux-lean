import STLTableaux.Automata.Recognition.SingletonLabelPartition

open STLTableau STLTableau.IntervalPartition

namespace SingletonBoundaryRegression

def times : Fin 4 → ℝ := ![0, 1, 1, 2]
def markers : Fin 4 → Marker := ![●, ●, ○, ●]

theorem times_monotone : Monotone times := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [times, Fin.le_iff_val_le_val] at *

theorem singleton_compatible : SingletonCompatible times markers := by
  intro i hi
  fin_cases i <;> norm_num [times, markers] at *

def partition : IntervalPartition (Set.Ico (0 : ℝ) 2) :=
  ofSingletonBoundaries times times_monotone markers singleton_compatible rfl rfl

example : partition.size = 3 := rfl

example : (partition.interval ⟨0, by decide⟩).carrier = Set.Ico (0 : ℝ) 1 := by
  simp [partition, ofSingletonBoundaries, markedBoundaryPiece, times, markers,
    MarkedInterval.carrier_eq, Marker.complement]

example : (partition.interval ⟨1, by decide⟩).carrier = {(1 : ℝ)} := by
  simp [partition, ofSingletonBoundaries, markedBoundaryPiece, times, markers,
    MarkedInterval.carrier_eq, Marker.complement]

example : (partition.interval ⟨2, by decide⟩).carrier = Set.Ioo (1 : ℝ) 2 := by
  simp [partition, ofSingletonBoundaries, markedBoundaryPiece, times, markers,
    MarkedInterval.carrier_eq, Marker.complement]

theorem no_points_lost : (⋃ i, (partition.interval i).carrier) = Set.Ico (0 : ℝ) 2 :=
  partition.covers

theorem raw_predicates_preserved (P : Fin 3 → ℝ → Prop)
    (hP : ∀ i t, t ∈ rawBoundaryPiece times i → P i t) :
    ∀ i t, t ∈ (partition.interval i).carrier → P i t := by
  intro i
  apply markedBoundaryPiece_preserves_predicate times markers i ?_ (P i) (hP i)
  fin_cases i <;> norm_num [times, markers]

end SingletonBoundaryRegression

/- A shared point may belong to the preceding positive piece. This is not
a subset of that piece's raw half-open interval, but is a valid partition. -/
namespace RightClosedBoundaryRegression

def times : Fin 3 → ℝ := ![0, 1, 2]
def markers : Fin 3 → Marker := ![●, ○, ●]

theorem times_monotone : Monotone times := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [times, Fin.le_iff_val_le_val] at *

theorem compatible : SingletonCompatible times markers := by
  intro i hi
  fin_cases i <;> norm_num [times] at hi

def partition : IntervalPartition (Set.Ico (0 : ℝ) 2) :=
  ofSingletonBoundaries times times_monotone markers compatible rfl rfl

example : (partition.interval ⟨0, by decide⟩).carrier = Set.Icc (0 : ℝ) 1 := by
  simp [partition, ofSingletonBoundaries, markedBoundaryPiece, times, markers,
    MarkedInterval.carrier_eq, Marker.complement]

example : (partition.interval ⟨1, by decide⟩).carrier = Set.Ioo (1 : ℝ) 2 := by
  simp [partition, ofSingletonBoundaries, markedBoundaryPiece, times, markers,
    MarkedInterval.carrier_eq, Marker.complement]

theorem no_points_lost : (⋃ i, (partition.interval i).carrier) = Set.Ico (0 : ℝ) 2 :=
  partition.covers

end RightClosedBoundaryRegression

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``markedBoundaryPiece_nonempty_of_monotone,
      ``markedBoundaryPiece_disjoint_of_monotone, ``ofSingletonBoundaries,
      ``markedBoundaryPiece_subset_raw, ``markedBoundaryPiece_preserves_predicate,
      ``STLTableau.Section4.Finiteness.labels_hold_on_singleton_partition,
      ``SingletonBoundaryRegression.no_points_lost,
      ``SingletonBoundaryRegression.raw_predicates_preserved,
      ``RightClosedBoundaryRegression.no_points_lost] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
