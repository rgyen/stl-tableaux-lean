import STLTableaux.Automata.Recognition.ExecutionIntervalAssignment

open STLTableau STLTableau.Section4.Tableau

example : IntervalPartition.singletonMarkers
    (fun j : Fin 4 => residenceBoundary [1, 0, 1] j.val) ⟨2, by decide⟩ = ○ := by
  simpa using singletonMarkers_residence_succ [1, 0, 1] ⟨1, by decide⟩

example : IntervalPartition.singletonMarkers
    (fun j : Fin 4 => residenceBoundary [1, 0, 1] j.val) ⟨1, by decide⟩ = ● := by
  simpa using singletonMarkers_residence_succ [1, 0, 1] ⟨0, by decide⟩

example : ∃ P : IntervalPartition (Set.Ico (0 : ℝ) 2), P.size = 3 := by
  let ds : List NNReal := [1, 0, 1]
  have hz : ∀ (i : Fin ds.length) (hi : i.val + 1 < ds.length),
      ds[i.val] = 0 → ds[i.val + 1] ≠ 0 := by
    intro i hi he
    fin_cases i <;> norm_num [ds] at *
  have hl : ∀ i : Fin ds.length, i.val + 1 = ds.length → ds[i.val] ≠ 0 := by
    intro i hi
    fin_cases i <;> norm_num [ds] at *
  obtain ⟨P, hsize, _⟩ := exists_assignedExecutionInterval_partition 0 ds hz hl
  have hend : (0 : ℝ) + (ds.sum : ℝ) = 2 := by norm_num [ds]
  refine ⟨{ P with covers := ?_ }, hsize⟩
  exact P.covers.trans (congrArg (Set.Ico (0 : ℝ)) hend)

example : (executionInterval 1 1 ●).carrier = {1} := by
  simp [executionInterval_closed_carrier]

example : (executionInterval 1 2 ○).carrier = Set.Ioo 1 2 := by
  norm_num [executionInterval, MarkedInterval.carrier_eq]

-- The user's concrete [0,1), {1}, (1,2) construction is a valid partition.
example : ∃ P : IntervalPartition (Set.Ico (0 : ℝ) 2), ∃ hsize : P.size = 3,
    (P.interval ⟨0, by omega⟩).carrier = Set.Ico 0 1 ∧
    (P.interval ⟨1, by omega⟩).carrier = {1} ∧
    (P.interval ⟨2, by omega⟩).carrier = Set.Ioo 1 2 := by
  let b : Fin 4 → ℝ := ![0, 1, 1, 2]
  have hb : Monotone b := by
    intro i j hij
    have hnat : i.val ≤ j.val := hij
    clear hij
    fin_cases i <;> fin_cases j <;> norm_num [b] at *
  have hz : IntervalPartition.IsolatedSingletons b := by
    intro i hi he
    fin_cases i <;> norm_num [b] at *
  have hl : ∀ i : Fin 3, i.val + 1 = 3 →
      b ⟨i.val, by omega⟩ ≠ b ⟨i.val + 1, by omega⟩ := by
    intro i hi
    fin_cases i <;> norm_num [b] at *
  obtain ⟨P, hsize, hpiece⟩ := exists_executionInterval_partition b hb hz hl
  refine ⟨P, hsize, ?_, ?_, ?_⟩
  · rw [hpiece ⟨0, by decide⟩]
    norm_num [b, executionInterval, IntervalPartition.singletonMarkers, MarkedInterval.carrier_eq]
  · rw [hpiece ⟨1, by decide⟩]
    norm_num [b, executionInterval, IntervalPartition.singletonMarkers, MarkedInterval.carrier_eq]
  · rw [hpiece ⟨2, by decide⟩]
    norm_num [b, executionInterval, IntervalPartition.singletonMarkers, MarkedInterval.carrier_eq]

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``executionInterval_closed_carrier, ``executionInterval_subset_raw,
      ``executionInterval_nonempty_iff, ``assignedExecutionInterval_duration,
      ``executionInterval_eq_singletonBoundaryPiece, ``exists_executionInterval_partition,
      ``residenceBoundary_eq_next_iff, ``exists_assignedExecutionInterval_partition,
      ``singletonMarkers_residence_succ, ``singletonMarkers_residence_open_iff,
      ``ObservedPath.atom_on_executionInterval] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
