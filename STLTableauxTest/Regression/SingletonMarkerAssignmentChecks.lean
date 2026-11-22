import STLTableaux.Automata.Recognition.SingletonLabelPartition

open STLTableau STLTableau.IntervalPartition

namespace SingletonMarkerRegression

def times : Fin 4 → ℝ := ![0, 1, 1, 2]

theorem computed_markers : singletonMarkers times = ![●, ●, ○, ●] := by
  funext i
  fin_cases i <;> simp [singletonMarkers, times]

theorem isolated : IsolatedSingletons times := by
  intro i hi he
  fin_cases i <;> norm_num [times] at *

theorem final_piece_positive : ∀ i : Fin 3, i.val + 1 = 3 →
    times ⟨i.val, by omega⟩ ≠ times ⟨i.val + 1, by omega⟩ := by
  intro i hi
  fin_cases i <;> norm_num [times] at *

theorem markers_compatible : SingletonCompatible times (singletonMarkers times) :=
  singletonMarkers_compatible times isolated

/-- No free marker witness is needed for the user's three-piece example. -/
example : ∃ m : Fin 4 → Marker,
    m 0 = ● ∧ m 3 = ● ∧ SingletonCompatible times m ∧
    (∀ i : Fin 3, times ⟨i.val, by omega⟩ ≠ times ⟨i.val + 1, by omega⟩ →
      m ⟨i.val + 1, by omega⟩ = ●) ∧
    ∀ i mark, mark ∈ ({(![●, ●, ○] : Fin 3 → Marker) i} : Set Marker) →
      m ⟨i.val, by omega⟩ = mark := by
  apply (exists_singletonMarkers_iff times _).mpr
  refine ⟨isolated, final_piece_positive, ?_⟩
  intro i mark hmark
  simp only [Set.mem_singleton_iff] at hmark
  rw [computed_markers, hmark]
  fin_cases i <;> rfl

/-- The label-driven construction also preserves the singleton/open pair. -/
theorem label_driven_singleton : ∃ m : Fin 4 → Marker,
    m 0 = ● ∧ m 3 = ● ∧ SingletonCompatible times m ∧
    ∀ i mark, mark ∈ ({(![●, ●, ○] : Fin 3 → Marker) i} : Set Marker) →
      m ⟨i.val, by omega⟩ = mark := by
  apply exists_markers_of_singleton_requirements (by decide) times _
  · simp [singletonRequirements, times]
  · intro i
    fin_cases i <;> simp [singletonRequirements, times, Fin.exists_fin_succ]
  · exact final_piece_positive

end SingletonMarkerRegression

namespace LabelDrivenMarkerRegression

def times : Fin 3 → ℝ := ![0, 1, 2]
def required : Fin 2 → Set Marker := fun i => {(![●, ○] : Fin 2 → Marker) i}

/-- The label of the second positive piece requires an open left boundary.
The old canonical singletonMarkers would choose closed at this boundary. -/
theorem chooses_label_markers : ∃ m : Fin 3 → Marker,
    m 0 = ● ∧ m 2 = ● ∧ SingletonCompatible times m ∧
    ∀ i mark, mark ∈ required i → m ⟨i.val, by omega⟩ = mark := by
  apply exists_markers_of_singleton_requirements (by decide) times required
  · simp [singletonRequirements, required, times]
  · intro i
    fin_cases i <;>
      simp [singletonRequirements, required, times]
  · intro i hi
    fin_cases i <;> norm_num [times] at *

theorem not_canonical : singletonMarkers times 1 ≠ ○ := by
  norm_num [singletonMarkers, times]
  decide

end LabelDrivenMarkerRegression

-- An initial singleton contributes a closed requirement, never an open one.
example : ○ ∉ singletonRequirements (![0, 0, 1] : Fin 3 → ℝ)
    (fun _ : Fin 2 => (∅ : Set Marker)) ⟨0, by decide⟩ := by
  rw [open_mem_singletonRequirements_first_iff]
  exact Set.notMem_empty _

-- Nor can a positive first piece acquire an open requirement from geometry.
example : ○ ∉ singletonRequirements (![0, 1, 2] : Fin 3 → ℝ)
    (fun _ : Fin 2 => ({●} : Set Marker)) ⟨0, by decide⟩ := by
  rw [open_mem_singletonRequirements_first_iff]
  simp

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``open_mem_singletonRequirements_first_iff,
      ``singletonMarkers_compatible, ``singletonMarkers_unique,
      ``exists_singletonMarkers_iff, ``ofIsolatedSingletons,
      ``exists_markers_of_singleton_requirements,
      ``LabelDrivenMarkerRegression.chooses_label_markers,
      ``LabelDrivenMarkerRegression.not_canonical,
      ``STLTableau.Section4.Finiteness.execution_labels_hold_on_required_partition,
      ``SingletonMarkerRegression.computed_markers,
      ``SingletonMarkerRegression.label_driven_singleton,
      ``STLTableau.Section4.Finiteness.execution_labels_hold_on_isolated_singleton_partition] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
