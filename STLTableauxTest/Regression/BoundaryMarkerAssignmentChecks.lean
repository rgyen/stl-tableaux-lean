import STLTableaux.Automata.Recognition.NormalizedInputMarkerPartition

open STLTableau STLTableau.IntervalPartition

-- A demand for an open first piece cannot be hidden by choosing other markers.
example {n : ℕ} (hn : 0 < n) (required : Fin n → Set Marker)
    (ho : ○ ∈ required ⟨0, hn⟩) :
    ¬ (∃ m : Fin (n + 1) → Marker,
      m ⟨0, by omega⟩ = ● ∧ m ⟨n, by omega⟩ = ● ∧
      ∀ i : Fin n, ∀ b ∈ required i, m ⟨i.val, by omega⟩ = b) := by
  rw [exists_boundaryMarkers_iff hn required]
  exact fun h => h.1 ho

-- Empty requirements allow a closed-left choice at every cut.
example {n : ℕ} (hn : 0 < n) :
    ∃ m : Fin (n + 1) → Marker,
      m ⟨0, by omega⟩ = ● ∧ m ⟨n, by omega⟩ = ● ∧
      ∀ i : Fin n, ∀ b ∈ (∅ : Set Marker), m ⟨i.val, by omega⟩ = b := by
  exact (exists_boundaryMarkers_iff hn (fun _ => ∅)).mpr ⟨by simp, by simp⟩

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``exists_boundaryMarkers_iff, ``exists_markedPartition_of_requirements,
      ``STLTableau.Section4.Finiteness.inputTableau_exists_flow_label_partition,
      ``STLTableau.Section4.Finiteness.inputTableau_exists_flow_label_partition_with_duration,
      ``STLTableau.Section4.Finiteness.inputTableau_terminal_exists_flow_label_partition,
      ``STLTableau.Section4.Finiteness.inputTableau_exists_completed_flow_label_partition] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
