import STLTableaux.Semantics.Partitions.MarkedBoundaryPartition

/-! Exact feasibility of assigning left markers to positive-length pieces.
The final boundary marker is a sentinel: closed there makes the preceding
right endpoint open. These are geometric constraints, not assumed properties
of a tableau graph or an erasure rule for zero-time transitions. -/
namespace STLTableau.IntervalPartition

theorem exists_boundaryMarkers_iff {n : ℕ} (hn : 0 < n)
    (required : Fin n → Set Marker) :
    (∃ m : Fin (n + 1) → Marker,
      m ⟨0, by omega⟩ = ● ∧ m ⟨n, by omega⟩ = ● ∧
      ∀ i : Fin n, ∀ b ∈ required i, m ⟨i.val, by omega⟩ = b) ↔
    (○ ∉ required ⟨0, hn⟩ ∧ ∀ i, ¬ (○ ∈ required i ∧ ● ∈ required i)) := by
  classical
  constructor
  · rintro ⟨m, hfirst, _, hm⟩
    constructor
    · intro ho
      have he := hm ⟨0, hn⟩ ○ ho
      rw [hfirst] at he
      cases he
    · intro i hc
      have he := (hm i ○ hc.1).symm.trans (hm i ● hc.2)
      cases he
  · rintro ⟨hfirst, hconsistent⟩
    let m : Fin (n + 1) → Marker := fun j =>
      if hj : j.val < n then
        if ○ ∈ required ⟨j.val, hj⟩ then ○ else ●
      else ●
    refine ⟨m, ?_, ?_, ?_⟩
    · simp [m, hn, hfirst]
    · simp [m]
    · intro i b hb
      change (if hi : i.val < n then
        if ○ ∈ required ⟨i.val, hi⟩ then ○ else ● else ●) = b
      rw [dif_pos i.isLt]
      cases b with
      | «open» => simp [hb]
      | closed =>
        have ho : ○ ∉ required i := fun ho => hconsistent i ⟨ho, hb⟩
        simp [ho]

/-- Feasible requirements give an actual covering partition with the same
strictly increasing boundaries and exactly n pieces. No point is discarded. -/
theorem exists_markedPartition_of_requirements {n : ℕ} (hn : 0 < n)
    (b : Fin (n + 1) → ℝ) (hb : StrictMono b) (required : Fin n → Set Marker)
    (hfirst : ○ ∉ required ⟨0, hn⟩)
    (hconsistent : ∀ i, ¬ (○ ∈ required i ∧ ● ∈ required i)) :
    ∃ m : Fin (n + 1) → Marker, ∃ h0 : m ⟨0, by omega⟩ = ●,
      ∃ hlast : m ⟨n, by omega⟩ = ●,
        ∀ i : Fin n, ∀ mark ∈ required i,
          ((ofMarkedBoundaries b hb m h0 hlast).interval i).leftBoundary = mark := by
  obtain ⟨m, h0, hlast, hm⟩ := (exists_boundaryMarkers_iff hn required).mpr ⟨hfirst, hconsistent⟩
  exact ⟨m, h0, hlast, hm⟩

end STLTableau.IntervalPartition
