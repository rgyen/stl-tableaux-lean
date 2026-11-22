import STLTableaux.Semantics.Partitions.Partition

/-! Ordered half-open partitions from strictly increasing boundaries. -/
namespace STLTableau.IntervalPartition

theorem exists_boundary_piece {n : ℕ} (b : Fin (n + 1) → ℝ)
    {x : ℝ} (hx : x ∈ Set.Ico (b ⟨0, by omega⟩) (b ⟨n, by omega⟩)) :
    ∃ i : Fin n, x ∈ Set.Ico (b ⟨i.val, by omega⟩) (b ⟨i.val + 1, by omega⟩) := by
  classical
  have hex : ∃ k : ℕ, ∃ hk : k < n + 1, x < b ⟨k, hk⟩ := ⟨n, by omega, hx.2⟩
  let k := Nat.find hex
  obtain ⟨hk, hlt⟩ := Nat.find_spec hex
  have hpos : 0 < k := by
    by_contra hn
    have he : k = 0 := by omega
    change x < b ⟨k, hk⟩ at hlt
    simp only [he] at hlt
    exact (not_lt_of_ge hx.1) hlt
  have hprev : b ⟨k - 1, by omega⟩ ≤ x := by
    by_contra hn
    exact Nat.find_min hex (by change k - 1 < k; omega)
      ⟨by omega, lt_of_not_ge hn⟩
  refine ⟨⟨k - 1, by omega⟩, hprev, ?_⟩
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hlt

def ofBoundaries {n : ℕ} (b : Fin (n + 1) → ℝ) (hb : StrictMono b) :
    IntervalPartition (Set.Ico (b ⟨0, by omega⟩) (b ⟨n, by omega⟩)) where
  size := n
  interval := fun i => ⟨b ⟨i.val, by omega⟩, b ⟨i.val + 1, by omega⟩, ●, ○⟩
  nonempty := by
    intro i
    rw [MarkedInterval.carrier_eq]
    exact ⟨b ⟨i.val, by omega⟩, le_rfl, hb (by change i.val < i.val + 1; omega)⟩
  pairwiseDisjoint := by
    intro i j hij
    rw [MarkedInterval.carrier_eq, MarkedInterval.carrier_eq]
    apply Set.disjoint_left.mpr
    intro x hi hj
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hle := hb.monotone (show (⟨i.val + 1, by omega⟩ : Fin (n + 1)) ≤
          ⟨j.val, by omega⟩ by change i.val + 1 ≤ j.val; exact hij)
      exact (not_lt_of_ge (hle.trans hj.1)) hi.2
    · have hle := hb.monotone (show (⟨j.val + 1, by omega⟩ : Fin (n + 1)) ≤
          ⟨i.val, by omega⟩ by change j.val + 1 ≤ i.val; exact hji)
      exact (not_lt_of_ge (hle.trans hi.1)) hj.2
  covers := by
    ext x
    simp only [Set.mem_iUnion, MarkedInterval.carrier_eq]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨(hb.monotone (by change 0 ≤ i.val; omega)).trans hi.1,
        hi.2.trans_le (hb.monotone (by change i.val + 1 ≤ n; omega))⟩
    · exact exists_boundary_piece b
  ordered := by
    intro i j hij
    exact hb.monotone (by change i.val + 1 ≤ j.val; exact hij)

end STLTableau.IntervalPartition
