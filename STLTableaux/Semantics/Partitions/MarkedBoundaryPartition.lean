import STLTableaux.Semantics.Partitions.BoundaryPartition

/-! Marker-aware partitions on strictly increasing boundaries. At each cut,
the left marker of the next piece determines ownership of the shared point.
This construction neither adds pieces nor represents zero-time graph steps. -/
namespace STLTableau.IntervalPartition

def markedBoundaryPiece {n : ℕ} (b : Fin (n + 1) → ℝ)
    (m : Fin (n + 1) → Marker) (i : Fin n) : MarkedInterval :=
  ⟨b ⟨i.val, by omega⟩, b ⟨i.val + 1, by omega⟩,
    m ⟨i.val, by omega⟩, Marker.complement (m ⟨i.val + 1, by omega⟩)⟩

theorem markedBoundaryPiece_subset_closed {n : ℕ} (b : Fin (n + 1) → ℝ)
    (m : Fin (n + 1) → Marker) (i : Fin n) :
    (markedBoundaryPiece b m i).carrier ⊆
      Set.Icc (b ⟨i.val, by omega⟩) (b ⟨i.val + 1, by omega⟩) :=
  fun _ hx => ⟨MarkedInterval.left_le_of_mem hx, MarkedInterval.le_right_of_mem hx⟩

theorem markedBoundaryPiece_disjoint {n : ℕ} (b : Fin (n + 1) → ℝ)
    (hb : StrictMono b) (m : Fin (n + 1) → Marker)
    {i j : Fin n} (hij : i < j) :
    Disjoint (markedBoundaryPiece b m i).carrier (markedBoundaryPiece b m j).carrier := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hi := markedBoundaryPiece_subset_closed b m i hxi
  have hj := markedBoundaryPiece_subset_closed b m j hxj
  have hle : b ⟨i.val + 1, by omega⟩ ≤ b ⟨j.val, by omega⟩ :=
    hb.monotone (by change i.val + 1 ≤ j.val; exact hij)
  have he : b ⟨i.val + 1, by omega⟩ = b ⟨j.val, by omega⟩ :=
    le_antisymm hle (hj.1.trans hi.2)
  have heidx := hb.injective he
  have hx : x = b ⟨i.val + 1, by omega⟩ :=
    le_antisymm hi.2 (he ▸ hj.1)
  have hri := (MarkedInterval.mem_iff.mp hxi).2
  have hlj := (MarkedInterval.mem_iff.mp hxj).1
  change (x < b ⟨i.val + 1, by omega⟩ ∨
    (x = b ⟨i.val + 1, by omega⟩ ∧ (Marker.complement (m _)).Includes)) at hri
  change (b ⟨j.val, by omega⟩ < x ∨
    (b ⟨j.val, by omega⟩ = x ∧ (m _).Includes)) at hlj
  rw [hx, heidx] at hri
  rw [hx, he] at hlj
  cases hm : m ⟨j.val, by omega⟩ <;>
    simp [hm, Marker.complement, Marker.Includes] at hri hlj

def ofMarkedBoundaries {n : ℕ} (b : Fin (n + 1) → ℝ) (hb : StrictMono b)
    (m : Fin (n + 1) → Marker)
    (hfirst : m ⟨0, by omega⟩ = ●) (hlast : m ⟨n, by omega⟩ = ●) :
    IntervalPartition (Set.Ico (b ⟨0, by omega⟩) (b ⟨n, by omega⟩)) where
  size := n
  interval := markedBoundaryPiece b m
  nonempty := by
    intro i
    have hlt := hb (show (⟨i.val, by omega⟩ : Fin (n + 1)) <
      ⟨i.val + 1, by omega⟩ from Nat.lt_succ_self _)
    obtain ⟨x, hlo, hhi⟩ := exists_between hlt
    exact ⟨x, Or.inl hlo, Or.inl hhi⟩
  pairwiseDisjoint := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact markedBoundaryPiece_disjoint b hb m hlt
    · exact (markedBoundaryPiece_disjoint b hb m hgt).symm
  covers := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      have hx := markedBoundaryPiece_subset_closed b m i hi
      refine ⟨(hb.monotone (by change 0 ≤ i.val; omega)).trans hx.1, ?_⟩
      by_cases he : i.val + 1 = n
      · have hidx : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := Fin.ext he
        have hr := (MarkedInterval.mem_iff.mp hi).2
        change x < b ⟨i.val + 1, by omega⟩ ∨
          (x = b ⟨i.val + 1, by omega⟩ ∧ (Marker.complement (m _)).Includes) at hr
        simpa [hidx, hlast, Marker.complement, Marker.Includes] using hr
      · exact hx.2.trans_lt (hb (by change i.val + 1 < n; omega))
    · intro hx
      obtain ⟨i, hlo, hhi⟩ := exists_boundary_piece b hx
      by_cases he : b ⟨i.val, by omega⟩ = x
      · cases hm : m ⟨i.val, by omega⟩ with
        | closed =>
          exact ⟨i, Or.inr ⟨he, by simp [markedBoundaryPiece, hm, Marker.Includes]⟩,
            Or.inl hhi⟩
        | «open» =>
          have hipos : 0 < i.val := by
            by_contra hn
            have hz : (⟨i.val, by omega⟩ : Fin (n + 1)) = ⟨0, by omega⟩ :=
              Fin.ext (by dsimp; omega)
            rw [hz, hfirst] at hm
            cases hm
          let j : Fin n := ⟨i.val - 1, by omega⟩
          have heidx : (⟨j.val + 1, by omega⟩ : Fin (n + 1)) = ⟨i.val, by omega⟩ :=
            Fin.ext (by dsimp [j]; omega)
          refine ⟨j, Or.inl ?_, Or.inr ?_⟩
          · rw [← he]
            exact hb (by change i.val - 1 < i.val; omega)
          · change x = b ⟨j.val + 1, by omega⟩ ∧ (Marker.complement (m _)).Includes
            rw [heidx]
            exact ⟨he.symm, by simp [hm, Marker.complement, Marker.Includes]⟩
      · exact ⟨i, Or.inl (lt_of_le_of_ne hlo he), Or.inl hhi⟩
  ordered := by
    intro i j hij
    exact hb.monotone (by change i.val + 1 ≤ j.val; exact hij)

theorem markedBoundaryPiece_last_subset_halfOpen {n : ℕ}
    (b : Fin (n + 1) → ℝ) (m : Fin (n + 1) → Marker)
    (hlast : m ⟨n, by omega⟩ = ●) (i : Fin n) (hi : i.val + 1 = n) :
    (markedBoundaryPiece b m i).carrier ⊆
      Set.Ico (b ⟨i.val, by omega⟩) (b ⟨i.val + 1, by omega⟩) := by
  intro x hx
  refine ⟨(markedBoundaryPiece_subset_closed b m i hx).1, ?_⟩
  have hr := (MarkedInterval.mem_iff.mp hx).2
  have he : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := Fin.ext hi
  simpa [markedBoundaryPiece, he, hlast, Marker.complement, Marker.Includes] using hr

end STLTableau.IntervalPartition
