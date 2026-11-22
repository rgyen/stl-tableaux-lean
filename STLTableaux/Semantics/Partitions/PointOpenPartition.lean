import STLTableaux.Semantics.Partitions.BoundaryPartition

/-! Split each positive half-open piece into its left endpoint and open
interior. This geometric refinement does not assign tableau states to pieces. -/
namespace STLTableau.IntervalPartition

def pointOpenPiece {n : ℕ} (b : Fin (n + 1) → ℝ) (i : Fin (2 * n)) : MarkedInterval :=
  if i.val % 2 = 0 then
    ⟨b ⟨i.val / 2, by omega⟩, b ⟨i.val / 2, by omega⟩, ●, ●⟩
  else
    ⟨b ⟨i.val / 2, by omega⟩, b ⟨i.val / 2 + 1, by omega⟩, ○, ○⟩

theorem pointOpenPiece_carrier {n : ℕ} (b : Fin (n + 1) → ℝ) (i : Fin (2 * n)) :
    (pointOpenPiece b i).carrier =
      if i.val % 2 = 0 then {b ⟨i.val / 2, by omega⟩}
      else Set.Ioo (b ⟨i.val / 2, by omega⟩) (b ⟨i.val / 2 + 1, by omega⟩) := by
  split_ifs with hi <;> simp [pointOpenPiece, hi, MarkedInterval.carrier_eq]

theorem pointOpenPiece_subset_parent {n : ℕ} (b : Fin (n + 1) → ℝ)
    (hb : StrictMono b) (i : Fin (2 * n)) :
    (pointOpenPiece b i).carrier ⊆
      Set.Ico (b ⟨i.val / 2, by omega⟩) (b ⟨i.val / 2 + 1, by omega⟩) := by
  rw [pointOpenPiece_carrier]
  split_ifs with hi
  · rintro x rfl
    exact ⟨le_rfl, hb (by change i.val / 2 < i.val / 2 + 1; omega)⟩
  · intro x hx
    exact ⟨hx.1.le, hx.2⟩

def pointOpenPartition {n : ℕ} (b : Fin (n + 1) → ℝ) (hb : StrictMono b) :
    IntervalPartition (Set.Ico (b ⟨0, by omega⟩) (b ⟨n, by omega⟩)) where
  size := 2 * n
  interval := pointOpenPiece b
  nonempty := by
    intro i
    rw [pointOpenPiece_carrier]
    split_ifs
    · exact Set.singleton_nonempty _
    · exact Set.nonempty_Ioo.mpr (hb (by change i.val / 2 < i.val / 2 + 1; omega))
  pairwiseDisjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hxi := pointOpenPiece_subset_parent b hb i hx
    have hxj := pointOpenPiece_subset_parent b hb j hy
    by_cases hp : i.val / 2 = j.val / 2
    · rw [pointOpenPiece_carrier] at hx hy
      have hbEq : b ⟨i.val / 2, by omega⟩ = b ⟨j.val / 2, by omega⟩ :=
        congrArg b (Fin.ext hp)
      have hv : i.val ≠ j.val := fun he => hij (Fin.ext he)
      by_cases hi : i.val % 2 = 0
      · have hj : j.val % 2 ≠ 0 := by omega
        simp only [if_pos hi, Set.mem_singleton_iff] at hx
        simp only [if_neg hj, Set.mem_Ioo] at hy
        exact (ne_of_gt hy.1) (hx.trans hbEq)
      · have hj : j.val % 2 = 0 := by omega
        simp only [if_neg hi, Set.mem_Ioo] at hx
        simp only [if_pos hj, Set.mem_singleton_iff] at hy
        exact (ne_of_gt hx.1) (hy.trans hbEq.symm)
    · rcases lt_or_gt_of_ne hp with hp | hp
      · have ho := hb.monotone (show (⟨i.val / 2 + 1, by omega⟩ : Fin (n + 1)) ≤
            ⟨j.val / 2, by omega⟩ by change i.val / 2 + 1 ≤ j.val / 2; omega)
        exact (not_lt_of_ge (ho.trans hxj.1)) hxi.2
      · have ho := hb.monotone (show (⟨j.val / 2 + 1, by omega⟩ : Fin (n + 1)) ≤
            ⟨i.val / 2, by omega⟩ by change j.val / 2 + 1 ≤ i.val / 2; omega)
        exact (not_lt_of_ge (ho.trans hxi.1)) hxj.2
  covers := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      have hx := pointOpenPiece_subset_parent b hb i hi
      exact ⟨(hb.monotone (by change 0 ≤ i.val / 2; omega)).trans hx.1,
        hx.2.trans_le (hb.monotone (by change i.val / 2 + 1 ≤ n; omega))⟩
    · intro hx
      obtain ⟨i, hlo, hhi⟩ := exists_boundary_piece b hx
      by_cases he : x = b ⟨i.val, by omega⟩
      · refine ⟨⟨2 * i.val, by omega⟩, ?_⟩
        rw [pointOpenPiece_carrier]
        simpa using he
      · refine ⟨⟨2 * i.val + 1, by omega⟩, ?_⟩
        rw [pointOpenPiece_carrier]
        have hl : b ⟨i.val, by omega⟩ < x := lt_of_le_of_ne hlo (Ne.symm he)
        have hd : (2 * i.val + 1) / 2 = i.val := by omega
        simpa [hd] using And.intro hl hhi
  ordered := by
    intro i j hij
    have hv : i.val < j.val := hij
    unfold pointOpenPiece
    split_ifs with hi hj
    all_goals
      apply hb.monotone
      simp only [Fin.le_iff_val_le_val]
      omega

theorem pointOpenPartition_finer {n : ℕ} (b : Fin (n + 1) → ℝ) (hb : StrictMono b) :
    (pointOpenPartition b hb).FinerThan (ofBoundaries b hb) := by
  intro i
  change Fin (2 * n) at i
  refine ⟨⟨i.val / 2, by have := i.isLt; change i.val / 2 < n; omega⟩, ?_⟩
  simpa only [pointOpenPartition, ofBoundaries, MarkedInterval.carrier_eq] using
    pointOpenPiece_subset_parent b hb i

@[simp] theorem pointOpenPiece_leftMarker {n : ℕ}
    (b : Fin (n + 1) → ℝ) (i : Fin (2 * n)) :
    (pointOpenPiece b i).leftBoundary = if i.val % 2 = 0 then ● else ○ := by
  unfold pointOpenPiece
  split_ifs <;> rfl

end STLTableau.IntervalPartition
