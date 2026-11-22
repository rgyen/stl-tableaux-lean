import STLTableaux.Semantics.Partitions.BoundaryPartition
import Mathlib.Data.Finset.Sort

/-! Common finite time boundaries, using mathlib's ordered enumeration of a
finset. This module contains no automaton or formula hypotheses. -/
namespace STLTableau

/-- A refinement includes every old boundary and has the same endpoints.
Strict monotonicity is stated separately for both boundary maps. -/
structure RefinesBoundaries {n k : ℕ} (b : Fin (n + 1) → ℝ)
    (c : Fin (k + 1) → ℝ) : Prop where
  first : c 0 = b 0
  last : c (Fin.last k) = b (Fin.last n)
  includes : ∀ i, ∃ j, c j = b i

theorem exists_common_time_boundaries {n m : ℕ}
    (b : Fin (n + 1) → ℝ) (c : Fin (m + 1) → ℝ)
    (hb : StrictMono b) (hc : StrictMono c)
    (first : b 0 = c 0) (last : b (Fin.last n) = c (Fin.last m)) :
    ∃ (k : ℕ) (d : Fin (k + 1) → ℝ), StrictMono d ∧
      RefinesBoundaries b d ∧ RefinesBoundaries c d ∧
      Set.range d = Set.range b ∪ Set.range c := by
  classical
  let s := Finset.univ.image b ∪ Finset.univ.image c
  have positive : 0 < s.card := Finset.card_pos.mpr
    ⟨b 0, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)⟩
  let k := s.card - 1
  have card : s.card = k + 1 := by dsimp [k]; omega
  let d : Fin (k + 1) → ℝ := s.orderEmbOfFin card
  have hd : StrictMono d := (s.orderEmbOfFin card).strictMono
  have range : Set.range d = Set.range b ∪ Set.range c := by
    change Set.range (s.orderEmbOfFin card) = _
    rw [Finset.range_orderEmbOfFin]
    ext x
    simp [s]
  have left : ∀ i, ∃ j, d j = b i := by
    intro i
    have member : b i ∈ Set.range b ∪ Set.range c := Or.inl ⟨i, rfl⟩
    rw [← range] at member
    exact member
  have right : ∀ i, ∃ j, d j = c i := by
    intro i
    have member : c i ∈ Set.range b ∪ Set.range c := Or.inr ⟨i, rfl⟩
    rw [← range] at member
    exact member
  have start : d 0 = b 0 := by
    apply le_antisymm
    · obtain ⟨j, hj⟩ := left 0
      exact hj ▸ hd.monotone (Fin.zero_le j)
    · have member : d 0 ∈ Set.range b ∪ Set.range c := range ▸ ⟨0, rfl⟩
      rcases member with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact hi ▸ hb.monotone (Fin.zero_le i)
      · rw [first]
        exact hi ▸ hc.monotone (Fin.zero_le i)
  have finish : d (Fin.last k) = b (Fin.last n) := by
    apply le_antisymm
    · have member : d (Fin.last k) ∈ Set.range b ∪ Set.range c :=
        range ▸ ⟨Fin.last k, rfl⟩
      rcases member with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact hi ▸ hb.monotone (Fin.le_last i)
      · rw [last]
        exact hi ▸ hc.monotone (Fin.le_last i)
    · obtain ⟨j, hj⟩ := left (Fin.last n)
      exact hj ▸ hd.monotone (Fin.le_last j)
  exact ⟨k, d, hd, ⟨start, finish, left⟩,
    ⟨start.trans first, finish.trans last, right⟩, range⟩

namespace RefinesBoundaries
variable {n k : ℕ} {b : Fin (n + 1) → ℝ} {c : Fin (k + 1) → ℝ}
variable (r : RefinesBoundaries b c) (hb : StrictMono b) (hc : StrictMono c)
include r hc

theorem exists_cell (j : Fin k) :
    ∃ i : Fin n, b i.castSucc ≤ c j.castSucc ∧ c j.castSucc < b i.succ := by
  apply IntervalPartition.exists_boundary_piece b
  constructor
  · change b 0 ≤ c j.castSucc
    rw [← r.first]
    exact hc.monotone (Fin.zero_le _)
  · change c j.castSucc < b (Fin.last n)
    rw [← r.last]
    exact hc (by change j.val < k; exact j.isLt)

noncomputable def cell (j : Fin k) : Fin n := (r.exists_cell hc j).choose

theorem cell_left (j : Fin k) : b (r.cell hc j).castSucc ≤ c j.castSucc :=
  (r.exists_cell hc j).choose_spec.1

theorem cell_left_lt_end (j : Fin k) : c j.castSucc < b (r.cell hc j).succ :=
  (r.exists_cell hc j).choose_spec.2

/-- No old boundary lies strictly inside one adjacent refined pair. -/
theorem cell_right (j : Fin k) : c j.succ ≤ b (r.cell hc j).succ := by
  obtain ⟨l, hl⟩ := r.includes (r.cell hc j).succ
  have earlier : j.castSucc < l := hc.lt_iff_lt.mp (hl.symm ▸ r.cell_left_lt_end hc j)
  exact hl ▸ hc.monotone (by change j.val + 1 ≤ l.val; exact earlier)

include hb in
theorem cell_eq (j : Fin k) (i : Fin n)
    (lower : b i.castSucc ≤ c j.castSucc) (upper : c j.castSucc < b i.succ) :
    r.cell hc j = i := by
  have a := hb.lt_iff_lt.mp ((r.cell_left hc j).trans_lt upper)
  have z := hb.lt_iff_lt.mp (lower.trans_lt (r.cell_left_lt_end hc j))
  apply Fin.ext
  change (r.cell hc j).val < i.val + 1 at a
  change i.val < (r.cell hc j).val + 1 at z
  omega

include hb in
/-- Every old closed flow cell is covered by refined cells belonging to it,
including its right endpoint rather than assigning it to the next flow. -/
theorem covers_old_cell (i : Fin n) {t : ℝ}
    (inside : b i.castSucc ≤ t ∧ t ≤ b i.succ) :
    ∃ j : Fin k, r.cell hc j = i ∧ c j.castSucc ≤ t ∧ t ≤ c j.succ := by
  obtain ⟨a, ha⟩ := r.includes i.castSucc
  obtain ⟨z, hz⟩ := r.includes i.succ
  have az : a < z := hc.lt_iff_lt.mp (by rw [ha, hz]; exact hb (by simp))
  by_cases before : t < b i.succ
  · have global : t ∈ Set.Ico (c 0) (c (Fin.last k)) := by
      constructor
      · rw [r.first]
        exact (hb.monotone (Fin.zero_le _)).trans inside.1
      · rw [r.last]
        exact before.trans_le (hb.monotone (Fin.le_last _))
    obtain ⟨j, lower, upper⟩ := IntervalPartition.exists_boundary_piece c global
    have start : a ≤ j.castSucc := by
      by_contra notle
      have earlier : j.succ ≤ a := by
        change j.val + 1 ≤ a.val
        have h := lt_of_not_ge notle
        exact h
      have bound := hc.monotone earlier
      rw [ha] at bound
      exact (not_lt_of_ge (bound.trans inside.1)) upper
    have lowerOld : b i.castSucc ≤ c j.castSucc := ha ▸ hc.monotone start
    exact ⟨j, r.cell_eq hb hc j i lowerOld (lower.trans_lt before), lower, upper.le⟩
  · have atEnd : t = b i.succ := le_antisymm inside.2 (le_of_not_gt before)
    have zpos : 0 < z.val := by change a.val < z.val at az; omega
    let j : Fin k := ⟨z.val - 1, by have := z.isLt; omega⟩
    have endIndex : j.succ = z := Fin.ext (by dsimp [j]; omega)
    have lowerOld : b i.castSucc ≤ c j.castSucc := by
      rw [← ha]
      apply hc.monotone
      change a.val ≤ z.val - 1
      change a.val < z.val at az
      omega
    have upperOld : c j.castSucc < b i.succ := by
      rw [← hz, ← endIndex]
      exact hc (by simp)
    refine ⟨j, r.cell_eq hb hc j i lowerOld upperOld, ?_, ?_⟩
    · exact upperOld.le.trans_eq atEnd.symm
    · exact (atEnd.trans hz.symm).trans (congrArg c endIndex.symm) |>.le

include hb in
theorem cell_first (hk : 0 < k) : (r.cell hc ⟨0, hk⟩).val = 0 := by
  have lower := r.cell_left hc ⟨0, hk⟩
  change b (r.cell hc ⟨0, hk⟩).castSucc ≤ c 0 at lower
  rw [r.first] at lower
  have index := hb.le_iff_le.mp lower
  change (r.cell hc ⟨0, hk⟩).val ≤ 0 at index
  omega

include hb in
theorem cell_last (hk : 0 < k) : (r.cell hc ⟨k - 1, by omega⟩).val + 1 = n := by
  have upper := r.cell_right hc ⟨k - 1, by omega⟩
  have time : (⟨k - 1, by omega⟩ : Fin k).succ = Fin.last k := Fin.ext (by simp; omega)
  rw [time, r.last] at upper
  have index := hb.le_iff_le.mp upper
  have bound := (r.cell hc ⟨k - 1, by omega⟩).isLt
  change n ≤ (r.cell hc ⟨k - 1, by omega⟩).val + 1 at index
  omega

include hb in
/-- Consecutive refined cells either remain in one old flow or cross its
original boundary. No original jump boundary is skipped. -/
theorem cell_next (j : Fin k) (hj : j.val + 1 < k) :
    r.cell hc ⟨j.val + 1, hj⟩ = r.cell hc j ∨
      ((r.cell hc ⟨j.val + 1, hj⟩).val = (r.cell hc j).val + 1 ∧
        c j.succ = b (r.cell hc j).succ) := by
  let i := r.cell hc j
  let l := r.cell hc ⟨j.val + 1, hj⟩
  have lower := r.cell_left hc ⟨j.val + 1, hj⟩
  have upper := r.cell_right hc j
  have order : l.castSucc ≤ i.succ := hb.le_iff_le.mp (lower.trans upper)
  have strict : i.castSucc < l.succ := hb.lt_iff_lt.mp
    ((r.cell_left hc j).trans_lt ((hc (show j.castSucc < j.succ by simp)).trans
      (r.cell_left_lt_end hc ⟨j.val + 1, hj⟩)))
  by_cases same : l = i
  · exact Or.inl same
  · have next : l.val = i.val + 1 := by
      have different := Fin.val_ne_of_ne same
      change l.val ≤ i.val + 1 at order
      change i.val < l.val + 1 at strict
      omega
    refine Or.inr ⟨next, le_antisymm upper ?_⟩
    have equal : l.castSucc = i.succ := Fin.ext next
    exact equal ▸ lower

run_elab do
  for name in #[``exists_common_time_boundaries, ``exists_cell, ``cell_right,
      ``cell_eq, ``covers_old_cell,
      ``cell_first, ``cell_last, ``cell_next] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name} uses unexpected axiom {ax}"

end RefinesBoundaries
end STLTableau
