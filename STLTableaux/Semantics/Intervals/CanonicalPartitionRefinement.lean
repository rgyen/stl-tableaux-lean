import STLTableaux.Automata.Translation.CanonicalTableauForward
import STLTableaux.Semantics.Partitions.PointOpenPartition
import STLTableaux.Semantics.Stability.StabilityRefinement

/-! Every finite interval partition admits a refinement of the two boundary
forms used by the translation. Isolating all endpoints gives a simple
refinement, including at time zero. -/
namespace STLTableau.IntervalPartition
open STLTableau.Section4

theorem exists_canonical_refinement {Var : Type*} (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) :
    ∃ R : IntervalPartition σ.domain, R.FinerThan P ∧ Tableau.CanonicalBoundaryForms σ R := by
  classical
  let S := insert 0 (insert σ.horizon ((Finset.univ.image fun i => (P.interval i).left) ∪
    (Finset.univ.image fun i => (P.interval i).right)))
  have hcard : 0 < S.card := Finset.card_pos.mpr ⟨0, Finset.mem_insert_self _ _⟩
  let n := S.card - 1
  have card : S.card = n + 1 := by dsimp [n]; omega
  let b := S.orderEmbOfFin card
  have mono : StrictMono b := b.strictMono
  have range : Set.range b = (S : Set ℝ) := Finset.range_orderEmbOfFin S card
  have mem (t : ℝ) : t ∈ S → 0 ≤ t ∧ t ≤ σ.horizon := by
    intro ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact ⟨le_rfl,σ.horizon_pos.le⟩
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact ⟨σ.horizon_pos.le,le_rfl⟩
    rcases Finset.mem_union.mp ht with ht | ht
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ht
      exact ⟨(Tableau.pieceEntry σ P i).property.1,
        (P.left_le_right i).trans (P.right_le_domain_right i)⟩
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ht
      exact ⟨(Tableau.pieceEntry σ P i).property.1.trans (P.left_le_right i),
        P.right_le_domain_right i⟩
  have left (i : Fin P.size) : ∃ k, b k = (P.interval i).left := by
    change (P.interval i).left ∈ Set.range b
    rw [range]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)))
  have right (i : Fin P.size) : ∃ k, b k = (P.interval i).right := by
    change (P.interval i).right ∈ Set.range b
    rw [range]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)))
  have first : b 0 = 0 := by
    have hx : 0 ∈ Set.range b := range.symm ▸ Finset.mem_insert_self _ _
    obtain ⟨i,hi⟩ := hx
    have member : b 0 ∈ (S : Set ℝ) := range ▸ (show b 0 ∈ Set.range b from ⟨0,rfl⟩)
    exact le_antisymm (hi ▸ mono.monotone (Fin.zero_le i)) (mem _ member).1
  have last : b (Fin.last n) = σ.horizon := by
    have hx : σ.horizon ∈ Set.range b := range.symm ▸
      Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    obtain ⟨i,hi⟩ := hx
    have member : b (Fin.last n) ∈ (S : Set ℝ) := range ▸
      (show b (Fin.last n) ∈ Set.range b from ⟨Fin.last n,rfl⟩)
    exact le_antisymm (mem _ member).2 (hi ▸ mono.monotone (Fin.le_last i))
  let R : IntervalPartition σ.domain := { pointOpenPartition b mono with
    covers := by
      rw [(pointOpenPartition b mono).covers]
      change Set.Ico (b 0) (b (Fin.last n)) = Set.Ico 0 σ.horizon
      rw [first,last] }
  refine ⟨R,?_,?_⟩
  · intro i
    change Fin (2*n) at i
    change ∃ j : Fin P.size, (pointOpenPiece b i).carrier ⊆ (P.interval j).carrier
    obtain ⟨x,hx⟩ := R.nonempty i
    have inDomain : x ∈ σ.domain := by
      rw [← R.covers]
      exact Set.mem_iUnion.mpr ⟨i,hx⟩
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (P.covers.symm ▸ inDomain)
    refine ⟨j,?_⟩
    change x ∈ (pointOpenPiece b i).carrier at hx
    rw [pointOpenPiece_carrier] at hx ⊢
    split_ifs at hx ⊢ with even
    · intro y hy
      exact ((Set.mem_singleton_iff.mp hy).trans (Set.mem_singleton_iff.mp hx).symm) ▸ hj
    · let k : Fin (n+1) := ⟨i.val/2, by have := i.isLt; omega⟩
      let k' : Fin (n+1) := ⟨i.val/2+1, by have := i.isLt; omega⟩
      obtain ⟨a,ha⟩ := left j
      obtain ⟨c,hc⟩ := right j
      have hla : a ≤ k := by
        by_contra! he
        have hh : k' ≤ a := by change i.val/2 < a.val at he; change i.val/2+1 ≤ a.val; omega
        exact (not_lt_of_ge ((mono.monotone hh).trans (ha ▸ MarkedInterval.left_le_of_mem hj))) hx.2
      have hrc : k' ≤ c := by
        by_contra! he
        have hh : c ≤ k := by change c.val < i.val/2+1 at he; change c.val ≤ i.val/2; omega
        exact (not_lt_of_ge ((hc ▸ MarkedInterval.le_right_of_mem hj).trans (mono.monotone hh))) hx.1
      intro y hy
      exact ⟨Or.inl ((ha ▸ mono.monotone hla).trans_lt hy.1),
        Or.inl (hy.2.trans_le (hc ▸ mono.monotone hrc))⟩
  · intro i
    have size : R.size = 2*n := rfl
    let j : Fin (2*n) := ⟨i.val,by have := i.isLt; omega⟩
    let k : Fin (2*n) := ⟨i.val+1,by have := i.isLt; omega⟩
    change (pointOpenPiece b k).leftBoundary =
      if (pointOpenPiece b j).left = (pointOpenPiece b j).right then ○ else ●
    rw [pointOpenPiece_leftMarker]
    by_cases even : j.val % 2 = 0
    · have odd : k.val % 2 ≠ 0 := by dsimp [j,k] at *; omega
      rw [if_neg odd]
      simp [pointOpenPiece,even]
    · have odd : k.val % 2 = 0 := by dsimp [j,k] at *; omega
      rw [if_pos odd]
      have distinct : b ⟨j.val/2,by have := j.isLt; omega⟩ ≠
          b ⟨j.val/2+1,by have := j.isLt; omega⟩ := (mono (by simp)).ne
      simp [pointOpenPiece,even,distinct]

end STLTableau.IntervalPartition
