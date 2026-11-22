/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Semantics.Partitions.Partition
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Prod.Lex

/-! Marker-aware interval intersections and finite common refinements. -/

namespace STLTableau
namespace MarkedInterval

/-- Intersection retains the more restrictive endpoint, including its marker. -/
noncomputable def inter (I J : MarkedInterval) : MarkedInterval := by
  classical
  exact ⟨max I.left J.left, min I.right J.right,
    if I.left < J.left then J.leftBoundary else
      if J.left < I.left then I.leftBoundary else Marker.conj I.leftBoundary J.leftBoundary,
    if I.right < J.right then I.rightBoundary else
      if J.right < I.right then J.rightBoundary else Marker.conj I.rightBoundary J.rightBoundary⟩

@[simp] theorem carrier_inter (I J : MarkedInterval) :
    (inter I J).carrier = I.carrier ∩ J.carrier := by
  classical
  have hleft (a c x : ℝ) (l m : Marker) :
      (max a c < x ∨ (max a c = x ∧
        (if a < c then m else if c < a then l else Marker.conj l m).Includes)) ↔
      (a < x ∨ (a = x ∧ l.Includes)) ∧ (c < x ∨ (c = x ∧ m.Includes)) := by
    rcases lt_trichotomy a c with h | h | h <;>
      cases l <;> cases m <;>
      simp_all [Marker.Includes, Marker.conj, max_def] <;> grind
  have hright (b d x : ℝ) (r n : Marker) :
      (x < min b d ∨ (x = min b d ∧
        (if b < d then r else if d < b then n else Marker.conj r n).Includes)) ↔
      (x < b ∨ (x = b ∧ r.Includes)) ∧ (x < d ∨ (x = d ∧ n.Includes)) := by
    rcases lt_trichotomy b d with h | h | h <;>
      cases r <;> cases n <;>
      simp_all [Marker.Includes, Marker.conj, min_def] <;> grind
  ext x
  rcases I with ⟨a,b,l,r⟩
  rcases J with ⟨c,d,m,n⟩
  simp only [Set.mem_inter_iff, mem_carrier, mem_iff, inter]
  rw [hleft, hright]
  tauto

end MarkedInterval

namespace IntervalPartition
open scoped STL

/-- Nonempty pairwise intersections form the coarsest common refinement.
Any partition finer than both inputs is finer than this one. -/
theorem exists_common_refinement {domain : Set ℝ} (P Q : IntervalPartition domain) :
    ∃ R : IntervalPartition domain, R ⊑ P ∧ R ⊑ Q ∧
      ∀ S : IntervalPartition domain, S ⊑ P → S ⊑ Q → S ⊑ R := by
  classical
  let T := {p : Fin P.size ×ₗ Fin Q.size //
    ((P.interval (ofLex p).1).carrier ∩ (Q.interval (ofLex p).2).carrier).Nonempty}
  let e := monoEquivOfFin T rfl
  let f : T → MarkedInterval := fun p =>
    MarkedInterval.inter (P.interval (ofLex p.val).1) (Q.interval (ofLex p.val).2)
  have hf (p : T) : (f p).carrier =
      (P.interval (ofLex p.val).1).carrier ∩ (Q.interval (ofLex p.val).2).carrier :=
    MarkedInterval.carrier_inter _ _
  let R : IntervalPartition domain := {
    size := Fintype.card T
    interval := fun i => f (e i)
    nonempty := fun i => (hf (e i)).symm ▸ (e i).property
    pairwiseDisjoint := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro x hxi hxj
      rw [hf] at hxi hxj
      have hne : (e i).val ≠ (e j).val := by
        intro heq
        exact hij (e.injective (Subtype.ext heq))
      by_cases hfirst : (ofLex (e i).val).1 = (ofLex (e j).val).1
      · have hsecond : (ofLex (e i).val).2 ≠ (ofLex (e j).val).2 := by
          intro hsecond
          exact hne (Prod.ext hfirst hsecond)
        exact Set.disjoint_left.mp (Q.pairwiseDisjoint hsecond) hxi.2 hxj.2
      · exact Set.disjoint_left.mp (P.pairwiseDisjoint hfirst) hxi.1 hxj.1
    covers := by
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨i, hx⟩
        have hp := (hf (e i) ▸ hx).1
        rw [← P.covers]
        exact Set.mem_iUnion.mpr ⟨_, hp⟩
      · intro hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (P.covers.symm ▸ hx)
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (Q.covers.symm ▸ hx)
        let p : T := ⟨toLex (i,j), x, hi, hj⟩
        refine ⟨e.symm p, ?_⟩
        rw [e.apply_symm_apply, hf]
        exact ⟨hi,hj⟩
    ordered := by
      intro i j hij
      have hlt := e.strictMono hij
      have hlex : (e i).val < (e j).val := hlt
      rcases Prod.Lex.lt_iff.mp hlex with h | ⟨_,h⟩
      · exact (min_le_left _ _).trans ((P.ordered h).trans (le_max_left _ _))
      · exact (min_le_right _ _).trans ((Q.ordered h).trans (le_max_right _ _)) }
  refine ⟨R, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(ofLex (e i).val).1, fun x hx => (hf (e i) ▸ hx).1⟩
  · intro i
    exact ⟨(ofLex (e i).val).2, fun x hx => (hf (e i) ▸ hx).2⟩
  · intro S hSP hSQ k
    obtain ⟨i, hi⟩ := hSP k
    obtain ⟨j, hj⟩ := hSQ k
    obtain ⟨x, hx⟩ := S.nonempty k
    let p : T := ⟨toLex (i,j), x, hi hx, hj hx⟩
    refine ⟨e.symm p, ?_⟩
    change (S.interval k).carrier ⊆ (f (e (e.symm p))).carrier
    rw [e.apply_symm_apply, hf]
    exact fun y hy => ⟨hi hy,hj hy⟩

end IntervalPartition
end STLTableau
