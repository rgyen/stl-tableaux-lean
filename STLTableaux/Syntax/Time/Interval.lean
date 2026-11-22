/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import Mathlib

/-!
# Marked real intervals

Boundary markers and marked interval operations from Appendix A.1.
A closed marker includes its endpoint and an open marker excludes it.
-/

namespace STLTableau

/-- Whether an endpoint of an interval is included. -/
inductive Marker where
  | open
  | closed
  deriving DecidableEq, Repr

/-- Notation for open and closed boundary markers. -/
notation "○" => STLTableau.Marker.open
notation "●" => STLTableau.Marker.closed

namespace Marker

/-- The proposition represented by a boundary marker. -/
def Includes : Marker → Prop
  | .open => False
  | .closed => True

instance : ∀ b : Marker, Decidable b.Includes
  | .open => isFalse id
  | .closed => isTrue trivial

@[simp] theorem includes_open : (○ : Marker).Includes ↔ False := Iff.rfl
@[simp] theorem includes_closed : (● : Marker).Includes ↔ True := Iff.rfl

/-- Logical negation of a boundary marker. -/
def complement : Marker → Marker
  | .open => .closed
  | .closed => .open

/-- Notation for marker negation. -/
scoped[STL] prefix:max "¬ₘ " => STLTableau.Marker.complement

open scoped STL

@[simp] theorem complement_open : ¬ₘ ○ = ● := rfl
@[simp] theorem complement_closed : ¬ₘ ● = ○ := rfl

@[simp] theorem complement_complement (b : Marker) : ¬ₘ (¬ₘ b) = b := by
  cases b <;> rfl

@[simp] theorem includes_complement (b : Marker) :
    (¬ₘ b).Includes ↔ ¬b.Includes := by
  cases b <;> simp [complement, Includes]

/-- Conjunction of boundary markers: closed exactly when both inputs are closed. -/
def conj : Marker → Marker → Marker
  | .closed, .closed => .closed
  | _, _ => .open

@[simp] theorem includes_conj (a b : Marker) : (conj a b).Includes ↔ a.Includes ∧ b.Includes := by
  cases a <;> cases b <;> simp [conj, Includes]

/-- Disjunction of markers: a touching union includes the joint endpoint
when either of its two intervals includes it. -/
def disj : Marker → Marker → Marker
  | .open, .open => .open
  | _, _ => .closed

@[simp] theorem includes_disj (a b : Marker) :
    (disj a b).Includes ↔ a.Includes ∨ b.Includes := by
  cases a <;> cases b <;> simp [disj, Includes]

/-- Marker for implication: equality is allowed unless a closed source endpoint
must be contained in an open target endpoint. -/
def imp : Marker → Marker → Marker
  | .closed, .open => .open
  | _, _ => .closed

@[simp] theorem includes_imp (a b : Marker) : (imp a b).Includes ↔ (a.Includes → b.Includes) := by
  cases a <;> cases b <;> simp [imp, Includes]

/-- The marker for `a ∨ ¬b`, where a closed marker represents truth. -/
def orNot : Marker → Marker → Marker
  | .open, .closed => .open
  | _, _ => .closed

@[simp] theorem includes_orNot (a b : Marker) :
    (orNot a b).Includes ↔ (a.Includes ∨ ¬b.Includes) := by
  cases a <;> cases b <;> simp [orNot, Includes]

/-- Marker corresponding to `¬a ∨ ¬b`: equality separates two adjacent
intervals unless both of them include the common endpoint. -/
def notConj : Marker → Marker → Marker
  | .closed, .closed => .open
  | _, _ => .closed

@[simp] theorem includes_notConj (a b : Marker) :
    (notConj a b).Includes ↔ (¬a.Includes ∨ ¬b.Includes) := by
  cases a <;> cases b <;> simp [notConj, Includes]

end Marker

/-- Strict inequality, or equality when the marker is closed. -/
def MarkedLT (b : Marker) (x y : ℝ) : Prop :=
  x < y ∨ (x = y ∧ b.Includes)

/-- Notation for comparison with an endpoint marker. -/
scoped[STL] notation:50 x:51 " <[" b "] " y:51 => STLTableau.MarkedLT b x y

open scoped STL

@[simp] theorem lt_or_eq_iff_le_real (x y : ℝ) : x < y ∨ x = y ↔ x ≤ y :=
  ⟨fun h => h.elim le_of_lt le_of_eq, lt_or_eq_of_le⟩

@[simp] theorem markedLT_open (x y : ℝ) : x <[○] y ↔ x < y := by
  simp [MarkedLT]

@[simp] theorem markedLT_closed (x y : ℝ) : x <[●] y ↔ x ≤ y := by
  simp only [MarkedLT, Marker.includes_closed, and_true]
  constructor
  · rintro (h | rfl)
    · exact h.le
    · exact le_rfl
  · exact lt_or_eq_of_le

/-- An interval with independently open or closed endpoints. -/
structure MarkedInterval where
  left : ℝ
  right : ℝ
  leftBoundary : Marker
  rightBoundary : Marker

namespace MarkedInterval

/-- Membership in a marked interval. -/
def Mem (I : MarkedInterval) (x : ℝ) : Prop :=
  (I.left < x ∨ (I.left = x ∧ I.leftBoundary.Includes)) ∧
    (x < I.right ∨ (x = I.right ∧ I.rightBoundary.Includes))

instance : Membership ℝ MarkedInterval := ⟨fun I x => I.Mem x⟩

/-- The set denoted by a marked interval. -/
def carrier (I : MarkedInterval) : Set ℝ := {x | x ∈ I}

@[simp] theorem mem_carrier {I : MarkedInterval} {x : ℝ} : x ∈ I.carrier ↔ x ∈ I := Iff.rfl

theorem mem_iff {I : MarkedInterval} {x : ℝ} :
    x ∈ I ↔
      (I.left < x ∨ (I.left = x ∧ I.leftBoundary.Includes)) ∧
      (x < I.right ∨ (x = I.right ∧ I.rightBoundary.Includes)) :=
  Iff.rfl

/-- A marked interval agrees with the corresponding standard Mathlib interval. -/
theorem carrier_eq (I : MarkedInterval) :
    I.carrier = match I.leftBoundary, I.rightBoundary with
      | .open, .open => Set.Ioo I.left I.right
      | .open, .closed => Set.Ioc I.left I.right
      | .closed, .open => Set.Ico I.left I.right
      | .closed, .closed => Set.Icc I.left I.right := by
  rcases I with ⟨left, right, lb, rb⟩
  ext x
  change Mem ⟨left, right, lb, rb⟩ x ↔ _
  cases lb <;> cases rb <;> simp [Mem, Marker.Includes]

/-- Lemma A.2 (nonemptiness). A singleton requires both markers to be closed. -/
theorem nonempty_iff (I : MarkedInterval) :
    I.carrier.Nonempty ↔
      I.left <[Marker.conj I.leftBoundary I.rightBoundary] I.right := by
  constructor
  · rintro ⟨x, (hleft | ⟨hleft, hLB⟩), (hright | ⟨hright, hRB⟩)⟩
    · exact Or.inl (hleft.trans hright)
    · exact Or.inl (hright ▸ hleft)
    · exact Or.inl (hleft ▸ hright)
    · right
      refine ⟨hleft.trans hright, ?_⟩
      exact (Marker.includes_conj _ _).2 ⟨hLB, hRB⟩
  · rintro (hlt | ⟨heq, hboundaries⟩)
    · refine ⟨(I.left + I.right) / 2, ?_⟩
      constructor <;> left <;> linarith
    · refine ⟨I.left, ?_⟩
      have hb := (Marker.includes_conj _ _).1 hboundaries
      constructor
      · exact Or.inr ⟨rfl, hb.1⟩
      · exact Or.inr ⟨heq, hb.2⟩

theorem left_le_of_mem {I : MarkedInterval} {x : ℝ} (hx : x ∈ I) : I.left ≤ x := by
  rcases hx.1 with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

theorem le_right_of_mem {I : MarkedInterval} {x : ℝ} (hx : x ∈ I) : x ≤ I.right := by
  rcases hx.2 with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

theorem left_mem (I : MarkedInterval) (hne : I.carrier.Nonempty)
    (hclosed : I.leftBoundary.Includes) : I.left ∈ I := by
  have hv := (nonempty_iff I).1 hne
  rcases hv with hlt | ⟨heq, hmarkers⟩
  · exact ⟨Or.inr ⟨rfl, hclosed⟩, Or.inl hlt⟩
  · have hm := (Marker.includes_conj _ _).1 hmarkers
    exact ⟨Or.inr ⟨rfl, hclosed⟩, Or.inr ⟨heq, hm.2⟩⟩

theorem right_mem (I : MarkedInterval) (hne : I.carrier.Nonempty)
    (hclosed : I.rightBoundary.Includes) : I.right ∈ I := by
  have hv := (nonempty_iff I).1 hne
  rcases hv with hlt | ⟨heq, hmarkers⟩
  · exact ⟨Or.inl hlt, Or.inr ⟨rfl, hclosed⟩⟩
  · have hm := (Marker.includes_conj _ _).1 hmarkers
    exact ⟨Or.inr ⟨heq, hm.1⟩, Or.inr ⟨rfl, hclosed⟩⟩

private theorem lower_le_of_subset {I₁ I₂ : MarkedInterval} (hne : I₁.carrier.Nonempty)
    (hsub : I₁.carrier ⊆ I₂.carrier) : I₂.left ≤ I₁.left := by
  by_cases hc : I₁.leftBoundary.Includes
  · exact left_le_of_mem (hsub (left_mem I₁ hne hc))
  · rcases hne with ⟨x, hx⟩
    by_contra hle
    have h₁ : I₁.left < x := by
      rcases hx.1 with h | ⟨_, hinc⟩
      · exact h
      · exact (hc hinc).elim
    have h₂ : I₁.left < I₂.left := lt_of_not_ge hle
    obtain ⟨y, hly, hymin⟩ := exists_between (lt_min h₁ h₂)
    have hyx : y < x := hymin.trans_le (min_le_left _ _)
    have hyt : y < I₂.left := hymin.trans_le (min_le_right _ _)
    have hyI₁ : y ∈ I₁ := by
      refine ⟨Or.inl hly, ?_⟩
      rcases hx.2 with h | ⟨h, hr⟩
      · exact Or.inl (hyx.trans h)
      · exact Or.inl (h ▸ hyx)
    exact hyt.not_ge (left_le_of_mem (hsub hyI₁))

private theorem upper_le_of_subset {I₁ I₂ : MarkedInterval} (hne : I₁.carrier.Nonempty)
    (hsub : I₁.carrier ⊆ I₂.carrier) : I₁.right ≤ I₂.right := by
  by_cases hc : I₁.rightBoundary.Includes
  · exact le_right_of_mem (hsub (right_mem I₁ hne hc))
  · rcases hne with ⟨x, hx⟩
    by_contra hle
    have h₁ : x < I₁.right := by
      rcases hx.2 with h | ⟨_, hinc⟩
      · exact h
      · exact (hc hinc).elim
    have h₂ : I₂.right < I₁.right := lt_of_not_ge hle
    obtain ⟨y, hmaxy, hyr⟩ := exists_between (max_lt h₁ h₂)
    have hxy : x < y := (le_max_left _ _).trans_lt hmaxy
    have hty : I₂.right < y := (le_max_right _ _).trans_lt hmaxy
    have hyI₁ : y ∈ I₁ := by
      refine ⟨?_, Or.inl hyr⟩
      rcases hx.1 with h | ⟨h, hl⟩
      · exact Or.inl (h.trans hxy)
      · exact Or.inl (h ▸ hxy)
    exact hty.not_ge (le_right_of_mem (hsub hyI₁))

/-- Lemma A.3(1) (interval inclusion). -/
theorem subset_iff {I₁ I₂ : MarkedInterval} (hne₁ : I₁.carrier.Nonempty) :
    I₁.carrier ⊆ I₂.carrier ↔
      I₂.left <[Marker.imp I₁.leftBoundary I₂.leftBoundary] I₁.left ∧
      I₁.right <[Marker.imp I₁.rightBoundary I₂.rightBoundary] I₂.right := by
  constructor
  · intro hsub
    have hl := lower_le_of_subset hne₁ hsub
    have hr := upper_le_of_subset hne₁ hsub
    constructor
    · rcases hl.lt_or_eq with hlt | heq
      · exact Or.inl hlt
      · right
        refine ⟨heq, (Marker.includes_imp _ _).2 fun hinc => ?_⟩
        have hm := (hsub (left_mem I₁ hne₁ hinc)).1
        rcases hm with h | ⟨_, hinc₂⟩
        · exact (h.ne heq).elim
        · exact hinc₂
    · rcases hr.lt_or_eq with hlt | heq
      · exact Or.inl hlt
      · right
        refine ⟨heq, (Marker.includes_imp _ _).2 fun hinc => ?_⟩
        have hm := (hsub (right_mem I₁ hne₁ hinc)).2
        rcases hm with h | ⟨_, hinc₂⟩
        · exact (h.ne heq).elim
        · exact hinc₂
  · rintro ⟨hl, hr⟩ x hx
    constructor
    · rcases hl with hlt | ⟨heq, himp⟩
      · exact Or.inl (hlt.trans_le (left_le_of_mem hx))
      · rcases hx.1 with hxlt | ⟨hxeq, hxinc⟩
        · exact Or.inl (heq ▸ hxlt)
        · exact Or.inr ⟨heq.trans hxeq, (Marker.includes_imp _ _).1 himp hxinc⟩
    · rcases hr with hlt | ⟨heq, himp⟩
      · exact Or.inl ((le_right_of_mem hx).trans_lt hlt)
      · rcases hx.2 with hxlt | ⟨hxeq, hxinc⟩
        · exact Or.inl (heq ▸ hxlt)
        · exact Or.inr ⟨hxeq.trans heq, (Marker.includes_imp _ _).1 himp hxinc⟩

/-- Lemma A.3(3) (nonempty intersection). The marker comparisons place the
left and right endpoints in the required order. -/
theorem inter_nonempty_of_markedLT {I₁ I₂ : MarkedInterval} (hne₂ : I₂.carrier.Nonempty)
    (hleft : I₁.left <[Marker.orNot I₁.leftBoundary I₂.leftBoundary] I₂.left)
    (hright : I₂.left <[Marker.conj I₁.rightBoundary I₂.leftBoundary] I₁.right) :
    (I₁.carrier ∩ I₂.carrier).Nonempty := by
  cases h₂l : I₂.leftBoundary
  · have h₂right : I₂.left < I₂.right := by
      rcases hne₂ with ⟨x, hx⟩
      have hlx : I₂.left < x := by
        rcases hx.1 with h | ⟨_, hm⟩
        · exact h
        · simp [Marker.Includes, h₂l] at hm
      exact hlx.trans_le (le_right_of_mem hx)
    have h₁right : I₂.left < I₁.right := by
      simpa [MarkedLT, Marker.conj, Marker.Includes, h₂l] using hright
    obtain ⟨x, h₂x, hxmin⟩ := exists_between (lt_min h₁right h₂right)
    refine ⟨x, ?_, ?_⟩
    · constructor
      · have hle : I₁.left ≤ I₂.left := by
          have h : I₁.left < I₂.left ∨ I₁.left = I₂.left := by
            simpa [MarkedLT, Marker.orNot, Marker.Includes, h₂l] using hleft
          exact h.elim le_of_lt le_of_eq
        exact Or.inl (hle.trans_lt h₂x)
      · exact Or.inl (hxmin.trans_le (min_le_left _ _))
    · constructor
      · exact Or.inl h₂x
      · exact Or.inl (hxmin.trans_le (min_le_right _ _))
  · refine ⟨I₂.left, ?_, left_mem I₂ hne₂ (by simp [Marker.Includes, h₂l])⟩
    constructor
    · rcases hleft with h | ⟨h, hm⟩
      · exact Or.inl h
      · refine Or.inr ⟨h, ?_⟩
        rcases (Marker.includes_orNot _ _).1 hm with hi | hn
        · exact hi
        · exact (hn (by simp [Marker.Includes, h₂l])).elim
    · rcases hright with h | ⟨h, hm⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, ((Marker.includes_conj _ _).1 hm).1⟩

/-- Lemma A.3(2) (disjoint intervals). -/
theorem disjoint_iff {I₁ I₂ : MarkedInterval}
    (hne₁ : I₁.carrier.Nonempty) (hne₂ : I₂.carrier.Nonempty) :
    Disjoint I₁.carrier I₂.carrier ↔
      I₁.right <[Marker.notConj I₁.rightBoundary I₂.leftBoundary] I₂.left ∨
      I₂.right <[Marker.notConj I₁.leftBoundary I₂.rightBoundary] I₁.left := by
  constructor
  · intro hd
    rcases lt_trichotomy I₁.right I₂.left with hlt | heq | hgt
    · exact Or.inl (Or.inl hlt)
    · by_cases hb : I₁.rightBoundary.Includes ∧ I₂.leftBoundary.Includes
      · have hm₁ := right_mem I₁ hne₁ hb.1
        have hm₂ := left_mem I₂ hne₂ hb.2
        exact (hd.notMem_of_mem_left hm₁ (heq ▸ hm₂)).elim
      · left
        exact Or.inr ⟨heq, (Marker.includes_notConj _ _).2 (not_and_or.mp hb)⟩
    · rcases lt_trichotomy I₂.right I₁.left with hlt | heq | hgt₂
      · exact Or.inr (Or.inl hlt)
      · by_cases hb : I₁.leftBoundary.Includes ∧ I₂.rightBoundary.Includes
        · have hm₁ := left_mem I₁ hne₁ hb.1
          have hm₂ := right_mem I₂ hne₂ hb.2
          exact (hd.notMem_of_mem_left hm₁ (heq ▸ hm₂)).elim
        · right
          exact Or.inr ⟨heq, (Marker.includes_notConj _ _).2 (not_and_or.mp hb)⟩
      · exfalso
        have hinter : (I₁.carrier ∩ I₂.carrier).Nonempty := by
          rcases lt_trichotomy I₁.left I₂.left with hleft | heq | hleft
          · exact inter_nonempty_of_markedLT hne₂ (Or.inl hleft) (Or.inl hgt)
          · by_cases h₂open : ¬I₂.leftBoundary.Includes
            · apply inter_nonempty_of_markedLT hne₂
              · exact Or.inr ⟨heq, (Marker.includes_orNot _ _).2 (Or.inr h₂open)⟩
              · exact Or.inl hgt
            · by_cases h₁closed : I₁.leftBoundary.Includes
              · apply inter_nonempty_of_markedLT hne₂
                · exact Or.inr ⟨heq, (Marker.includes_orNot _ _).2 (Or.inl h₁closed)⟩
                · exact Or.inl hgt
              · rw [Set.inter_comm]
                apply inter_nonempty_of_markedLT hne₁
                · exact Or.inr ⟨heq.symm,
                    (Marker.includes_orNot _ _).2 (Or.inr h₁closed)⟩
                · exact Or.inl hgt₂
          · rw [Set.inter_comm]
            exact inter_nonempty_of_markedLT hne₁ (Or.inl hleft) (Or.inl hgt₂)
        rcases hinter with ⟨x, hx₁, hx₂⟩
        exact hd.notMem_of_mem_left hx₁ hx₂
  · rintro (hsep | hsep)
    · rw [Set.disjoint_left]
      intro x hx₁ hx₂
      rcases hsep with hlt | ⟨heq, hm⟩
      · exact (not_lt_of_ge (le_right_of_mem hx₁)) (hlt.trans_le (left_le_of_mem hx₂))
      · have hxr : x = I₁.right := le_antisymm (le_right_of_mem hx₁)
          (heq ▸ left_le_of_mem hx₂)
        have hb₁ : I₁.rightBoundary.Includes := by
          rcases hx₁.2 with h | ⟨_, hb⟩
          · exact False.elim (lt_irrefl _ (hxr ▸ h))
          · exact hb
        have hb₂ : I₂.leftBoundary.Includes := by
          rcases hx₂.1 with h | ⟨_, hb⟩
          · exact False.elim (lt_irrefl _ ((hxr.trans heq).symm ▸ h))
          · exact hb
        exact ((Marker.includes_notConj _ _).1 hm).elim (fun h => h hb₁) (fun h => h hb₂)
    · rw [Set.disjoint_left]
      intro x hx₁ hx₂
      rcases hsep with hlt | ⟨heq, hm⟩
      · exact (not_lt_of_ge (le_right_of_mem hx₂)) (hlt.trans_le (left_le_of_mem hx₁))
      · have hxr : x = I₂.right := le_antisymm (le_right_of_mem hx₂)
          (heq ▸ left_le_of_mem hx₁)
        have hb₁ : I₁.leftBoundary.Includes := by
          rcases hx₁.1 with h | ⟨_, hb⟩
          · exact False.elim (lt_irrefl _ ((hxr.trans heq).symm ▸ h))
          · exact hb
        have hb₂ : I₂.rightBoundary.Includes := by
          rcases hx₂.2 with h | ⟨_, hb⟩
          · exact False.elim (lt_irrefl _ (hxr ▸ h))
          · exact hb
        exact ((Marker.includes_notConj _ _).1 hm).elim (fun h => h hb₁) (fun h => h hb₂)

/-- Splitting a marked interval at a strict interior point, using complementary
markers at the cut, preserves its carrier. -/
theorem carrier_union_split_interior (L C R : ℝ) (l m r : Marker)
    (hLC : L < C) (hCR : C < R) :
    (⟨L, C, l, ¬ₘ m⟩ : MarkedInterval).carrier ∪
        (⟨C, R, m, r⟩ : MarkedInterval).carrier =
      (⟨L, R, l, r⟩ : MarkedInterval).carrier := by
  cases l <;> cases m <;> cases r <;>
    simp [carrier_eq, Marker.complement, hLC, hLC.le, hCR, hCR.le]

/-- At a degenerate left cut, the split is valid under the marker
compatibility used by the corrected form of Proposition 3.10 (2). -/
theorem carrier_union_split_left (L R : ℝ) (l m r : Marker)
    (hLR : L < R) (hmarker : m.Includes → l.Includes) :
    (⟨L, L, l, ¬ₘ m⟩ : MarkedInterval).carrier ∪
        (⟨L, R, m, r⟩ : MarkedInterval).carrier =
      (⟨L, R, l, r⟩ : MarkedInterval).carrier := by
  cases l <;> cases m <;> cases r <;>
    simp [carrier_eq, Marker.complement, Marker.Includes, hLR, hLR.le] at hmarker ⊢

/-- Union of two strictly overlapping marked intervals. The first interval
starts no later than the second; if they start together, the second left
marker may not include an endpoint excluded by the first. -/
theorem carrier_union_overlap (L A B R : ℝ) (l q m r : Marker)
    (hleft : L < A ∨ (L = A ∧ (m.Includes → l.Includes)))
    (hoverlap : A < B) (hright : B < R) :
    (⟨L, B, l, q⟩ : MarkedInterval).carrier ∪
        (⟨A, R, m, r⟩ : MarkedInterval).carrier =
      (⟨L, R, l, r⟩ : MarkedInterval).carrier := by
  ext x
  cases l <;> cases q <;> cases m <;> cases r <;>
    simp [carrier_eq, Marker.Includes] at hleft ⊢ <;> grind

/-- Merge overlapping or touching intervals, including all endpoint cases.
At a shared cut at least one side must include the cut; coincident outer
endpoints must respect containment of markers. -/
theorem carrier_union_connected (L A B R : ℝ) (l q m r : Marker)
    (hleft : L < A ∨ (L = A ∧ (m.Includes → l.Includes)))
    (hjoin : A < B ∨ (A = B ∧ (q.Includes ∨ m.Includes)))
    (hright : B < R ∨ (B = R ∧ (q.Includes → r.Includes))) :
    (⟨L, B, l, q⟩ : MarkedInterval).carrier ∪
        (⟨A, R, m, r⟩ : MarkedInterval).carrier =
      (⟨L, R, l, r⟩ : MarkedInterval).carrier := by
  ext x
  cases l <;> cases q <;> cases m <;> cases r <;>
    simp [carrier_eq, Marker.Includes] at hleft hjoin hright ⊢ <;> grind

/-- A nonempty interval intersects a half-open suffix if it starts before
the horizon and its right endpoint reaches the suffix with compatible markers. -/
theorem inter_suffix_nonempty (K : MarkedInterval) (u τ : ℝ) (m : Marker)
    (hne : K.carrier.Nonempty) (hu : u < τ) (hstart : K.left < τ)
    (hreach : u <[Marker.conj m K.rightBoundary] K.right) :
    (K.carrier ∩ (⟨u, τ, m, ○⟩ : MarkedInterval).carrier).Nonempty := by
  apply Set.not_disjoint_iff_nonempty_inter.1
  intro hd
  have hs : (⟨u, τ, m, ○⟩ : MarkedInterval).carrier.Nonempty :=
    (nonempty_iff _).2 (Or.inl hu)
  have hsep := (disjoint_iff hne hs).1 hd
  rcases K with ⟨l, r, lb, rb⟩
  cases m <;> cases lb <;> cases rb <;>
    simp [MarkedLT, Marker.conj, Marker.notConj, Marker.Includes] at hsep hreach <;>
    grind

/-- Consecutive nonempty intervals with complementary markers cover every
point between any point of the first and any point of the second. -/
theorem mem_union_of_between_adjacent (J K : MarkedInterval)
    (hJ : J.carrier.Nonempty) (hK : K.carrier.Nonempty)
    (hadj : J.right = K.left)
    (hm : J.rightBoundary = Marker.complement K.leftBoundary)
    {t u x : ℝ} (ht : t ∈ J) (hu : u ∈ K) (htx : t ≤ x) (hxu : x ≤ u) :
    x ∈ J.carrier ∪ K.carrier := by
  rcases lt_trichotomy x J.right with hlt | heq | hgt
  · left
    refine ⟨?_, Or.inl hlt⟩
    rcases ht.1 with htl | ⟨het, hb⟩
    · exact Or.inl (htl.trans_le htx)
    · rcases htx.lt_or_eq with htx | htx
      · exact Or.inl (het ▸ htx)
      · exact Or.inr ⟨het.trans htx, hb⟩
  · subst x
    by_cases hb : J.rightBoundary.Includes
    · exact Or.inl (right_mem J hJ hb)
    · have hk : K.leftBoundary.Includes := by
        rw [hm, Marker.includes_complement] at hb
        exact Classical.not_not.mp hb
      exact Or.inr (hadj ▸ left_mem K hK hk)
  · right
    refine ⟨Or.inl (hadj ▸ hgt), ?_⟩
    rcases hu.2 with hur | ⟨heu, hb⟩
    · exact Or.inl (hxu.trans_lt hur)
    · rcases hxu.lt_or_eq with hxu | hxu
      · exact Or.inl (hxu.trans_eq heu)
      · exact Or.inr ⟨hxu.trans heu, hb⟩

/-- A future point outside the current piece admits a point of the next
piece no later than it. The next piece need not contain its left endpoint. -/
theorem exists_mem_next_le_of_not_mem (J K : MarkedInterval)
    (hJ : J.carrier.Nonempty) (hK : K.carrier.Nonempty)
    (hadj : J.right = K.left)
    (hm : J.rightBoundary = Marker.complement K.leftBoundary)
    {t x : ℝ} (ht : t ∈ J) (htx : t ≤ x) (hx : x ∉ J) :
    ∃ u ∈ K, u ≤ x := by
  have hge : J.right ≤ x := by
    by_contra hn
    have hxr : x < J.right := lt_of_not_ge hn
    apply hx
    refine ⟨?_, Or.inl hxr⟩
    rcases ht.1 with hlt | ⟨heq, hb⟩
    · exact Or.inl (hlt.trans_le htx)
    · rcases htx.lt_or_eq with hlt | heq'
      · exact Or.inl (heq ▸ hlt)
      · exact Or.inr ⟨heq.trans heq', hb⟩
  rcases hge.lt_or_eq with hlt | heq
  · obtain ⟨z, hz⟩ := hK
    by_cases hzx : z ≤ x
    · exact ⟨z, hz, hzx⟩
    · have hlx : K.left < x := hadj ▸ hlt
      have hxz : x < z := lt_of_not_ge hzx
      obtain ⟨u, hlu, hux⟩ := exists_between hlx
      refine ⟨u, ⟨Or.inl hlu, Or.inl ?_⟩, hux.le⟩
      exact (hux.trans hxz).trans_le (le_right_of_mem hz)
  · have hn : ¬J.rightBoundary.Includes := by
      intro hb
      exact hx (heq ▸ right_mem J hJ hb)
    have hb : K.leftBoundary.Includes := by
      rw [hm, Marker.includes_complement] at hn
      exact Classical.not_not.mp hn
    exact ⟨K.left, left_mem K hK hb, (hadj.symm.trans heq).le⟩

/-- Nonempty marked intervals intersect when each left endpoint reaches
the other's right endpoint with compatible markers. -/
theorem inter_nonempty_of_cross_bounds (J K : MarkedInterval)
    (hJ : J.carrier.Nonempty) (hK : K.carrier.Nonempty)
    (hJK : J.left <[Marker.conj J.leftBoundary K.rightBoundary] K.right)
    (hKJ : K.left <[Marker.conj K.leftBoundary J.rightBoundary] J.right) :
    (J.carrier ∩ K.carrier).Nonempty := by
  apply Set.not_disjoint_iff_nonempty_inter.1
  intro hd
  have hsep := (disjoint_iff hJ hK).1 hd
  rcases J with ⟨jl, jr, jlb, jrb⟩
  rcases K with ⟨kl, kr, klb, krb⟩
  cases jlb <;> cases jrb <;> cases klb <;> cases krb <;>
    simp [MarkedLT, Marker.conj, Marker.notConj, Marker.Includes] at hsep hJK hKJ <;>
    grind

/-- Translate an interval by `t`; this is the notation `t + I`. -/
def translate (t : ℝ) (I : MarkedInterval) : MarkedInterval where
  left := t + I.left
  right := t + I.right
  leftBoundary := I.leftBoundary
  rightBoundary := I.rightBoundary

@[simp] theorem left_translate (t : ℝ) (I : MarkedInterval) :
    (translate t I).left = t + I.left := rfl

@[simp] theorem right_translate (t : ℝ) (I : MarkedInterval) :
    (translate t I).right = t + I.right := rfl

/-- Membership in a translated interval can be pulled back by subtraction. -/
theorem mem_translate_iff {t x : ℝ} {I : MarkedInterval} :
    x ∈ translate t I ↔ x - t ∈ I := by
  simp only [mem_iff, translate]
  constructor
  · rintro ⟨hl, hr⟩
    constructor
    · rcases hl with h | ⟨h, hb⟩
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, hb⟩
    · rcases hr with h | ⟨h, hb⟩
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, hb⟩
  · rintro ⟨hl, hr⟩
    constructor
    · rcases hl with h | ⟨h, hb⟩
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, hb⟩
    · rcases hr with h | ⟨h, hb⟩
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, hb⟩

/-- Minkowski difference `K - I` (Section 2). -/
def minkowskiDifference (K I : MarkedInterval) : Set ℝ :=
  {t | ∃ k ∈ K, ∃ i ∈ I, t = k - i}

/-- Lemma A.1 (Minkowski difference). The witness is at or after `t`
because `I` lies in the nonnegative reals. -/
theorem mem_minkowskiDifference_iff {t : ℝ} {K I : MarkedInterval}
    (hI : ∀ i ∈ I, 0 ≤ i) :
    t ∈ minkowskiDifference K I ↔
      ∃ t' ≥ t, t' ∈ K ∧ t' ∈ translate t I := by
  constructor
  · rintro ⟨k, hk, i, hi, rfl⟩
    refine ⟨k, ?_, hk, ?_⟩
    · have := hI i hi
      linarith
    · rw [mem_translate_iff]
      convert hi using 1
      ring
  · rintro ⟨t', htt', ht'K, ht'I⟩
    refine ⟨t', ht'K, t' - t, ?_, ?_⟩
    · exact mem_translate_iff.mp ht'I
    · ring

end MarkedInterval

end STLTableau
