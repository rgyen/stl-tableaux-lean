/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Closure.Residual.BranchNormalization

/-! # Clock renaming and fresh bound-clock representatives

Renaming uses permutations, so arbitrary nested reset scopes (including
shadowing) are preserved. Fixing the free clocks gives alpha-equivalence.
-/
namespace STLTableau
open scoped STL

/-- Move a finite set of bound names away from any finite forbidden set,
while fixing a disjoint finite set of free names. -/
theorem exists_fresh_clock_permutation {Clock : Type*} [Infinite Clock]
    (S T U : Set Clock) (hS : S.Finite) (hT : T.Finite) (hU : U.Finite)
    (hST : Disjoint S T) :
    ∃ e : Equiv.Perm Clock, (∀ c ∈ T, e c = c) ∧ Disjoint (e '' S) U := by
  classical
  induction S, hS using Set.Finite.induction_on generalizing T U with
  | empty => exact ⟨Equiv.refl _, by simp, by simp⟩
  | @insert a S ha hS ih =>
      have haT : a ∉ T := fun h => Set.disjoint_left.1 hST (by simp) h
      have hST' : Disjoint S (insert a T) := by
        apply Set.disjoint_left.2
        intro x hx ht
        rcases ht with rfl | ht
        · exact ha hx
        · exact Set.disjoint_left.1 hST (Or.inr hx) ht
      obtain ⟨e, hfix, hdis⟩ := ih (insert a T) (insert a U)
        (hT.insert a) (hU.insert a) hST'
      obtain ⟨b, hb⟩ := (((hU.union hT).union (hS.image e)).insert a).exists_notMem
      have hba : b ≠ a := fun h => hb (Or.inl h)
      have hbU : b ∉ U := fun h => hb (Or.inr (Or.inl (Or.inl h)))
      have hbT : b ∉ T := fun h => hb (Or.inr (Or.inl (Or.inr h)))
      have hbS : b ∉ e '' S := fun h => hb (Or.inr (Or.inr h))
      refine ⟨e.trans (Equiv.swap a b), ?_, Set.disjoint_left.2 ?_⟩
      · intro x hx
        change Equiv.swap a b (e x) = x
        rw [hfix x (Or.inr hx)]
        exact Equiv.swap_apply_of_ne_of_ne
          (fun h => haT (h ▸ hx)) (fun h => hbT (h ▸ hx))
      · rintro y ⟨x, hx, rfl⟩ hy
        rcases hx with rfl | hx
        · apply hbU
          simpa [Equiv.trans_apply, hfix x (by simp)] using hy
        · have hxa : e x ≠ a := fun h =>
            Set.disjoint_left.1 hdis ⟨x, hx, h⟩ (by simp)
          have hxb : e x ≠ b := fun h => hbS ⟨x, hx, h⟩
          have heq : (e.trans (Equiv.swap a b)) x = e x :=
            Equiv.swap_apply_of_ne_of_ne hxa hxb
          rw [heq] at hy
          exact Set.disjoint_left.1 hdis ⟨x, hx, rfl⟩ (Or.inr hy)

namespace IntervalPredicate
variable {Clock Var : Type*}

def rename (e : Equiv.Perm Clock) : IntervalPredicate Clock Var → IntervalPredicate Clock Var
  | .plain φ => .plain φ
  | .upper c m op I φ => .upper (e c) m op I φ
  | .bounded c d m q op I φ => .bounded (e c) (e d) m q op I φ

theorem scope_rename (e : Equiv.Perm Clock) (p : IntervalPredicate Clock Var)
    (J : MarkedInterval) (α : ClockValuation Clock) :
    (p.rename e).scope J α = p.scope J (α ∘ e) := by
  cases p <;> rfl

theorem satisfies_rename (e : Equiv.Perm Clock) (p : IntervalPredicate Clock Var)
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock) :
    (p.rename e).Satisfies σ J α ↔ p.Satisfies σ J (α ∘ e) := by
  cases p with
  | plain => rfl
  | upper c m op I φ => cases op <;> rfl
  | bounded c d m q op I φ => cases op <;> rfl

theorem invariant_rename (e : Equiv.Perm Clock) (p : IntervalPredicate Clock Var)
    (J : MarkedInterval) (α : ClockValuation Clock) :
    Invariant J α (p.rename e) ↔ Invariant J (α ∘ e) p := by
  cases p with
  | plain => rfl
  | upper c m op I φ => cases op <;> rfl
  | bounded c d m q op I φ => cases op <;> rfl

@[simp] theorem clockSet_rename (e : Equiv.Perm Clock) (p : IntervalPredicate Clock Var) :
    (p.rename e).clockSet = e '' p.clockSet := by
  cases p <;> simp [rename, clockSet, Set.image_insert_eq]

theorem clockSet_finite (p : IntervalPredicate Clock Var) : p.clockSet.Finite := by
  cases p <;> simp [clockSet]

end IntervalPredicate

namespace ClockResetSet
variable {Clock : Type*}

def rename (e : Equiv.Perm Clock) (Λ : ClockResetSet Clock) : ClockResetSet Clock where
  value c := Λ.value (e.symm c)
  finite_domain := (Λ.finite_domain.image e).subset (by
    rintro c ⟨a, ha⟩
    exact ⟨e.symm c, ⟨a, ha⟩, e.apply_symm_apply c⟩)

@[simp] theorem clocks_rename (e : Equiv.Perm Clock) (Λ : ClockResetSet Clock) :
    (Λ.rename e).clocks = e '' Λ.clocks := by
  ext c
  simp [clocks, rename]

theorem apply_rename (e : Equiv.Perm Clock) (Λ : ClockResetSet Clock)
    (α : ClockValuation Clock) :
    (Λ.rename e).apply α ∘ e = Λ.apply (α ∘ e) := by
  funext c
  simp [apply, rename]

end ClockResetSet

namespace Judgement
variable {Clock Var : Type*}

def rename (e : Equiv.Perm Clock) : Judgement Clock Var → Judgement Clock Var
  | .terminal => .terminal
  | .clock c r a => .clock (e c) r a
  | .leftMarker m => .leftMarker m
  | .predicate p => .predicate (p.rename e)
  | .next Ψ => .next (rename e Ψ)
  | .reset Λ Ψ => .reset (Λ.rename e) (rename e Ψ)
  | .conj Φ Ψ => .conj (rename e Φ) (rename e Ψ)

theorem satisfies_rename (e : Equiv.Perm Clock) (Ψ : Judgement Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P) :
    Satisfies σ P α k (Ψ.rename e) ↔ Satisfies σ P (α ∘ e) k Ψ := by
  induction Ψ generalizing α k with
  | predicate p => simp [rename, Satisfies, IntervalPredicate.satisfies_rename]
  | reset Λ Ψ ih => simp [rename, Satisfies, ih, ClockResetSet.apply_rename]
  | next Ψ ih =>
      simp only [rename, Satisfies]
      split
      · exact ih _ _
      · rfl
  | conj Φ Ψ ihΦ ihΨ => simp [rename, Satisfies, ihΦ, ihΨ]
  | _ => rfl

theorem clocks_finite (Ψ : Judgement Clock Var) : Ψ.clocks.Finite := by
  induction Ψ with
  | terminal => exact Set.finite_empty
  | leftMarker => exact Set.finite_empty
  | clock c => exact Set.finite_singleton c
  | predicate p => exact p.clockSet_finite
  | next Ψ ih => exact ih
  | reset Λ Ψ ih => exact Λ.finite_domain.union ih
  | conj Φ Ψ ihΦ ihΨ => exact ihΦ.union ihΨ

theorem freeClocks_subset_clocks (Ψ : Judgement Clock Var) : Ψ.freeClocks ⊆ Ψ.clocks := by
  induction Ψ with
  | reset Λ Ψ ih => exact fun _ h => Or.inr (ih h.1)
  | conj Φ Ψ ihΦ ihΨ => exact Set.union_subset_union ihΦ ihΨ
  | next Ψ ih => exact ih
  | _ => exact Set.Subset.refl _

theorem freeClocks_finite (Ψ : Judgement Clock Var) : Ψ.freeClocks.Finite :=
  Ψ.clocks_finite.subset Ψ.freeClocks_subset_clocks

@[simp] theorem freeClocks_rename (e : Equiv.Perm Clock) (Ψ : Judgement Clock Var) :
    (Ψ.rename e).freeClocks = e '' Ψ.freeClocks := by
  induction Ψ with
  | reset Λ Ψ ih =>
      simp [rename, freeClocks, ih, Set.image_sdiff e.injective]
  | conj Φ Ψ ihΦ ihΨ => simp [rename, freeClocks, ihΦ, ihΨ, Set.image_union]
  | next Ψ ih => exact ih
  | predicate p => exact p.clockSet_rename e
  | _ => simp [rename, freeClocks]

/-- Uniform clock renaming is alpha-conversion when it fixes every free clock.
For a reset judgement, its reset-bound clocks are excluded from this condition. -/
theorem rename_equivalent (e : Equiv.Perm Clock) (Ψ : Judgement Clock Var)
    (hfix : ∀ c ∈ Ψ.freeClocks, e c = c) : Ψ.rename e ≡ⱼ Ψ := by
  intro σ P α k
  rw [satisfies_rename]
  exact satisfies_congr_of_agree (fun c hc => by simp [hfix c hc]) σ P k

/-- One-hole judgement contexts from the alpha-conversion lemma. -/
inductive Context (Clock Var : Type*) where
  | hole
  | conjLeft (context : Context Clock Var) (right : Judgement Clock Var)
  | conjRight (left : Judgement Clock Var) (context : Context Clock Var)
  | next (context : Context Clock Var)
  | reset (resets : ClockResetSet Clock) (context : Context Clock Var)

namespace Context

def fill (Ψ : Judgement Clock Var) : Context Clock Var → Judgement Clock Var
  | .hole => Ψ
  | .conjLeft K Χ => .conj (fill Ψ K) Χ
  | .conjRight Χ K => .conj Χ (fill Ψ K)
  | .next K => .next (fill Ψ K)
  | .reset Λ K => .reset Λ (fill Ψ K)

theorem fill_equivalent (K : Context Clock Var) {Ψ Χ : Judgement Clock Var}
    (h : Ψ ≡ⱼ Χ) : K.fill Ψ ≡ⱼ K.fill Χ := by
  intro σ P α k
  induction K generalizing α k with
  | hole => exact h σ P α k
  | conjLeft K Θ ih => exact and_congr (ih α k) Iff.rfl
  | conjRight Θ K ih => exact and_congr Iff.rfl (ih α k)
  | reset Λ K ih => exact ih (Λ.apply α) k
  | next K ih =>
      simp only [fill, Satisfies]
      split
      · exact ih _ _
      · rfl

/-- Alpha-conversion may be performed inside any surrounding reset/next/conjunction. -/
theorem fill_rename_equivalent (K : Context Clock Var) (e : Equiv.Perm Clock)
    (Ψ : Judgement Clock Var) (hfix : ∀ c ∈ Ψ.freeClocks, e c = c) :
    K.fill (Ψ.rename e) ≡ⱼ K.fill Ψ :=
  K.fill_equivalent (Ψ.rename_equivalent e hfix)

end Context

end Judgement
end STLTableau
