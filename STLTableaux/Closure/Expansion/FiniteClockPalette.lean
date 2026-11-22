import Mathlib.Algebra.Group.End
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Equiv.Fintype

/-! A finite palette for the names not yet seen in an expansion prefix. -/

namespace STLTableau.FiniteClockPalette

/-- A permutation can move any bounded finite support into one fixed finite
palette while fixing each name in the given prefix support. -/
private theorem exists_palette_infinite {Clock : Type*} [Infinite Clock] (S : Finset Clock) (n : ℕ) :
    ∃ Q : Finset Clock, ∀ U : Finset Clock, U.card ≤ n →
      ∃ e : Equiv.Perm Clock, (∀ c ∈ S, e c = c) ∧ (∀ c ∈ U, e c ∈ Q) := by
  classical
  obtain ⟨P, hP, hPc⟩ := S.finite_toSet.infinite_compl.exists_subset_card_eq n
  refine ⟨S ∪ P, ?_⟩
  intro U hU
  have hcard : (U \ S).card ≤ P.card := by
    rw [hPc]
    exact (Finset.card_le_card Finset.sdiff_subset).trans hU
  obtain ⟨V, hVP, hVc⟩ := Finset.exists_subset_card_eq hcard
  let a : (U \ S : Finset Clock) ≃ V := Finset.equivOfCardEq hVc.symm
  let f (x : (U \ S : Finset Clock)) : {c : Clock // c ∉ S} :=
    ⟨x.val, (Finset.mem_sdiff.mp x.property).2⟩
  let g (x : (U \ S : Finset Clock)) : {c : Clock // c ∉ S} :=
    ⟨(a x).val, hP (hVP (a x).property)⟩
  have hf : Function.Injective f := fun _ _ h =>
    Subtype.ext (congrArg (fun y : {c : Clock // c ∉ S} => y.val) h)
  have hg : Function.Injective g := fun _ _ h =>
    a.injective (Subtype.ext (congrArg (fun y : {c : Clock // c ∉ S} => y.val) h))
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  have hfix {c : Clock} (hc : c ∈ S) : e.ofSubtype c = c :=
    Equiv.Perm.ofSubtype_apply_of_not_mem _ (fun hn => hn hc)
  refine ⟨e.ofSubtype, fun _ => hfix, ?_⟩
  intro c hc
  by_cases hS : c ∈ S
  · rw [hfix hS]
    exact Finset.mem_union_left _ hS
  · let x : (U \ S : Finset Clock) := ⟨c, Finset.mem_sdiff.mpr ⟨hc, hS⟩⟩
    rw [Equiv.Perm.ofSubtype_apply_of_mem e hS]
    change (e (f x)).val ∈ S ∪ P
    rw [he x]
    exact Finset.mem_union_right _ (hVP (a x).property)

/-- A finite palette suffices even when the clock type itself is finite. -/
theorem exists_palette {Clock : Type*} (S : Finset Clock) (n : ℕ) :
    ∃ Q : Finset Clock, ∀ U : Finset Clock, U.card ≤ n →
      ∃ e : Equiv.Perm Clock, (∀ c ∈ S, e c = c) ∧ (∀ c ∈ U, e c ∈ Q) := by
  classical
  rcases finite_or_infinite Clock with h | h
  · letI := Fintype.ofFinite Clock
    exact ⟨Finset.univ, fun _ _ => ⟨Equiv.refl _, fun _ _ => rfl,
      fun _ _ => Finset.mem_univ _⟩⟩
  · exact exists_palette_infinite S n

end STLTableau.FiniteClockPalette
