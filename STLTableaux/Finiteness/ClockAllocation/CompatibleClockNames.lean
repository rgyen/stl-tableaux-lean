import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.EquivFin

/-! Combinatorial clock-name allocation only. No semantic renaming or path
lifting is asserted: derivation invariance and no-reappearance are separate. -/
namespace STLTableau.Section4.Finiteness

variable {Clock : Type*}

/-- A prescribed injective interface assignment extends to the entire support. -/
theorem extend_clock_names {U E : Finset Clock} {K : Nat}
    (hEU : E ⊆ U) (hcard : U.card ≤ K) (f : E → Fin K)
    (hf : Function.Injective f) :
    ∃ g : U → Fin K, Function.Injective g ∧
      ∀ e : E, g ⟨e.val, hEU e.property⟩ = f e := by
  classical
  obtain ⟨b⟩ := Function.Embedding.nonempty_of_card_le
    (α := U) (β := Fin K) (by simpa using hcard)
  let inclusion : E → U := fun e => ⟨e.val, hEU e.property⟩
  have hi : Function.Injective inclusion := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : U => z.val) h)
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair (fun e => b (inclusion e)) f
    (b.injective.comp hi) hf
  exact ⟨fun u => p (b u), p.injective.comp b.injective, hp⟩

/-- Even a countable support sequence admits compatible allocations when each
interface is contained in both consecutive supports and every support fits. -/
theorem compatible_clock_names (U E : Nat → Finset Clock) (K : Nat)
    (hleft : ∀ i, E i ⊆ U i) (hright : ∀ i, E i ⊆ U (i + 1))
    (hcard : ∀ i, (U i).card ≤ K) :
    ∃ a : ∀ i, U i → Fin K,
      (∀ i, Function.Injective (a i)) ∧
      ∀ i (e : E i), a i ⟨e.val, hleft i e.property⟩ =
        a (i + 1) ⟨e.val, hright i e.property⟩ := by
  classical
  let Allocation (i : Nat) := {f : U i → Fin K // Function.Injective f}
  have initial : Nonempty (Allocation 0) := by
    obtain ⟨b⟩ := Function.Embedding.nonempty_of_card_le
      (α := U 0) (β := Fin K) (by simpa using hcard 0)
    exact ⟨⟨b, b.injective⟩⟩
  have next (i : Nat) (a : Allocation i) :
      ∃ b : Allocation (i + 1), ∀ e : E i,
        a.val ⟨e.val, hleft i e.property⟩ =
          b.val ⟨e.val, hright i e.property⟩ := by
    let f : E i → Fin K := fun e => a.val ⟨e.val, hleft i e.property⟩
    have hf : Function.Injective f := by
      intro x y h
      exact Subtype.ext (congrArg (fun z : U i => z.val) (a.property h))
    obtain ⟨g, hg, he⟩ := extend_clock_names (hright i) (hcard (i + 1)) f hf
    exact ⟨⟨g, hg⟩, fun e => (he e).symm⟩
  let a : ∀ i, Allocation i := fun i =>
    Nat.rec (Classical.choice initial) (fun j prev => Classical.choose (next j prev)) i
  refine ⟨fun i => (a i).val, fun i => (a i).property, ?_⟩
  intro i e
  exact Classical.choose_spec (next i (a i)) e

/-- A finite sequence is a special case: extend its last support constantly and
use empty interfaces after its last transition. No budget outside the prefix is
required. -/
theorem finite_compatible_clock_names (U E : Nat → Finset Clock) (n K : Nat)
    (hleft : ∀ i, i < n → E i ⊆ U i)
    (hright : ∀ i, i < n → E i ⊆ U (i + 1))
    (hcard : ∀ i, i ≤ n → (U i).card ≤ K) :
    ∃ a : ∀ i : Fin (n + 1), U i.val → Fin K,
      (∀ i, Function.Injective (a i)) ∧
      ∀ i (hi : i < n) (e : E i),
        a ⟨i, by omega⟩ ⟨e.val, hleft i hi e.property⟩ =
        a ⟨i + 1, by omega⟩ ⟨e.val, hright i hi e.property⟩ := by
  classical
  let V : Nat → Finset Clock := fun i => U (min i n)
  let F : Nat → Finset Clock := fun i => if i < n then E i else ∅
  have hl : ∀ i, F i ⊆ V i := by
    intro i
    by_cases hi : i < n
    · simpa [F, V, hi, Nat.min_eq_left (by omega : i ≤ n)] using hleft i hi
    · simp [F, hi]
  have hr : ∀ i, F i ⊆ V (i + 1) := by
    intro i
    by_cases hi : i < n
    · simpa [F, V, hi, Nat.min_eq_left (by omega : i + 1 ≤ n)] using hright i hi
    · simp [F, hi]
  obtain ⟨b, hb, he⟩ := compatible_clock_names V F K hl hr
    (fun i => hcard (min i n) (Nat.min_le_right i n))
  let a : ∀ i : Fin (n + 1), U i.val → Fin K := fun i x =>
    b i.val ⟨x.val, by simp [V, Nat.min_eq_left (by omega : i.val ≤ n), x.property]⟩
  refine ⟨a, ?_, ?_⟩
  · intro i x y h
    exact Subtype.ext (congrArg (fun z : V i.val => z.val) (hb i.val h))
  · intro i hi e
    exact he i ⟨e.val, by simp [F, hi, e.property]⟩

end STLTableau.Section4.Finiteness
