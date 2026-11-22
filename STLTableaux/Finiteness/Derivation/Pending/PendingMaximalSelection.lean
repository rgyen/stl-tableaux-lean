import STLTableaux.Finiteness.Derivation.CanonicalProjections
import STLTableaux.Finiteness.Derivation.Pending.PendingComplexity
import Mathlib.Data.Finset.Max

/-! Actual maximal-current selection. These finite selection facts impose no
boundary sharing policy and do not assert a bounded accepting path. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

private theorem atomic_current_weight_zero (J : MixedJ Clock Var)
    (h : ∀ p ∈ J.currentPredicates, p.IsAtomic) : pendingWeight J = 0 := by
  induction J with
  | predicate p => simp [pendingWeight, h p (by simp [Section3.Judgement.currentPredicates])]
  | conj J K ih ik =>
    simp only [pendingWeight, ih (fun p hp => h p (Or.inl hp)),
      ik (fun p hp => h p (Or.inr hp)), Nat.zero_add]
  | reset R J ih => exact ih h
  | next => rfl
  | terminal => rfl
  | marker => rfl
  | clock => rfl

/-- A nonzero owned pending spine contains an actual nonatomic local of maximal
complexity among its current nonatomic locals. The split selects its occurrence. -/
theorem owned_select_maximal
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (hz : pendingWeight owned.canonical ≠ 0) :
    ∃ p left right, owned.locals = left ++ Local.predicate p :: right ∧
      ¬p.IsAtomic ∧ ∀ q, Local.predicate q ∈ owned.locals → ¬q.IsAtomic →
        q.complexity ≤ p.complexity := by
  classical
  have he : ∃ p, Local.predicate p ∈ owned.locals ∧ ¬p.IsAtomic := by
    by_contra hn
    apply hz
    apply atomic_current_weight_zero
    intro p hp
    by_contra hna
    exact hn ⟨p, (canonical_currentPredicates_iff owned.shape p).1 hp, hna⟩
  let S := owned.locals.toFinset.filter
    (fun l => ∃ p, l = Local.predicate p ∧ ¬p.IsAtomic)
  let complexity : Local Clock Var → ℕ := fun l => match l with
    | .predicate p => p.complexity
    | .marker _ => 0
    | .terminal => 0
  have hne : S.Nonempty := by
    obtain ⟨p, hp, hna⟩ := he
    exact ⟨Local.predicate p, Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr hp, p, rfl, hna⟩⟩
  obtain ⟨l, hl, hmax⟩ := Finset.exists_max_image S complexity hne
  obtain ⟨hmem, p, rfl, hna⟩ := Finset.mem_filter.mp hl
  obtain ⟨left, right, hsplit⟩ := List.mem_iff_append.mp (List.mem_toFinset.mp hmem)
  refine ⟨p, left, right, hsplit, hna, ?_⟩
  intro q hq hnq
  exact hmax (.predicate q) (Finset.mem_filter.mpr
    ⟨List.mem_toFinset.mpr hq, q, rfl, hnq⟩)

/-- Replacing a maximal current source by an actual raw branch introduces only
strictly smaller current children. Surviving old nonatomic locals stay at most
as complex as the selected source. -/
theorem maximal_raw_branch_replacement [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var}
    (left right : List (Local Clock Var))
    (hmax : ∀ q, Local.predicate q ∈ left ++ Local.predicate p :: right →
      ¬q.IsAtomic → q.complexity ≤ p.complexity)
    (hB : RawBranch p B) :
    (∀ q ∈ B.currentPredicates, q.complexity < p.complexity) ∧
    (∀ q, q ∈ B.currentPredicates ∨ Local.predicate q ∈ left ++ right →
      ¬q.IsAtomic → q.complexity ≤ p.complexity) := by
  refine ⟨hB.current_smaller, ?_⟩
  intro q hq hna
  rcases hq with hnew | hold
  · exact (hB.current_smaller q hnew).le
  · apply hmax q _ hna
    simp only [List.mem_append, List.mem_cons] at hold ⊢
    tauto

end STLTableau.Section4.Finiteness
