import STLTableaux.Finiteness.Derivation.Pending.PendingOwnership
import Mathlib.Data.List.Dedup

/-! Directed collection of duplicate current requirements. The literal next
list is retained. Empty conjunction is still Option.none; no neutral judgement
is introduced. Structural equivalence and nonincreasing pending weight are
proved separately, without arbitrary StructuralEq weight invariance. -/
namespace STLTableau.Section4.Finiteness.PendingCollection
open Section3
variable {Clock Var : Type*}

noncomputable def collect {α : Type*} (L : List α) : List α := by
  classical
  exact L.dedup

@[simp] theorem mem_collect {α : Type*} (L : List α) (a : α) : a ∈ collect L ↔ a ∈ L := by
  classical
  exact List.mem_dedup

theorem collect_nodup {α : Type*} (L : List α) : (collect L).Nodup := by
  classical
  exact List.nodup_dedup _

@[simp] theorem collect_eq_nil {α : Type*} (L : List α) : collect L = [] ↔ L = [] := by
  classical
  exact List.dedup_eq_nil _

/-- A selected occurrence can absorb one duplicated prefix through actual
AC-idempotence. This statement makes no claim about arbitrary rewrites' weight. -/
theorem absorb_existing (L : List (MixedJ Clock Var)) (J K : MixedJ Clock Var)
    (hfold : foldCurrent L = some J) (hmem : K ∈ L) : StructuralEq (.conj K J) J := by
  obtain ⟨Γ,hΓ,_⟩ := foldCurrent_expose L J K hfold hmem
  cases Γ with
  | none =>
    exact .trans (.conj (.refl K) hΓ) (.trans (.idem K) hΓ.symm)
  | some G =>
    exact .trans (.conj (.refl K) hΓ)
      (.trans (.symm (.assoc K K G)) (.trans (.conj (.idem K) (.refl G)) hΓ.symm))

/-- Deduplicate only the mapped prefix, leaving the exact tail unchanged.
The tail may contain future requirements; it is never deduplicated or replaced. -/
theorem collect_map_prefix {α : Type*} (L : List α) (f : α → MixedJ Clock Var)
    (tail : List (MixedJ Clock Var)) (J : MixedJ Clock Var)
    (hfold : foldCurrent (L.map f ++ tail) = some J) :
    ∃ K, foldCurrent ((collect L).map f ++ tail) = some K ∧
      StructuralEq J K ∧ pendingWeight K ≤ pendingWeight J := by
  classical
  induction L generalizing J with
  | nil =>
    exact ⟨J,hfold,.refl _,le_rfl⟩
  | cons a L ih =>
    cases ht : foldCurrent (L.map f ++ tail) with
    | none =>
      have he := (foldCurrent_none_iff _).1 ht
      simp only [List.append_eq_nil_iff,List.map_eq_nil_iff] at he
      obtain ⟨rfl,rfl⟩ := he
      have hJ : f a = J := by simpa [foldCurrent,optionalConj] using hfold
      subst J
      exact ⟨f a,by simp [collect,foldCurrent,optionalConj],.refl _,le_rfl⟩
    | some G =>
      have hJ : Section3.Judgement.conj (f a) G = J := by
        simpa only [List.map_cons,List.cons_append,foldCurrent_cons,ht,prependCurrent,Option.some.injEq] using hfold
      subst J
      obtain ⟨K,hK,hGK,hw⟩ := ih G ht
      by_cases ha : a ∈ L
      · have hcollect : collect (a :: L) = collect L := List.dedup_cons_of_mem ha
        refine ⟨K,?_,?_,?_⟩
        · simpa only [hcollect] using hK
        · exact .trans (absorb_existing (L.map f ++ tail) G (f a) ht
            (List.mem_append_left _ (List.mem_map_of_mem ha))) hGK
        · change pendingWeight K ≤ pendingWeight (f a) + pendingWeight G
          omega
      · have hcollect : collect (a :: L) = a :: collect L := List.dedup_cons_of_notMem ha
        refine ⟨.conj (f a) K,?_,.conj (.refl _) hGK,?_⟩
        · simp only [hcollect,List.map_cons,List.cons_append,foldCurrent_cons,hK,prependCurrent]
        · exact Nat.add_le_add_left hw _

/-- Collection preserves literal absence as well as successful nonempty folds. -/
theorem fold_collect_none_iff {α : Type*} (L : List α) (f : α → MixedJ Clock Var)
    (tail : List (MixedJ Clock Var)) :
    foldCurrent ((collect L).map f ++ tail) = none ↔ foldCurrent (L.map f ++ tail) = none := by
  simp only [foldCurrent_none_iff,List.append_eq_nil_iff,List.map_eq_nil_iff,collect_eq_nil]

/-- Actual local collection, retaining the same next syntax list byte-for-byte.
Membership and Nodup concern the represented Local syntax, before mapping it. -/
theorem collect_locals (locals : List (Local Clock Var)) (nextInputs : List (MixedJ Clock Var))
    (J : MixedJ Clock Var)
    (hfold : foldCurrent (locals.map Local.toJudgement ++ nextInputs.map Section3.Judgement.next) = some J) :
    ∃ K, foldCurrent ((collect locals).map Local.toJudgement ++ nextInputs.map Section3.Judgement.next) = some K ∧
      StructuralEq J K ∧ pendingWeight K ≤ pendingWeight J ∧
      (collect locals).Nodup ∧ ∀ l, l ∈ collect locals ↔ l ∈ locals := by
  obtain ⟨K,hK,hs,hw⟩ := collect_map_prefix locals Local.toJudgement
    (nextInputs.map Section3.Judgement.next) J hfold
  exact ⟨K,hK,hs,hw,collect_nodup _,mem_collect _⟩

end STLTableau.Section4.Finiteness.PendingCollection
