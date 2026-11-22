import STLTableaux.Closure.Expansion.BranchwiseRename
import STLTableaux.Closure.Expansion.BranchwiseLengthCore
import STLTableaux.Closure.Expansion.PrefixOrbitTermination
import STLTableaux.Closure.Expansion.BranchwiseClosure
import STLTableaux.Closure.Expansion.BranchwiseOrbitFinite

/-! The common suffix bound in C.15, using orbits of entire expansion prefixes. -/

namespace STLTableau.Section3.ConcreteContextual

open Section4.Finiteness (renameTransition)

variable {Clock Var : Type*} [DecidableEq Clock]

/-- Before level k the one-step family may take any expansion. From level k
on, the selected current predicate must not yet be rule-closed. -/
def ClosureSearchStep (k i : ℕ) (A B : TransitionForm Clock Var) : Prop :=
  ∃ p ∈ branchwiseCurrent A, (k ≤ i → ¬ catalogue.RuleClosedFor A p) ∧
    AlphaBranchwisePExpansion p A B

private theorem closureSearchStep_rename (e : Equiv.Perm Clock) {k i : ℕ}
    {A B : TransitionForm Clock Var} (h : ClosureSearchStep k i A B) :
    ClosureSearchStep k i (renameTransition e A) (renameTransition e B) := by
  obtain ⟨p, hp, ho, hs⟩ := h
  exact ⟨p.rename e, (branchwiseCurrent_rename_iff e A p).mpr hp,
    fun hi hc => ho hi ((ruleClosedFor_rename_iff e A p).mp hc), hs.rename e⟩

private theorem closureSearch_no_infinite (k : ℕ) (A : ℕ → TransitionForm Clock Var)
    (h : ∀ i, ClosureSearchStep k i (A i) (A (i + 1))) : False := by
  classical
  let T : ℕ → TransitionForm Clock Var := fun i => A (k + i)
  have htail (i : ℕ) : ∃ p ∈ branchwiseCurrent (T i),
      ¬ catalogue.RuleClosedFor (T i) p ∧ AlphaBranchwisePExpansion p (T i) (T (i + 1)) := by
    obtain ⟨p, hp, hopen, hs⟩ := h (k + i)
    exact ⟨p, hp, hopen (Nat.le_add_right k i), hs⟩
  choose p hp hopen hs using htail
  -- Once selected, the predicate stays rule-closed along later expansions.
  have hLater (i : ℕ) : ∀ j, i < j → catalogue.RuleClosedFor (T j) (p i) := by
    intro j
    induction j with
    | zero => omega
    | succ j ih =>
      intro hij
      obtain ⟨_, ha, he⟩ := hs j
      by_cases hEq : i = j
      · subst i
        exact branchwisePExpansion_target_ruleClosed he
      · exact ruleClosed_mono he.extension _ ((ha.ruleClosed_iff _).mpr (ih (by omega)))
  have hinj : Function.Injective p := by
    intro i j he
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact (hopen j (he ▸ hLater i j hlt)).elim
    · exact heq
    · exact (hopen i (he.symm ▸ hLater j i hgt)).elim
  -- The downward induction on I_d excludes an infinite literal suffix.
  apply BranchwiseLength.no_infinite_expansions
    (fun i => FaithfulClosure.statePredicates (T i).current) p Predicate.complexity
    (fun i => (FaithfulClosure.mem_statePredicates _ _).mpr (hp i)) hinj
  intro i q hnew
  obtain ⟨hq, hn⟩ := Finset.mem_sdiff.mp hnew
  obtain ⟨S, ha, he⟩ := hs i
  apply he.new_current_complexity ((FaithfulClosure.mem_statePredicates _ _).mp hq)
  rw [ha.current]
  exact fun hm => hn ((FaithfulClosure.mem_statePredicates _ _).mpr hm)

local instance clockRenameAction : MulAction (Equiv.Perm Clock) (TransitionForm Clock Var) where
  smul := renameTransition
  one_smul F := renameTransition_refl F
  mul_smul e f F := (renameTransition_trans f e F).symm

private def fixRootClocks (F : TransitionForm Clock Var) : Subgroup (Equiv.Perm Clock) where
  carrier := {e | ∀ c ∈ F.allClocks, e c = c}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro e f he hf c hc
    change e (f c) = c
    rw [hf c hc, he c hc]
  inv_mem' := by
    intro e he c hc
    change e.symm c = c
    exact e.injective ((e.apply_symm_apply c).trans (he c hc).symm)

/-- Bound the length after level k by finite branching of whole-prefix orbits.
The representatives of successors may depend on the already visited prefix. -/
theorem closureSearch_common_suffix_bound (F : TransitionForm Clock Var) (k : ℕ) :
    ∃ D, ∀ n A, PrefixOrbitTermination.Valid (ClosureSearchStep k) F n A → n ≤ k + D := by
  classical
  have finiteCover (n : ℕ) (A : ℕ → TransitionForm Clock Var)
      (hA : PrefixOrbitTermination.Valid (ClosureSearchStep k) F n A) :
      ∃ reps : Finset (TransitionForm Clock Var), ∀ B, ClosureSearchStep k n (A n) B →
        ∃ e : fixRootClocks F, (∀ i ≤ n, e • A i = A i) ∧ e • B ∈ reps := by
    let S := (Finset.range (n + 1)).biUnion fun i => (A i).allClocks_finite.toFinset
    have hS (i : ℕ) (hi : i ≤ n) : (A i).allClocks ⊆ (S : Set Clock) := by
      intro c hc
      exact Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_range.mpr (by omega), by simpa only [Set.Finite.mem_toFinset] using hc⟩
    obtain ⟨T, hT, hcover⟩ := finite_alphaBranchwise_successor_cover (A n) S
    refine ⟨hT.toFinset, ?_⟩
    rintro B ⟨p, hp, _, hs⟩
    obtain ⟨e, he, hB⟩ := hcover hp hs
    have hfix : e ∈ fixRootClocks F := by
      intro c hc
      apply he c (hS 0 (Nat.zero_le n) ?_)
      simpa only [hA.1] using hc
    refine ⟨⟨e, hfix⟩, fun i hi => renameTransition_eq_of_fixes e (A i)
      (fun c hc => he c (hS i hi hc)), ?_⟩
    change renameTransition e B ∈ hT.toFinset
    exact (Set.Finite.mem_toFinset hT).mpr hB
  obtain ⟨N, hN⟩ := PrefixOrbitTermination.common_length_bound
    (G := fixRootClocks F) (ClosureSearchStep k) F
    (by intro e i A B h; exact closureSearchStep_rename e.val h) finiteCover
    (fun ⟨A, _, hs⟩ => closureSearch_no_infinite k A hs)
  refine ⟨N - k, ?_⟩
  intro n A hn
  have := hN n A hn
  omega

end STLTableau.Section3.ConcreteContextual
