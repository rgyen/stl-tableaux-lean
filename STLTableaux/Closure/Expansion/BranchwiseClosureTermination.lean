import STLTableaux.Closure.Expansion.BranchwiseClosure
import STLTableaux.Closure.Expansion.BranchwiseClosureOrbitBound
import STLTableaux.Closure.Expansion.BranchwiseRankOrbit
import STLTableaux.Closure.Expansion.FaithfulLevelRankBounds

/-! Lemma C.15 for single-predicate expansion levels. Downward induction
excludes infinite open-predicate suffixes, and finite branching of
clock-renaming prefix orbits gives the common bound. The target-guided
sequence stays subsumed by a fixed closure. -/

namespace STLTableau.Section3.ConcreteContextual

open BranchwiseExpansion

variable {Clock Var : Type*} [DecidableEq Clock]

/-- Apply the shared literal target-guided search with the common bound
on prefixes modulo renaming. -/
private theorem closure_reached_by_bound {F U : TransitionForm Clock Var} (k D : ℕ)
    (bound : ∀ n A, PrefixOrbitTermination.Valid (ClosureSearchStep k) F n A → n ≤ k + D)
    (hc : catalogue.IsClosure F U) :
    ∃ i ≤ k + D, U ∈ alphaBranchwiseExpansionLevel F i := by
  obtain ⟨i, hi, hm⟩ := guided_closure_of_length_bound (k + D) hc (fun n A h => by
    refine bound n A ⟨h.start, ?_⟩
    intro i hi
    obtain ⟨p, hp, ho, hs⟩ := h.step i hi
    exact ⟨p, hp, fun _ => ho, A i, .refl _, hs⟩)
  exact ⟨i, hi, branchwiseExpansionLevel_subset_alpha F i hm⟩

private theorem rank_zero_at_start_closed {F : TransitionForm Clock Var}
    (hz : alphaBranchwiseLevelRank F 0 = 0) : catalogue.IsClosed F := by
  intro p hp
  have hpRank : p.complexity ≤ alphaBranchwiseLevelRank F 0 := by
    apply complexity_le_rank (N := ExpansionFamily.initialBound F)
    · rw [fresh_zero]
      exact ExpansionFamily.initialBound_spec F
    · rwa [fresh_zero]
  exact zero_complexity_ruleClosed F p (by omega)

private theorem closed_mem_later_level {F U : TransitionForm Clock Var} {i : ℕ}
    (h : U ∈ alphaBranchwiseExpansionLevel F i) (hc : catalogue.IsClosed U)
    {p : Predicate Clock Var} (hp : p ∈ branchwiseCurrent U) :
    ∀ j, U ∈ alphaBranchwiseExpansionLevel F (i + j) := by
  intro j
  induction j with
  | zero => exact h
  | succ j ih =>
    exact ⟨U, ih, p, hp, U, .refl _, Or.inl ⟨hc p hp, rfl⟩⟩

/-- Appendix Lemma C.15. At or above the first zero rank there is one
exact single-expansion level containing every minimal closure of `F`. -/
theorem all_closures_mem_branchwise_level_at_first_rank_zero
    (F : TransitionForm Clock Var) (k : ℕ) (hz : alphaBranchwiseLevelRank F k = 0)
    (hfirst : ∀ i < k, 0 < alphaBranchwiseLevelRank F i) :
    ∃ N ≥ k, ∀ U, catalogue.IsClosure F U → U ∈ alphaBranchwiseExpansionLevel F N := by
  classical
  by_cases hk : k = 0
  · subst k
    have hclosed := rank_zero_at_start_closed hz
    refine ⟨0, le_rfl, fun U hc => ?_⟩
    exact (hc.minimal F (.refl _) hclosed hc.extension).antisymm hc.extension
  · have hp : (branchwiseCurrent F).Nonempty := by
      by_contra hn
      have he := Set.not_nonempty_iff_eq_empty.mp hn
      have hz0 : alphaBranchwiseLevelRank F 0 = 0 := by
        simp [alphaBranchwiseLevelRank, rank, he]
      exact (ne_of_gt (hfirst 0 (by omega))) hz0
    obtain ⟨p, hp⟩ := hp
    obtain ⟨D, hD⟩ := closureSearch_common_suffix_bound F k
    let N := k + D
    refine ⟨N, Nat.le_add_right k _, fun U hc => ?_⟩
    obtain ⟨i, hi, hm⟩ := closure_reached_by_bound k D hD hc
    have he : i + (N - i) = N := Nat.add_sub_of_le hi
    rw [← he]
    exact closed_mem_later_level hm hc.closed (hc.extension.current.locals hp) (N - i)

/-- C.15 with the rank modulo permutations fixing the initial
clock names. The expansion levels and the closures themselves are unchanged. -/
theorem all_closures_mem_branchwise_level_at_first_orbit_rank_zero
    (F : TransitionForm Clock Var) (k : ℕ) (hz : orbitBranchwiseLevelRank F k = 0)
    (hfirst : ∀ i < k, 0 < orbitBranchwiseLevelRank F i) :
    ∃ N ≥ k, ∀ U, catalogue.IsClosure F U → U ∈ alphaBranchwiseExpansionLevel F N := by
  exact all_closures_mem_branchwise_level_at_first_rank_zero F k
    (by simpa only [orbitBranchwiseLevelRank_eq] using hz)
    (by simpa only [orbitBranchwiseLevelRank_eq] using hfirst)

run_elab do
  for name in #[``all_closures_mem_branchwise_level_at_first_rank_zero,
      ``all_closures_mem_branchwise_level_at_first_orbit_rank_zero] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "C.15: unexpected axiom {ax}"

end STLTableau.Section3.ConcreteContextual
