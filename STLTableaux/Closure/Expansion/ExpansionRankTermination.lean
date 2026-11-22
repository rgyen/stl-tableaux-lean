import STLTableaux.Closure.Expansion.FaithfulPExpansion

/-! Natural-number descent used by the eventual-zero argument.
The sequence supplied by the final application is the actual level maximum,
not a replacement potential. -/
namespace STLTableau.Section3

theorem rank_le_initial_sub (a : ℕ → ℕ)
    (hdecrease : ∀ i, 0 < a i → a (i+1) < a i)
    (hzero : ∀ i, a i = 0 → a (i+1) = 0) :
    ∀ i, a i ≤ a 0 - i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
      by_cases hz : a i = 0
      · rw [hzero i hz]
        exact Nat.zero_le _
      · have hd := hdecrease i (Nat.pos_of_ne_zero hz)
        omega

theorem eventually_zero_of_rank_decrease (a : ℕ → ℕ)
    (hdecrease : ∀ i, 0 < a i → a (i+1) < a i)
    (hzero : ∀ i, a i = 0 → a (i+1) = 0) :
    ∃ k : ℕ, ∀ i ≥ k, a i = 0 := by
  refine ⟨a 0, ?_⟩
  intro i hi
  have hb := rank_le_initial_sub a hdecrease hzero i
  omega

end STLTableau.Section3
