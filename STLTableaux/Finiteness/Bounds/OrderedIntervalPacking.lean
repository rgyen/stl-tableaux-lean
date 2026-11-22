import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
A numeric packing bound for a finite ordered list of real intervals.
This file makes no claim about connected components or tableau paths.
-/

namespace OrderedIntervalPacking

/-- If `n` ordered intervals lie in `[u, u + b]`, each has length at least
`w`, and successive intervals do not overlap in their interiors, then their
minimum total length is at most `b`. Endpoint contact is allowed. -/
theorem mul_width_le
    (n : ℕ) (L R : ℕ → ℝ) (u b w : ℝ)
    (hb : 0 ≤ b)
    (hleft : ∀ i, i < n → u ≤ L i)
    (hright : ∀ i, i < n → R i ≤ u + b)
    (hwidth : ∀ i, i < n → w ≤ R i - L i)
    (hordered : ∀ i, i + 1 < n → R i ≤ L (i + 1)) :
    (n : ℝ) * w ≤ b := by
  have hprefix : ∀ i, i < n → u + ((i : ℝ) + 1) * w ≤ R i := by
    intro i
    induction i with
    | zero =>
        intro hi
        have hl := hleft 0 hi
        have hw := hwidth 0 hi
        norm_num at *
        linarith
    | succ i ih =>
        intro hi
        have hp := ih (by omega)
        have ho := hordered i hi
        have hw := hwidth (i + 1) hi
        push_cast
        linarith
  cases n with
  | zero => simpa using hb
  | succ k =>
      have hp := hprefix k (by omega)
      have hr := hright k (by omega)
      push_cast
      linarith

/-- The corresponding natural-number packing bound for strictly positive width. -/
theorem le_floor_div_width
    (n : ℕ) (L R : ℕ → ℝ) (u b w : ℝ)
    (hb : 0 ≤ b) (hw : 0 < w)
    (hleft : ∀ i, i < n → u ≤ L i)
    (hright : ∀ i, i < n → R i ≤ u + b)
    (hwidth : ∀ i, i < n → w ≤ R i - L i)
    (hordered : ∀ i, i + 1 < n → R i ≤ L (i + 1)) :
    n ≤ ⌊b / w⌋₊ := by
  apply Nat.le_floor
  exact (le_div_iff₀ hw).2
    (mul_width_le n L R u b w hb hleft hright hwidth hordered)

#print axioms mul_width_le
#print axioms le_floor_div_width

end OrderedIntervalPacking
