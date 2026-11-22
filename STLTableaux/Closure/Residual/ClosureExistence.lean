/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Closure.Residual.AlphaClosure

/-! # Existence of minimal expansions and closures -/
namespace STLTableau
open scoped STL
namespace ExpansionRules
variable {Clock Var : Type*}

/-- A rule-closed extension suffices; a closure need not already be given. -/
theorem pExpansion_exists_of_extension {E : ExpansionRules Clock Var}
    {Φ U : TransitionForm Clock Var} {p : IntervalPredicate Clock Var}
    (hp : Judgement.predicate p ∈ Φ.current.locals) (hsub : Φ ⊑ U)
    (hu : E.RuleClosedFor U p) :
    ∃ F, E.PExpansion p Φ F ∧ F ⊑ U := by
  classical
  by_cases hc : E.RuleClosedFor Φ p
  · exact ⟨Φ, PExpansion.refl_of_ruleClosed hc, hsub⟩
  let Candidate := fun F : TransitionForm Clock Var =>
    (Φ ⊑ F) ∧ E.RuleClosedFor F p ∧ (F ⊑ U)
  have hrefl : U ⊑ U := syntacticallySubsumed_refl ∅ U (by simp)
  obtain ⟨F, hf⟩ := exists_minimalFor_of_wellFoundedLT Candidate
    TransitionForm.componentCount ⟨U, hsub, hu, hrefl⟩
  refine ⟨F, ⟨hp, Or.inr ⟨hc, hf.1.1, hf.1.2.1, ?_⟩⟩, hf.1.2.2⟩
  intro G hΦG hg hGF
  have hcount := hGF.componentCount_le
  have hmin := hf.2 ⟨hΦG, hg, hGF.trans hf.1.2.2⟩ hcount
  have heq := hGF.eq_of_componentCount_eq (Nat.le_antisymm hcount hmin)
  subst G
  exact hGF

/-- Minimize a closed extension by finite component count. -/
theorem closure_exists_of_closed_extension {E : ExpansionRules Clock Var}
    {Φ U : TransitionForm Clock Var} (hsub : Φ ⊑ U) (hu : E.IsClosed U) :
    ∃ F, E.IsClosure Φ F ∧ F ⊑ U := by
  let Candidate := fun F : TransitionForm Clock Var => (Φ ⊑ F) ∧ E.IsClosed F ∧ (F ⊑ U)
  have hrefl : U ⊑ U := syntacticallySubsumed_refl ∅ U (by simp)
  obtain ⟨F, hf⟩ := exists_minimalFor_of_wellFoundedLT Candidate
    TransitionForm.componentCount ⟨U, hsub, hu, hrefl⟩
  refine ⟨F, ⟨hf.1.1, hf.1.2.1, ?_⟩, hf.1.2.2⟩
  intro G hΦG hg hGF
  have hcount := hGF.componentCount_le
  have hmin := hf.2 ⟨hΦG, hg, hGF.trans hf.1.2.2⟩ hcount
  have heq := hGF.eq_of_componentCount_eq (Nat.le_antisymm hcount hmin)
  subst G
  exact hGF

/-- Local extension availability plus strict rank decrease constructs a closed
extension. No closed upper bound or closure is assumed. -/
theorem closed_extension_exists (E : ExpansionRules Clock Var)
    (hstep : ∀ (Φ : TransitionForm Clock Var) (p : IntervalPredicate Clock Var),
      Judgement.predicate p ∈ Φ.current.locals → ¬ E.RuleClosedFor Φ p →
        ∃ U, (Φ ⊑ U) ∧ E.RuleClosedFor U p)
    (Φ : TransitionForm Clock Var) : ∃ U, (Φ ⊑ U) ∧ E.IsClosed U := by
  classical
  have hw : WellFounded (fun F G : TransitionForm Clock Var => RankLT (E.rank F) (E.rank G)) :=
    rankLT_wellFounded.onFun
  induction Φ using hw.induction with
  | h Φ ih =>
      by_cases hc : E.IsClosed Φ
      · exact ⟨Φ, syntacticallySubsumed_refl ∅ Φ (by simp), hc⟩
      · obtain ⟨p, hp, hopen⟩ : ∃ p, Judgement.predicate p ∈ Φ.current.locals ∧
            ¬ E.RuleClosedFor Φ p := by simpa [IsClosed] using hc
        obtain ⟨U, hΦU, hu⟩ := hstep Φ p hp hopen
        obtain ⟨F, he, _⟩ := pExpansion_exists_of_extension hp hΦU hu
        obtain ⟨G, hFG, hg⟩ := ih F (he.rankDecrease hopen)
        exact ⟨G, he.extension.trans hFG, hg⟩

theorem closure_exists (E : ExpansionRules Clock Var)
    (hstep : ∀ (Φ : TransitionForm Clock Var) (p : IntervalPredicate Clock Var),
      Judgement.predicate p ∈ Φ.current.locals → ¬ E.RuleClosedFor Φ p →
        ∃ U, (Φ ⊑ U) ∧ E.RuleClosedFor U p)
    (Φ : TransitionForm Clock Var) : ∃ U, E.IsClosure Φ U := by
  obtain ⟨G, hΦG, hg⟩ := E.closed_extension_exists hstep Φ
  obtain ⟨U, hu, _⟩ := closure_exists_of_closed_extension hΦG hg
  exact ⟨U, hu⟩

end ExpansionRules
end STLTableau
