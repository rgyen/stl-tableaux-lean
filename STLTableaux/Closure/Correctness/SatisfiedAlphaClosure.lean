import STLTableaux.Closure.Normalization.ClosureAlphaNext
import STLTableaux.Tableau.Stability.ClosureStability

/-! Iteration of genuine minimal expansions with capture-free source
representatives. A path records actual next-binder permutations, so the
initial source can be transported along the same choices without losing
literal subsumption at the final minimization step. -/
namespace STLTableau
open scoped STL
variable {Clock Var : Type*}

/-- Finite capture-free next-binder renamings; no semantic property is a constructor. -/
inductive NextAlphaPath : TransitionForm Clock Var → TransitionForm Clock Var → Prop
  | refl (Φ) : NextAlphaPath Φ Φ
  | step (Φ) (e : Equiv.Perm Clock)
      (hfix : ∀ N, Φ.nextPart = some N →
        ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c)
      {Ψ} : NextAlphaPath (Φ.alphaNext e) Ψ → NextAlphaPath Φ Ψ

namespace NextAlphaPath

theorem trans {Φ Ψ Χ : TransitionForm Clock Var}
    (h : NextAlphaPath Φ Ψ) (g : NextAlphaPath Ψ Χ) : NextAlphaPath Φ Χ := by
  induction h with
  | refl => exact g
  | step Φ e hf tail ih => exact .step Φ e hf (ih g)

theorem alphaEquivalent {Φ Ψ : TransitionForm Clock Var} (h : NextAlphaPath Φ Ψ) :
    Ψ.AlphaEquivalent Φ := by
  induction h with
  | refl => exact .refl _
  | step Φ e hf tail ih => exact ih.trans (.next Φ e hf)

theorem current {Φ Ψ : TransitionForm Clock Var} (h : NextAlphaPath Φ Ψ) :
    Ψ.current = Φ.current := by
  induction h with
  | refl => rfl
  | step Φ e hf tail ih => exact ih

theorem rank [DecidableEq Clock] {Φ Ψ : TransitionForm Clock Var} (h : NextAlphaPath Φ Ψ) :
    AlphaBranchRepresentation.expansionRules.rank Ψ =
      AlphaBranchRepresentation.expansionRules.rank Φ := by
  induction h with
  | refl => rfl
  | step Φ e hf tail ih => exact ih.trans (AlphaBranchRepresentation.rank_alphaNext Φ e hf)

/-- Transport the smaller source along the larger source's actual path.
Fresh-subsumption side conditions ensure the inherited bindings remain safe. -/
theorem transport_subsumed {Φ Ψ Ψa : TransitionForm Clock Var}
    (hsub : Φ ⊑ Ψ) (hpath : NextAlphaPath Ψ Ψa) :
    ∃ Φa, NextAlphaPath Φ Φa ∧ (Φa ⊑ Ψa) := by
  induction hpath generalizing Φ with
  | refl => exact ⟨Φ,.refl Φ,hsub⟩
  | step Ψ e hf tail ih =>
      have hsmall := hsub.next_fix_of_subsumed e hf
      obtain ⟨Φa,hpath,hsub'⟩ := ih (hsub.alphaNext e hsmall)
      exact ⟨Φa,.step Φ e hsmall hpath,hsub'⟩

end NextAlphaPath

namespace AlphaBranchRepresentation
variable [DecidableEq Clock] [Infinite Clock]

/-- Well-founded iteration and final literal minimization. This generic
lemma isolates only ordinary property preservation; neither a closed upper
bound nor compatibility is assumed. Its concrete invariant/stability instance
is supplied separately. -/
theorem satisfied_alphaClosure_from_steps
    (Property : TransitionForm Clock Var → Prop)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hstep : ∀ Φ p, Property Φ → Φ.Satisfies σ P α k →
      Judgement.predicate p ∈ Φ.current.locals → ¬ expansionRules.RuleClosedFor Φ p →
      ∃ (e : Equiv.Perm Clock) (U : TransitionForm Clock Var),
        (∀ N, Φ.nextPart = some N →
          ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) ∧
        expansionRules.PExpansion p (Φ.alphaNext e) U ∧
        U.Satisfies σ P α k ∧ Property U)
    (Φ : TransitionForm Clock Var) (hprop : Property Φ) (hs : Φ.Satisfies σ P α k) :
    ∃ Φa U : TransitionForm Clock Var, NextAlphaPath Φ Φa ∧
      expansionRules.IsClosure Φa U ∧ U.Satisfies σ P α k := by
  classical
  have hw : WellFounded (fun F G : TransitionForm Clock Var =>
      ExpansionRules.RankLT (expansionRules.rank F) (expansionRules.rank G)) :=
    ExpansionRules.rankLT_wellFounded.onFun
  have aux : ∀ F : TransitionForm Clock Var, Property F → F.Satisfies σ P α k →
      ∃ Fa U : TransitionForm Clock Var, NextAlphaPath F Fa ∧ (Fa ⊑ U) ∧ expansionRules.IsClosed U ∧
        U.Satisfies σ P α k := by
    intro F
    induction F using hw.induction with
    | h F ih =>
        intro hpropF hsF
        by_cases hclosed : expansionRules.IsClosed F
        · exact ⟨F,F,.refl F,syntacticallySubsumed_refl ∅ F (by simp),hclosed,hsF⟩
        · obtain ⟨p,hp,hopen⟩ : ∃ p, Judgement.predicate p ∈ F.current.locals ∧
              ¬ expansionRules.RuleClosedFor F p := by
            simpa [ExpansionRules.IsClosed] using hclosed
          obtain ⟨e,U,hfix,hexp,hsU,hpropU⟩ := hstep F p hpropF hsF hp hopen
          have hopen' : ¬ expansionRules.RuleClosedFor (F.alphaNext e) p := by
            simpa only [ruleClosed_alphaNext_iff e hfix] using hopen
          have hlt : ExpansionRules.RankLT (expansionRules.rank U) (expansionRules.rank F) := by
            rw [← rank_alphaNext F e hfix]
            exact hexp.rankDecrease hopen'
          obtain ⟨Ua,V,hpathU,hsubUV,hclosedV,hsV⟩ := ih U hlt hpropU hsU
          obtain ⟨Fa,hpathF,hsubF⟩ := NextAlphaPath.transport_subsumed hexp.extension hpathU
          exact ⟨Fa,V,.step F e hfix hpathF,hsubF.trans hsubUV,hclosedV,hsV⟩
  obtain ⟨Φa,U,hpath,hsub,hclosed,hsU⟩ := aux Φ hprop hs
  obtain ⟨V,hV,hVU⟩ := ExpansionRules.closure_exists_of_closed_extension hsub hclosed
  exact ⟨Φa,V,hpath,hV,transitionForm_subsumption_sound hVU hsU⟩

/-- Concrete residual-catalogue completeness up to the compatible
representative convention. Compatibility, rank decrease, invariant transport,
and current-formula stability preservation are all proved, not caller premises.
The faithful interval semantics is a separate layer. -/
theorem satisfied_alphaClosure_exists
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (hk : k.1 < P.size)
    (Φ : TransitionForm Clock Var) (hi : Φ.InvariantAt P α k hk)
    (hst : ExpansionRules.AllCurrentPredicates Φ (fun q => σ.StablePartition q.formula P))
    (hs : Φ.Satisfies σ P α k) :
    ∃ U : TransitionForm Clock Var, expansionRules.AlphaClosure Φ U ∧ U.Satisfies σ P α k := by
  let Property := fun F : TransitionForm Clock Var =>
    F.InvariantAt P α k hk ∧
      ExpansionRules.AllCurrentPredicates F (fun q => σ.StablePartition q.formula P)
  have hstep : ∀ F p, Property F → F.Satisfies σ P α k →
      Judgement.predicate p ∈ F.current.locals → ¬ expansionRules.RuleClosedFor F p →
      ∃ (e : Equiv.Perm Clock) (U : TransitionForm Clock Var),
        (∀ N, F.nextPart = some N →
          ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) ∧
        expansionRules.PExpansion p (F.alphaNext e) U ∧
        U.Satisfies σ P α k ∧ Property U := by
    intro F p hprop hsF hp hopen
    have hhas : expansionRules.HasRule p := by
      by_contra hno
      exact hopen ⟨hp,Or.inl hno⟩
    obtain ⟨R,hr⟩ := hhas
    obtain ⟨Ψ,hΨ,hbranch⟩ := hr.branch_complete σ P (F.current.resets.apply α) k
      (fun _ => hprop.1.1 p hp) (hprop.2 p hp) (hsF.2.1 (.predicate p) hp)
    obtain ⟨e,U,hfix,hexp,hsU⟩ := satisfied_pExpansion_nextPermutation hp hr hΨ σ P α k hsF hbranch
    have ha : (F.alphaNext e).AlphaEquivalent F := .next F e hfix
    have hiF : (F.alphaNext e).InvariantAt P α k hk := (ha.invariantAt P α k hk).2 hprop.1
    have hnon : U.NonPredicateSatisfies σ P α k :=
      TransitionForm.nonPredicateSatisfies_of_atomicProjection
        (TransitionForm.atomicProjection_satisfies_of hsU)
    have hiU := hexp.preservesInvariantAt_of_ruleInvariant
      expansionRules_preservesEvaluatedInvariant P α k hk hnon hiF
    have hstableF : ExpansionRules.AllCurrentPredicates (F.alphaNext e)
        (fun q => σ.StablePartition q.formula P) := hprop.2
    exact ⟨e,U,hfix,hexp,hsU,hiU,expansion_preservesCurrentStability hexp hstableF⟩
  obtain ⟨Φa,U,hpath,hclosure,hsU⟩ := satisfied_alphaClosure_from_steps Property σ P α k
    hstep Φ ⟨hi,hst⟩ hs
  exact ⟨U,⟨Φa,U,hpath.alphaEquivalent,hclosure,.refl U⟩,hsU⟩

end AlphaBranchRepresentation
end STLTableau
