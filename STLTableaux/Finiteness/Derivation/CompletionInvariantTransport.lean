import STLTableaux.Finiteness.Derivation.DerivationNormalizationSoundness
import STLTableaux.Closure.Subsumption.InvariantTransport

/-! Full invariant and stability transport for recursive completion. All
correspondences follow from the actual structural rules and safety certificates;
no semantic transport premise is added. StructuralEq is the ACIdem alias. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

 theorem ACIdem.invariant_iff {J K : MixedJ Clock Var} (h : ACIdem J K)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    J.EvaluatedInvariant σ P α k ↔ K.EvaluatedInvariant σ P α k := by
  induction h generalizing α with
  | refl => rfl
  | symm h ih => exact (ih α).symm
  | trans h g ih ig => exact (ih α).trans (ig α)
  | assoc => exact and_assoc
  | comm => exact and_comm
  | idem => exact and_self_iff
  | conj h g ih ig => exact and_congr (ih α) (ig α)
  | reset R h ih => exact ih (R.apply α)
  | resetDistrib R J K => rfl
  | resetUnused R J hd =>
    exact Section3.Judgement.evaluatedInvariant_congr_of_agree σ P J _ _ k
      (reset_apply_agrees_on_free R J hd α)
  | resetNested R S J =>
    simp only [Section3.Judgement.EvaluatedInvariant,ClockResetSet.apply_union_eq_comp]

 theorem ACIdem.underlyingFormulas_eq {J K : MixedJ Clock Var} (h : ACIdem J K) :
    J.underlyingFormulas = K.underlyingFormulas := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig
  | assoc => exact Set.union_assoc _ _ _
  | comm => exact Set.union_comm _ _
  | idem => exact Set.union_self _
  | conj h g ih ig => exact congrArg₂ Set.union ih ig
  | reset R h ih => exact ih
  | resetDistrib R J K => rfl
  | resetUnused R J hd => rfl
  | resetNested R S J => rfl

 theorem ACIdem.stable_iff {J K : MixedJ Clock Var} (h : ACIdem J K)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) :
    J.UnderlyingStable σ P ↔ K.UnderlyingStable σ P := by
  unfold Section3.Judgement.UnderlyingStable
  rw [h.underlyingFormulas_eq]

 theorem union_fullInvariant_iff {F G : Section3.TransitionForm Clock Var}
    (h : F.UnionCompatible G) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :
    (F.union G).EvaluatedInvariant σ P α k ↔
      F.EvaluatedInvariant σ P α k ∧ G.EvaluatedInvariant σ P α k :=
  ⟨fun hi => ⟨h.left.evaluatedInvariant σ P α k hi,h.right.evaluatedInvariant σ P α k hi⟩,
    fun hi => h.evaluatedInvariant σ P α k hi.1 hi.2⟩

/-- Both directions preserve the FULL invariant, including scoped eventuality
clauses for no past satisfaction. This extends the frozen safety API from a separate module. -/
theorem SafeNormalization.fullInvariant {J : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : SafeNormalization J F)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    F.EvaluatedInvariant σ P α k ↔ J.EvaluatedInvariant σ P α k := by
  induction h generalizing α k with
  | terminal => simp [Section3.TransitionForm.ofState,Section3.TransitionForm.EvaluatedInvariant,
      Section3.StateForm.ofLocal,Section3.StateForm.EvaluatedInvariant,Local.EvaluatedInvariant,
      Local.toJudgement,Section3.Judgement.EvaluatedInvariant]
  | clock c r a => simp [Section3.TransitionForm.ofState,Section3.TransitionForm.EvaluatedInvariant,
      Section3.StateForm.ofGuard,Section3.StateForm.EvaluatedInvariant,Section3.Judgement.EvaluatedInvariant]
  | marker m => simp [Section3.TransitionForm.ofState,Section3.TransitionForm.EvaluatedInvariant,
      Section3.StateForm.ofLocal,Section3.StateForm.EvaluatedInvariant,Local.EvaluatedInvariant,
      Local.toJudgement,Section3.Judgement.EvaluatedInvariant]
  | predicate p => simp [Section3.TransitionForm.ofState,Section3.TransitionForm.EvaluatedInvariant,
      Section3.StateForm.ofLocal,Section3.StateForm.EvaluatedInvariant,Local.EvaluatedInvariant,
      Local.toJudgement,Section3.Judgement.EvaluatedInvariant,ClockResetSet.apply_empty]
  | conj h g hc ih ig =>
    exact (union_fullInvariant_iff hc σ P α k).trans (and_congr (ih α k) (ig α k))
  | reset R h hd ih =>
    exact (Section3.TransitionForm.underReset_evaluatedInvariant _ R σ P α k).trans (ih (R.apply α) k)
  | @next J F h hn ih =>
    simp only [Section3.TransitionForm.ofNextState,Section3.TransitionForm.EvaluatedInvariant,
      Section3.StateForm.empty,Section3.StateForm.EvaluatedInvariant,Set.mem_empty_iff_false,
      IsEmpty.forall_iff,implies_true,true_and,Option.some.injEq,forall_eq',ClockResetSet.apply_empty,
      Section3.Judgement.EvaluatedInvariant]
    apply forall_congr'
    intro hk
    simpa [Section3.TransitionForm.EvaluatedInvariant,Section3.StateForm.EvaluatedInvariant,hn] using ih _ _

 theorem SafeNormalization.stable {J : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : SafeNormalization J F)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) :
    F.UnderlyingStable σ P ↔ J.UnderlyingStable σ P :=
  Section3.TransitionForm.normalize_underlyingStable J h.normalizes σ P

end STLTableau.Section4.Finiteness
