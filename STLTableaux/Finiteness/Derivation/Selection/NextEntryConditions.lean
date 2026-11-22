import STLTableaux.Finiteness.Derivation.Selection.NextEntryProvenance
import STLTableaux.Finiteness.Derivation.BoundaryRuleConditions
import STLTableaux.Finiteness.Derivation.Selection.SelectedBoundedLedger
import STLTableaux.Finiteness.Derivation.Selection.SelectedResetMap

/-! Successor numeric eligibility from the complete next state's own truth,
and exact right-endpoint transfer using current reset-map agreement. No branch
satisfaction at an unknown recursive valuation is assumed. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*} [DecidableEq Clock]

/-- Whole-next truth supplies the actual marker. A strict entry leaves c
unreset, so elapsed nonnegativity/adjacency supplies the boundary comparison.
Truth of the timed formula on this successor is still a separate origin fact. -/
theorem SelectedTree.ledger_upper_successor_conditions
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var} (T : SelectedTree E U owned H Er)
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization H F)
    {N : Section3.StateForm Clock Var} (hn : F.nextPart=some N)
    {entry : RawLedgerEntry (Clock:=Clock) (Var:=Var)} (he : entry∈T.rawLedger)
    {K : MixedJ Clock Var} (hK : Conjunct entry.body (.next K))
    (c d : Clock) (m q : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hsource : ∃b,entry.source=.upper c b kind I φ)
    (hq : Predicate.bounded c d m q kind I φ ∈ K.currentPredicates)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (τ : ClockValuation Clock)
    (i : Fin P.size) (hnext : i.1+1<P.size)
    (hN : N.holds σ P (ClockResetSet.elapse τ (STLTableau.Judgement.duration P i)) ⟨i.1+1,by omega⟩) :
    ∃ell, q=Marker.complement ell ∧ ell=(P.interval ⟨i.1+1,hnext⟩).leftBoundary ∧
      Local.marker ell∈N.locals ∧ N.resets.value d=some 0 ∧
      (N.resets.apply (ClockResetSet.elapse τ (STLTableau.Judgement.duration P i)) d : ℝ)=0 ∧
      (Marker.imp ell m=Marker.open → N.resets.value c=none) ∧
      (0 : ℝ) <[Marker.imp ell m]
        (N.resets.apply (ClockResetSet.elapse τ (STLTableau.Judgement.duration P i)) c : ℝ) ∧
      Nonempty (FrozenByUpper c d m ell kind I φ) := by
  obtain ⟨ell,hqell,hm,hd,hc,hf⟩ := T.ledger_upper_entry hSafe hn he hK c d m q kind I φ hsource hq
  have hmarker := hN.2 (.marker ell) hm
  have hell : ell=(P.interval ⟨i.1+1,hnext⟩).leftBoundary := by
    exact (show (P.interval ⟨i.1+1,hnext⟩).leftBoundary=ell from by
      simpa only [Local.holds,Local.toJudgement,Section3.Judgement.holds,dif_pos hnext] using hmarker).symm
  refine ⟨ell,hqell,hell,hm,hd,?_,hc,?_,hf⟩
  · simp only [ClockResetSet.apply,hd]
    rfl
  · cases hb : Marker.imp ell m with
    | closed =>
        simpa only [markedLT_closed] using (N.resets.apply (ClockResetSet.elapse τ (STLTableau.Judgement.duration P i)) c).coe_nonneg
    | «open» =>
        have hval : N.resets.apply (ClockResetSet.elapse τ (STLTableau.Judgement.duration P i)) c =
            ClockResetSet.elapse τ (STLTableau.Judgement.duration P i) c := by
          simp only [ClockResetSet.apply,hc hb]
        rw [hval]
        have hcomp := boundary_comparison_after_elapse σ P τ i hnext c m
        rw [← hell,hb] at hcomp
        exact hcomp

omit [DecidableEq Clock] in
/-- Current selected-output reset agreement and actual next d-unreset preserve
the represented endpoint across this concrete partition successor. -/
theorem endpoint_next_of_reset_agreement
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (i : Fin P.size) (hnext : i.1+1<P.size) (d : Clock)
    (R S Nresets : ClockResetSet Clock) (hmap : S.value d=R.value d) (hn : Nresets.value d=none) :
    RightClockAge.endpoint d (P.interval ⟨i.1+1,hnext⟩).left
      (Nresets.apply (ClockResetSet.elapse (S.apply α) (STLTableau.Judgement.duration P i))) =
      RightClockAge.endpoint d (P.interval i).left (R.apply α) := by
  rw [RightClockAge.endpoint_reset d _ _ Nresets hn]
  change (P.interval ⟨i.1+1,hnext⟩).left -
      (ClockResetSet.elapse (S.apply α) (STLTableau.Judgement.duration P i) d : ℝ) =
    (P.interval i).left - (R.apply α d : ℝ)
  have he : S.apply α d=R.apply α d := by simp only [ClockResetSet.apply,hmap]
  exact (STLTableau.Judgement.next_left_sub_elapse_eq P (S.apply α) i hnext d).trans
    (congrArg (fun v : NNReal => (P.interval i).left - (v : ℝ)) he)

/-- Apply endpoint transfer to an actual bounded continuation in this tree;
both the complete next d-unreset and current reset-map agreement are derived
from this same tree and its actual input `↑↓` source. -/
theorem SelectedTree.ledger_bounded_endpoint
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var} (T : SelectedTree E U owned H Er)
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization H F)
    {N : Section3.StateForm Clock Var} (hn : F.nextPart=some N)
    {entry : RawLedgerEntry (Clock:=Clock) (Var:=Var)} (he : entry∈T.rawLedger)
    {K : MixedJ Clock Var} (hK : Conjunct entry.body (.next K))
    (c d : Clock) (b q m q' : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hsource : entry.source=.bounded c d b q kind I φ)
    (hq : Predicate.bounded c d m q' kind I φ∈K.currentPredicates)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (i : Fin P.size) (hnext : i.1+1<P.size) :
    RightClockAge.endpoint d (P.interval ⟨i.1+1,hnext⟩).left
      (N.resets.apply (ClockResetSet.elapse (F.current.resets.apply α) (STLTableau.Judgement.duration P i))) =
      RightClockAge.endpoint d (P.interval i).left (R.apply α) := by
  have hb : IsBoundedPredicate entry.source := by rw [hsource]; trivial
  have hmem := T.bounded_ledger_origin he hb
  have hbound : Local.predicate (.bounded c d b q kind I φ)∈owned.locals := hsource ▸ hmem
  have hdCanonical : d∈syntaxClocks owned.canonical :=
    canonical_local_support owned.shape hbound (Or.inr (Set.mem_singleton d))
  have hdW : d∈W := owned.covers_input (Or.inl (Or.inr hdCanonical))
  have hmap := T.normalized_reset_agreement hSafe d hdW
  apply endpoint_next_of_reset_agreement σ P α i hnext d R F.current.resets N.resets hmap
  exact T.ledger_bounded_right_unreset hSafe hn he hK c d b q m q' kind I φ hsource hq

end STLTableau.Section4.Finiteness
