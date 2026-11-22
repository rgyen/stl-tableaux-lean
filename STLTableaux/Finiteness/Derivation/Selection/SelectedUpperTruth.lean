import STLTableaux.Finiteness.Derivation.Selection.SelectedUpperConsumption
import STLTableaux.Finiteness.Derivation.Selection.SelectedRetainedPredicates

/-! Truth of newly expanded temporal uppers comes from actual plain expansion
or initial semantic eligibility, never from the retained upper alone. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

omit [DecidableEq Clock] in
private theorem current_plain_truth (J : MixedJ Clock Var) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hp : Predicate.plain φ ∈ J.currentPredicates) (hs : Judgement.holds σ P α k J) :
    Judgement.holds σ P α k (.predicate (.plain φ)) := by
  induction J generalizing α with
  | predicate q =>
    have he : Predicate.plain φ = q := hp
    subst q
    exact hs
  | conj J K ih ik =>
    rcases hp with hp | hp
    · exact ih α hp hs.1
    · exact ik α hp hs.2
  | reset R J ih => exact ih (R.apply α) hp hs
  | next | terminal | marker | clock => cases hp

/-- Every actual upper credit is true as an unclocked predicate on this piece. Ordinary
unclocked sources are recovered from full H; boundary sources are recovered in the
original owned input and discharged by the actual Eligibility.current fact. -/
theorem SelectedTree.upper_credit_plain_truth
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hEligible : Eligibility E owned U σ P α k)
    (hHolds : Judgement.holds σ P α k H)
    {φ : Formula Var} (hcredit : φ ∈ T.upperCredits) :
    Judgement.holds σ P α k (.predicate (.plain φ)) := by
  rcases T.upper_credit_source hcredit with ⟨entry,he,hs⟩ | ⟨q,b,hq,hformula⟩
  · have hn : ¬(Predicate.plain φ : Predicate Clock Var).IsAtomic := by
      rw [← hs]
      exact entry.actual.source_nonatomic
    exact current_plain_truth H φ σ P α k
      ((T.retained_nonatomic_iff _ hn).2 ⟨entry,he,hs⟩) hHolds
  · obtain ⟨hb,he,hm⟩ := T.boundary_consumed_origin hq
    obtain ⟨c,d,m,ℓ,kind,I,ψ,hdef,hf,hmarker,hd,hplain,hcomp,hU⟩ := hEligible.current q he hm
    have hformula' : q.formula = timedFormula kind I ψ := by
      rw [hdef]
      cases kind <;> rfl
    have heq := hformula'.symm.trans hformula
    rw [heq] at hplain
    exact hplain

/-- An actual upper raw-ledger source is backed by satisfaction of the unclocked temporal
predicate on the
current piece, assuming the actual incoming state has no upper locals. -/
theorem SelectedTree.upper_ledger_plain_truth
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hEligible : Eligibility E owned U σ P α k)
    (hHolds : Judgement.holds σ P α k H)
    (hno : ∀ c m kind I φ, Local.predicate (.upper c m kind I φ) ∉ owned.locals)
    {entry : RawLedgerEntry (Clock := Clock) (Var := Var)} (he : entry ∈ T.rawLedger)
    (c : Clock) (m : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hs : entry.source = .upper c m kind I φ) :
    Judgement.holds σ P α k (.predicate (.plain (timedFormula kind I φ))) := by
  have hm : timedFormula kind I φ ∈ T.upperExpanded := by
    rw [T.upperExpanded_eq_rawLedger]
    exact List.mem_filterMap.mpr ⟨entry,he,by rw [hs]⟩
  exact T.upper_credit_plain_truth σ P α k hEligible hHolds (T.upperExpanded_credit hno hm)
end STLTableau.Section4.Finiteness
