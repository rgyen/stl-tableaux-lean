import STLTableaux.Finiteness.Derivation.BoundaryReplacementSupport
import STLTableaux.Finiteness.Derivation.BoundaryInvariant
import STLTableaux.Finiteness.Derivation.CompletionInvariantTransport

/-! Fixed-signal semantic transfer for the literal boundary replacement.
Optional plain truth is explicit. No occurrence provenance is inferred. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*}

private theorem singleton_unused [DecidableEq Clock] (d : Clock) (J : MixedJ Clock Var)
    (hd : d ∉ J.freeClocks) : StructuralEq (.reset (ClockResetSet.singleton d 0) J) J := by
  apply ACIdem.resetUnused
  rw [ClockResetSet.clocks_singleton]
  exact Set.disjoint_singleton_left.2 hd

private theorem input_holds_parts [DecidableEq Clock] (required : Bool)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (c d : Clock) (m ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) (Γ : MixedJ Clock Var)
    (h : Judgement.holds σ P α k (boundaryReplacementInput required c d m ℓ kind I φ Γ)) :
    Judgement.holds σ P ((ClockResetSet.singleton d 0).apply α) k
      (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ)) ∧
    Judgement.holds σ P ((ClockResetSet.singleton d 0).apply α) k (.marker ℓ) ∧
    Judgement.holds σ P ((ClockResetSet.singleton d 0).apply α) k Γ ∧
    (required = true → Judgement.holds σ P ((ClockResetSet.singleton d 0).apply α) k
      (.predicate (.plain (timedFormula kind I φ)))) := by
  cases required with
  | false => exact ⟨h.1,h.2.1,h.2.2,by intro he; cases he⟩
  | true => exact ⟨h.1.1,h.2.1,h.2.2,fun _ => h.1.2⟩

theorem boundaryReplacement_position_lt [DecidableEq Clock] (required : Bool)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (c d : Clock) (m ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) (Γ : MixedJ Clock Var)
    (h : Judgement.holds σ P α k (boundaryReplacementInput required c d m ℓ kind I φ Γ)) :
    k.1 < P.size := by
  have hb := (input_holds_parts required σ P α k c d m ℓ kind I φ Γ h).1
  by_contra hk
  simp [Section3.Judgement.holds,hk] at hb

theorem boundaryReplacement_ready [DecidableEq Clock] (required : Bool)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (Γ : MixedJ Clock Var)
    (h : (boundaryReplacementInput required c d m ℓ kind I φ Γ).Ready) :
    (boundaryReplacementChild c m ℓ kind I φ Γ).Ready := by
  cases required <;> cases hg : Marker.imp ℓ m <;>
    simp_all [boundaryReplacementInput,boundaryReplacementChild,withBoundaryGuard,
      Section3.Judgement.Ready,Predicate.Ready]

theorem boundaryReplacement_holds [DecidableEq Clock] (required : Bool)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (c d : Clock) (m ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) (Γ : MixedJ Clock Var)
    (hcd : c ≠ d) (hdΓ : d ∉ Γ.freeClocks)
    (hc : (0 : ℝ) <[Marker.imp ℓ m] (α c : ℝ))
    (hplain : required = false → Judgement.holds σ P α k (.predicate (.plain (timedFormula kind I φ))))
    (h : Judgement.holds σ P α k (boundaryReplacementInput required c d m ℓ kind I φ Γ)) :
    Judgement.holds σ P α k (boundaryReplacementChild c m ℓ kind I φ Γ) := by
  obtain ⟨hb,hm,hΓ,ht⟩ := input_holds_parts required σ P α k c d m ℓ kind I φ Γ h
  let β := (ClockResetSet.singleton d 0).apply α
  have hβc : β c = α c := ClockResetSet.apply_singleton_of_ne 0 α hcd
  have hβd : (β d : ℝ) = 0 := by simp [β]
  have hpos := boundaryReplacement_position_lt required σ P α k c d m ℓ kind I φ Γ h
  have hmarker : ∀hk : k.1 < P.size, ℓ = (P.interval ⟨k.1,hk⟩).leftBoundary := by
    intro hk
    exact (show (P.interval ⟨k.1,hk⟩).leftBoundary = ℓ from by
      simpa only [Section3.Judgement.holds,dif_pos hk] using hm).symm
  have hplainβ : Judgement.holds σ P β k (.predicate (.plain (timedFormula kind I φ))) := by
    cases hr : required with
    | true => exact ht hr
    | false =>
      exact ((singleton_unused d (.predicate (.plain (timedFormula kind I φ))) (by
        intro hx; exact hx)).holds_iff σ P α k).2 (hplain hr)
  have huβ := (boundary_merge_at σ P β k c d m ℓ kind I φ hβd hmarker (by rw [hβc]; exact hc)).1 ⟨hb,hplainβ⟩
  have hu := ((singleton_unused d (.predicate (.upper c m kind I φ)) (by
    change d ∉ ({c} : Set Clock); exact Ne.symm hcd)).holds_iff σ P α k).1 huβ
  have hΓα := ((singleton_unused d Γ hdΓ).holds_iff σ P α k).1 hΓ
  refine ⟨hu,?_,(withBoundaryGuard_holds σ P α k c (Marker.imp ℓ m) Γ).2 ⟨hc,hΓα⟩⟩
  simpa only [Section3.Judgement.holds,dif_pos hpos] using hm

theorem boundaryReplacement_invariant [DecidableEq Clock] (required : Bool)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (c d : Clock) (m ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) (Γ : MixedJ Clock Var)
    (hcd : c ≠ d) (hdΓ : d ∉ Γ.freeClocks)
    (h : (boundaryReplacementInput required c d m ℓ kind I φ Γ).EvaluatedInvariant σ P α k) :
    (boundaryReplacementChild c m ℓ kind I φ Γ).EvaluatedInvariant σ P α k := by
  have hb : Section3.Judgement.EvaluatedInvariant σ P ((ClockResetSet.singleton d 0).apply α) k
      (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ)) := by
    cases required
    · exact h.1
    · exact h.1.1
  have hΓ : Γ.EvaluatedInvariant σ P ((ClockResetSet.singleton d 0).apply α) k := by
    cases required <;> exact h.2.2
  have huβ : Section3.Judgement.EvaluatedInvariant σ P ((ClockResetSet.singleton d 0).apply α) k
      (.predicate (.upper c m kind I φ)) := by
    intro hk
    exact BoundaryInvariant.invariant_bounded_to_upper σ P _ k hk c d m (¬ₘ ℓ) kind I φ (hb hk)
  have hu := ((singleton_unused d (.predicate (.upper c m kind I φ)) (by
    change d ∉ ({c} : Set Clock); exact Ne.symm hcd)).invariant_iff σ P α k).1 huβ
  have hΓα := ((singleton_unused d Γ hdΓ).invariant_iff σ P α k).1 hΓ
  change _ ∧ True ∧ _
  refine ⟨hu,trivial,?_⟩
  cases hg : Marker.imp ℓ m <;> simpa only [withBoundaryGuard,hg,Section3.Judgement.EvaluatedInvariant,true_and] using hΓα

theorem boundaryReplacement_underlyingFormulas [DecidableEq Clock] (required : Bool)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (Γ : MixedJ Clock Var) :
    (boundaryReplacementInput required c d m ℓ kind I φ Γ).underlyingFormulas =
      (boundaryReplacementChild c m ℓ kind I φ Γ).underlyingFormulas := by
  cases required <;> cases kind <;> cases hg : Marker.imp ℓ m <;>
    simp [boundaryReplacementInput,boundaryReplacementChild,withBoundaryGuard,hg,
      Section3.Judgement.underlyingFormulas,Predicate.formula,timedFormula]

theorem boundaryReplacement_stable [DecidableEq Clock] (required : Bool)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (Γ : MixedJ Clock Var)
    (h : (boundaryReplacementInput required c d m ℓ kind I φ Γ).UnderlyingStable σ P) :
    (boundaryReplacementChild c m ℓ kind I φ Γ).UnderlyingStable σ P := by
  unfold Section3.Judgement.UnderlyingStable at h ⊢
  rw [← boundaryReplacement_underlyingFormulas required c d m ℓ kind I φ Γ]
  exact h

end STLTableau.Section4.Finiteness
