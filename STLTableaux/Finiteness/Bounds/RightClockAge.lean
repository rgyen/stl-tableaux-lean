import STLTableaux.Tableau.Construction.Tableau
import STLTableaux.Syntax.Section3Judgements

/-! Right-clock age in literal bounded propagation branches. This proves
preservation after a right endpoint has been represented. It does not establish
where that endpoint originated or how many distinct source intervals exist. -/
namespace STLTableau.Section4.Finiteness.RightClockAge
open Section3
variable {Clock Var : Type*}

/-- An absolute right endpoint represented by clock age at absolute time t. -/
def endpoint (d : Clock) (t : ℝ) (α : ClockValuation Clock) : ℝ := t - (α d : ℝ)

theorem endpoint_elapse (d : Clock) (t : ℝ) (α : ClockValuation Clock) (δ : NNReal) :
    endpoint d (t + δ) (ClockResetSet.elapse α δ) = endpoint d t α := by
  simp only [endpoint,ClockResetSet.elapse,NNReal.coe_add]
  ring

theorem endpoint_reset (d : Clock) (t : ℝ) (α : ClockValuation Clock)
    (R : ClockResetSet Clock) (h : R.value d = none) :
    endpoint d t (R.apply α) = endpoint d t α := by
  unfold endpoint ClockResetSet.apply
  rw [h]

/-- The actual check branch resets c, including when this reset is inside next.
Its right d age is retained precisely because c and d are distinct. -/
theorem endpoint_left_reset [DecidableEq Clock] (c d : Clock) (hcd : c ≠ d)
    (t : ℝ) (α : ClockValuation Clock) (a : NNReal) :
    endpoint d t ((ClockResetSet.singleton c a).apply α) = endpoint d t α := by
  apply endpoint_reset
  simp [ClockResetSet.singleton,hcd.symm]

/-- Exact age at the descendant of a check branch: time elapses first, then
only the left clock is reset by the actual next-scoped reset assignment. -/
theorem right_age_after_next_left_reset [DecidableEq Clock]
    (c d : Clock) (hcd : c ≠ d) (α : ClockValuation Clock) (δ a : NNReal) :
    (ClockResetSet.singleton c a).apply (ClockResetSet.elapse α δ) d = α d + δ := by
  rw [ClockResetSet.apply_singleton_of_ne a _ hcd.symm]
  rfl

theorem endpoint_after_next_left_reset [DecidableEq Clock]
    (c d : Clock) (hcd : c ≠ d) (t : ℝ) (α : ClockValuation Clock) (δ a : NNReal) :
    endpoint d (t + δ) ((ClockResetSet.singleton c a).apply (ClockResetSet.elapse α δ)) =
      endpoint d t α :=
  (endpoint_left_reset c d hcd _ _ a).trans (endpoint_elapse d t α δ)

/-- All nested reset scopes exclude d; next and conjunction are traversed. -/
def NoRightReset (d : Clock) : Section3.Judgement Clock Var → Prop
  | .reset R Ψ => R.value d = none ∧ NoRightReset d Ψ
  | .next Ψ => NoRightReset d Ψ
  | .conj Φ Ψ => NoRightReset d Φ ∧ NoRightReset d Ψ
  | _ => True

def finiteRule [DecidableEq Clock] (kind : TemporalKind) (c d : Clock)
    (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var) : ExpansionRule Clock Var :=
  match kind with
  | .always => ExpansionRule.boundedAlways c d b q I φ
  | .eventually => ExpansionRule.boundedEventually c d b q I φ

def unboundedBranches [DecidableEq Clock] (kind : TemporalKind) (c d : Clock)
    (b q : Marker) (a : NNReal) (φ : Formula Var) : List (UnboundedClocked.Node Clock Var) :=
  match kind with
  | .always => UnboundedClocked.boundedAlwaysBranches c d b q a φ
  | .eventually => UnboundedClocked.boundedEventuallyBranches c d b q a φ

/-- Every literal finite bounded branch, including both propagating schemas,
resets only its left clock or no clock. The finishing schemas satisfy this too. -/
theorem finite_bounded_no_right_reset [DecidableEq Clock]
    (kind : TemporalKind) (c d : Clock) (hcd : c ≠ d) (b q : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) (B : STLTableau.Judgement Clock Var)
    (hB : B ∈ (finiteRule kind c d b q I φ).branches) :
    NoRightReset d (Section3.Judgement.ofFinite B) := by
  cases kind <;>
    simp only [finiteRule,ExpansionRule.boundedAlways,ExpansionRule.boundedEventually,
      List.mem_cons,List.not_mem_nil,or_false] at hB
  all_goals
    rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases b <;> cases q
  all_goals simp [NoRightReset,Section3.Judgement.ofFinite,
    ExpansionRule.boundedAlways_defer,ExpansionRule.boundedAlways_check,
    ExpansionRule.boundedAlways_finish,ExpansionRule.boundedEventually_defer,
    ExpansionRule.boundedEventually_check,ExpansionRule.boundedEventually_finish,
    STLTableau.Judgement.markedLT,STLTableau.Judgement.markedGT,
    Marker.imp,Marker.conj,Marker.notConj,Marker.complement,
    ClockResetSet.singleton,hcd.symm]

/-- The same syntactic fact for the actual infinite-bound versions. -/
theorem unbounded_bounded_no_right_reset [DecidableEq Clock]
    (kind : TemporalKind) (c d : Clock) (hcd : c ≠ d) (b q : Marker)
    (a : NNReal) (φ : Formula Var) (B : UnboundedClocked.Node Clock Var)
    (hB : B ∈ unboundedBranches kind c d b q a φ) :
    NoRightReset d (Section3.Judgement.ofUnbounded B) := by
  cases kind <;>
    simp only [unboundedBranches,UnboundedClocked.boundedAlwaysBranches,
      UnboundedClocked.boundedEventuallyBranches,List.mem_cons,List.not_mem_nil,or_false] at hB
  all_goals rcases hB with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases b <;> cases q
  all_goals simp [NoRightReset,Section3.Judgement.ofUnbounded,
    UnboundedClocked.boundedAlwaysDefer,UnboundedClocked.boundedAlwaysCheck,
    UnboundedClocked.alwaysWait,UnboundedClocked.alwaysLast,
    UnboundedClocked.boundedEventuallyDefer,UnboundedClocked.boundedEventuallyCheck,
    UnboundedClocked.boundedEventuallyFinish,UnboundedClocked.Node.lt,
    UnboundedClocked.Node.gt,ClockResetSet.singleton,hcd.symm]

/-- Evaluate the endpoint through exactly the reset and next scopes of mixed
Section 3 syntax, using the same durations and valuations as `Judgement.holds`.
At terminal positions next has no evaluable child. No truth premise is needed. -/
def EndpointAlong {D : Set ℝ} (P : IntervalPartition D) (d : Clock) (E : ℝ)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) (t : ℝ) :
    Section3.Judgement Clock Var → Prop
  | .reset R Ψ => endpoint d t α = E ∧ EndpointAlong P d E (R.apply α) k t Ψ
  | .next Ψ => endpoint d t α = E ∧ ∀ hk : k.1 < P.size,
      EndpointAlong P d E
        (ClockResetSet.elapse α (STLTableau.Judgement.duration P ⟨k.1,hk⟩))
        ⟨k.1+1,by omega⟩ (t + STLTableau.Judgement.duration P ⟨k.1,hk⟩) Ψ
  | .conj Φ Ψ => endpoint d t α = E ∧
      EndpointAlong P d E α k t Φ ∧ EndpointAlong P d E α k t Ψ
  | _ => endpoint d t α = E

theorem endpointAlong_of_noRightReset {D : Set ℝ} (P : IntervalPartition D)
    (d : Clock) (E : ℝ) (Ψ : Section3.Judgement Clock Var) (h : NoRightReset d Ψ)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) (t : ℝ)
    (he : endpoint d t α = E) : EndpointAlong P d E α k t Ψ := by
  induction Ψ generalizing α k t with
  | terminal => exact he
  | clock => exact he
  | marker => exact he
  | predicate => exact he
  | reset R Ψ ih =>
    exact ⟨he,ih h.2 _ _ _ ((endpoint_reset d t α R h.1).trans he)⟩
  | next Ψ ih =>
    exact ⟨he,fun hk => ih h _ _ _ ((endpoint_elapse d t α _).trans he)⟩
  | conj Φ Ψ ihΦ ihΨ => exact ⟨he,ihΦ h.1 _ _ _ he,ihΨ h.2 _ _ _ he⟩

/-- Concrete mixed-semantics endpoint invariant for a literal finite branch. -/
theorem finite_bounded_endpointAlong [DecidableEq Clock] {D : Set ℝ}
    (P : IntervalPartition D) (kind : TemporalKind) (c d : Clock) (hcd : c ≠ d)
    (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (B : STLTableau.Judgement Clock Var) (hB : B ∈ (finiteRule kind c d b q I φ).branches)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) (t : ℝ) :
    EndpointAlong P d (endpoint d t α) α k t (Section3.Judgement.ofFinite B) :=
  endpointAlong_of_noRightReset P d _ _
    (finite_bounded_no_right_reset kind c d hcd b q I φ B hB) α k t rfl

theorem unbounded_bounded_endpointAlong [DecidableEq Clock] {D : Set ℝ}
    (P : IntervalPartition D) (kind : TemporalKind) (c d : Clock) (hcd : c ≠ d)
    (b q : Marker) (a : NNReal) (φ : Formula Var)
    (B : UnboundedClocked.Node Clock Var) (hB : B ∈ unboundedBranches kind c d b q a φ)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) (t : ℝ) :
    EndpointAlong P d (endpoint d t α) α k t (Section3.Judgement.ofUnbounded B) :=
  endpointAlong_of_noRightReset P d _ _
    (unbounded_bounded_no_right_reset kind c d hcd b q a φ B hB) α k t rfl

/-- Explicit multi-step side condition on the reset fields of an actual trace.
A local bounded branch does not establish this for unrelated branches sharing d. -/
def TraceUnreset (d : Clock) : Trace Clock Var → Prop
  | .last S => S.resets.value d = none
  | .step S tail => S.resets.value d = none ∧ TraceUnreset d tail

/-- Endpoint before and after each frame reset, and at every evaluable suffix. -/
def TraceEndpointAlong {D : Set ℝ} (P : IntervalPartition D) (d : Clock) (E : ℝ)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) (t : ℝ) :
    Trace Clock Var → Prop
  | .last S => endpoint d t α = E ∧ endpoint d t (S.resets.apply α) = E
  | .step S tail => (endpoint d t α = E ∧ endpoint d t (S.resets.apply α) = E) ∧
      ∀ hk : k.1 < P.size, TraceEndpointAlong P d E
        (ClockResetSet.elapse (S.resets.apply α) (STLTableau.Judgement.duration P ⟨k.1,hk⟩))
        ⟨k.1+1,by omega⟩ (t + STLTableau.Judgement.duration P ⟨k.1,hk⟩) tail

theorem trace_endpoint_preserved {D : Set ℝ} (P : IntervalPartition D)
    (d : Clock) (E : ℝ) (trace : Trace Clock Var) (h : TraceUnreset d trace)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) (t : ℝ)
    (he : endpoint d t α = E) : TraceEndpointAlong P d E α k t trace := by
  induction trace generalizing α k t with
  | last S => exact ⟨he,(endpoint_reset d t α S.resets h).trans he⟩
  | step S tail ih =>
    have hr := (endpoint_reset d t α S.resets h.1).trans he
    exact ⟨⟨he,hr⟩,fun hk => ih h.2 _ _ _
      ((endpoint_elapse d t (S.resets.apply α) _).trans hr)⟩

end STLTableau.Section4.Finiteness.RightClockAge
