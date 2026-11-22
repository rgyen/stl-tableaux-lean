import STLTableaux.Finiteness.Derivation.Selection.SelectedPathOrigins
import STLTableaux.Finiteness.Bounds.RightClockContext
import STLTableaux.Closure.Correctness.NumericFromInvariant

/-! Bounds the number of two-clock predicates still tracking truth intervals
of a timed subformula. The invariant locates the endpoints of those intervals.
Used in the proof of Lemma 4.36. -/
namespace STLTableau.Section4.Finiteness
open Section3
open TruthPartitionIntervals
variable {Clock Var : Type*} [DecidableEq Clock]

noncomputable instance boundedLocalFintype (N : Section3.StateForm Clock Var) : Fintype (BoundedLocal N) := by
  classical
  have hi : Function.Injective (Local.predicate : Predicate Clock Var → Local Clock Var) :=
    fun p q h => Local.predicate.inj h
  have hf : {p : Predicate Clock Var | Local.predicate p∈N.locals ∧ IsBoundedPredicate p}.Finite :=
    (N.locals_finite.preimage hi.injOn).subset (fun p hp => hp.1)
  exact hf.fintype

noncomputable def boundedFamily (N : Section3.StateForm Clock Var)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) : Finset (BoundedLocal N) := by
  classical
  exact Finset.univ.filter (fun q => ∃c d m r,q.val=.bounded c d m r kind I φ)

omit [DecidableEq Clock] in
@[simp] theorem mem_boundedFamily (N : Section3.StateForm Clock Var)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) (q : BoundedLocal N) :
    q∈boundedFamily N kind I φ ↔ ∃c d m r,q.val=.bounded c d m r kind I φ := by
  classical
  simp [boundedFamily]

omit [DecidableEq Clock] in
private theorem family_formula {N : Section3.StateForm Clock Var}
    {kind : TemporalKind} {I : TimeInterval} {φ : Formula Var} {q : BoundedLocal N}
    (hq : q∈boundedFamily N kind I φ) : q.val.formula=timedFormula kind I φ := by
  obtain ⟨c,d,m,r,he⟩ := (mem_boundedFamily _ _ _ _ _).1 hq
  rw [he]
  cases kind <;> rfl

namespace InputOrigins
variable {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}
    {N : Section3.StateForm Clock Var}

noncomputable def connectedFamily (O : InputOrigins σ P α k N)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) : Finset (BoundedLocal N) := by
  classical
  exact (boundedFamily N kind I φ).filter (fun q => originConnected σ P k q.val.formula (O.last q))

noncomputable def endedFamily (O : InputOrigins σ P α k N)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) : Finset (BoundedLocal N) := by
  classical
  exact (boundedFamily N kind I φ).filter (fun q => ¬originConnected σ P k q.val.formula (O.last q))

/-- At most one two-clock predicate for a timed subformula tracks the current truth interval. -/
theorem connectedFamily_card_le_one (O : InputOrigins σ P α k N)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    (O.connectedFamily kind I φ).card≤1 := by
  classical
  apply Finset.card_le_one.mpr
  intro q hq r hr
  obtain ⟨hqFamily,hqConnect⟩ := Finset.mem_filter.mp hq
  obtain ⟨hrFamily,hrConnect⟩ := Finset.mem_filter.mp hr
  apply Subtype.ext
  exact O.eligible_unique_formula ⟨q,rfl,hqConnect⟩ ⟨r,rfl,hrConnect⟩
    ((family_formula hqFamily).trans (family_formula hrFamily).symm)

/-- The input's actual full invariant and ended-origin endpoint identify the
sliding endpoint window. The valuation includes the input reset map. -/
theorem endedFamily_endpoint_window (O : InputOrigins σ P α k N)
    (kind : TemporalKind) (I : BoundedTimeInterval) (φ : Formula Var)
    (hk : k.val<P.size) (q : BoundedLocal N) (hq : q∈O.endedFamily kind (.bounded I) φ) :
    let u := (P.interval ⟨k.val,hk⟩).left
    u-I.upper ≤ (P.interval (O.last q)).right ∧ (P.interval (O.last q)).right≤u := by
  classical
  obtain ⟨hFamily,hNotConnected⟩ := Finset.mem_filter.mp hq
  have hBefore := (O.classification q).resolve_left hNotConnected
  obtain ⟨c,d,m,r,hshape⟩ := (mem_boundedFamily _ _ _ _ _).1 hFamily
  have hp : Local.predicate (.bounded c d m r kind (.bounded I) φ)∈N.locals := hshape ▸ q.property.1
  have hWin := RightClockContext.state_bounded_endpoint_window N σ P α k hk c d m r kind I φ hp
    (N.numeric_of_invariant σ P α k O.fullInvariant)
  have hEnd := O.ended_endpoint q hk hBefore c d m r kind (.bounded I) φ hshape
  dsimp only at hWin
  rw [hEnd] at hWin
  exact hWin

/-- Assign each two-clock predicate tracking an ended interval to a distinct truth interval.
The window hypothesis of the interval count is discharged above. -/
theorem endedFamily_card_bound (O : InputOrigins σ P α k N)
    (kind : TemporalKind) (I : BoundedTimeInterval) (φ : Formula Var) (hk : k.val<P.size) :
    (O.endedFamily kind (.bounded I) φ).card ≤ ⌈I.upper/(I.upper-I.lower)⌉₊+3 := by
  classical
  let A := O.endedFamily kind (.bounded I) φ
  let θ := boundedTemporal kind I φ
  have hfam : ∀q∈A,q.val.formula=θ := by
    intro q hq
    exact (family_formula (Finset.mem_filter.mp hq).1).trans (by cases kind <;> rfl)
  let f : A → TruthBlock σ P θ := fun q =>
    ⟨O.last q.val,by rw [←hfam q.val q.property]; exact O.is_end q.val⟩
  have hinj : Function.Injective f := by
    intro q r he
    apply Subtype.ext
    exact O.injective_per_formula q.val r.val
      ((hfam q.val q.property).trans (hfam r.val r.property).symm) (congrArg Subtype.val he)
  let T := A.attach.image f
  have hcard : T.card=A.card := by
    rw [Finset.card_image_of_injective _ hinj,Finset.card_attach]
  by_cases hz : A.card=0
  · change A.card≤_
    rw [hz]
    exact Nat.zero_le _
  obtain ⟨q,hq⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hz)
  have hPart : σ.StablePartition θ P := by
    have h := O.stable.current q.val.formula ⟨q.val,q.property.1,rfl⟩
    rw [hfam q hq] at h
    exact h
  have hBound := ended_partition_truth_blocks_bound σ P kind I φ
    (fun i => (hPart i).stable) T (P.interval ⟨k.val,hk⟩).left (by
      intro b hb
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hb
      simpa only [endpoint,f] using O.endedFamily_endpoint_window kind I φ hk q.val q.property)
  rw [hcard] at hBound
  exact hBound

/-- Connected origins contribute one; ended origins obey the temporal
alternation bound. This is independent of the partition's number of pieces. -/
theorem boundedFamily_card_bound (O : InputOrigins σ P α k N)
    (kind : TemporalKind) (I : BoundedTimeInterval) (φ : Formula Var) :
    (boundedFamily N kind (.bounded I) φ).card ≤ ⌈I.upper/(I.upper-I.lower)⌉₊+4 := by
  classical
  by_cases hk : k.val<P.size
  · have hc := O.connectedFamily_card_le_one kind (.bounded I) φ
    have he := O.endedFamily_card_bound kind I φ hk
    have hs : (O.connectedFamily kind (.bounded I) φ).card +
        (O.endedFamily kind (.bounded I) φ).card = (boundedFamily N kind (.bounded I) φ).card := by
      exact Finset.card_filter_add_card_filter_not
        (fun q : BoundedLocal N => originConnected σ P k q.val.formula (O.last q))
    omega
  · have he : k.val=P.size := by omega
    have hf : boundedFamily N kind (.bounded I) φ=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q _
      exact O.no_bounded_at_terminal he q.val q.property.1
    rw [hf,Finset.card_empty]
    exact Nat.zero_le _

/-- Bounds all two-clock predicates for this timed subformula using the floor estimate. -/
theorem boundedFamily_card_floor_bound (O : InputOrigins σ P α k N)
    (kind : TemporalKind) (I : BoundedTimeInterval) (φ : Formula Var) :
    (boundedFamily N kind (.bounded I) φ).card ≤ 2*⌊I.upper/(I.upper-I.lower)⌋₊+7 := by
  have h := O.boundedFamily_card_bound kind I φ
  have hc := Nat.ceil_le_floor_add_one (I.upper/(I.upper-I.lower))
  omega

end InputOrigins

namespace TruthPartitionIntervals

omit [DecidableEq Clock] in
private theorem unbounded_always_piece_forward
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (a : NNReal) (φ : Formula Var)
    (i j : Fin P.size) (hij : i≤j)
    (hi : PieceTrue σ P (Formula.always (.unbounded a) φ) i) :
    PieceTrue σ P (Formula.always (.unbounded a) φ) j := by
  rcases lt_or_eq_of_le hij with hlt | rfl
  · obtain ⟨x,hx⟩ := piece_point σ P i
    intro z hz
    exact Finiteness.Alternation.signal_unbounded_always_forward σ a φ x z
      (point_lt_of_index_lt P hlt hx hz).le (hi x hx)
  · exact hi

omit [DecidableEq Clock] in
private theorem unbounded_eventually_piece_backward
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (a : NNReal) (φ : Formula Var)
    (i j : Fin P.size) (hij : i≤j)
    (hj : PieceTrue σ P (Formula.eventually (.unbounded a) φ) j) :
    PieceTrue σ P (Formula.eventually (.unbounded a) φ) i := by
  rcases lt_or_eq_of_le hij with hlt | rfl
  · obtain ⟨y,hy⟩ := piece_point σ P j
    intro z hz
    exact Finiteness.Alternation.signal_unbounded_eventually_backward σ a φ z y
      (point_lt_of_index_lt P hlt hz hy).le (hj y hy)
  · exact hj

omit [DecidableEq Clock] in
/-- Actual unbounded unary temporal truth has at most one consecutive block.
The proof uses semantic monotonicity, not a finite-window alternation bound. -/
theorem unbounded_truthBlock_unique
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (kind : TemporalKind)
    (a : NNReal) (φ : Formula Var)
    (b c : TruthBlock σ P (timedFormula kind (.unbounded a) φ)) : b=c := by
  apply end_unique b c
  intro j hl hr
  rcases le_total b.val c.val with hbc | hcb
  · have hbc' : b.val.val≤c.val.val := hbc
    have hL : b.val≤j := by change b.val.val≤j.val; simpa only [min_eq_left hbc'] using hl
    have hR : j≤c.val := by change j.val≤c.val.val; simpa only [max_eq_right hbc'] using hr
    cases kind with
    | always => exact unbounded_always_piece_forward σ P a φ b.val j hL b.property.1
    | eventually => exact unbounded_eventually_piece_backward σ P a φ j c.val hR c.property.1
  · have hcb' : c.val.val≤b.val.val := hcb
    have hL : c.val≤j := by change c.val.val≤j.val; simpa only [min_eq_right hcb'] using hl
    have hR : j≤b.val := by change j.val≤b.val.val; simpa only [max_eq_left hcb'] using hr
    cases kind with
    | always => exact unbounded_always_piece_forward σ P a φ c.val j hL c.property.1
    | eventually => exact unbounded_eventually_piece_backward σ P a φ j b.val hR b.property.1

end TruthPartitionIntervals

namespace InputOrigins
variable {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}
    {N : Section3.StateForm Clock Var}

/-- Connected and ended locals together share the single unbounded truth block. -/
theorem unboundedFamily_card_le_one (O : InputOrigins σ P α k N)
    (kind : TemporalKind) (a : NNReal) (φ : Formula Var) :
    (boundedFamily N kind (.unbounded a) φ).card≤1 := by
  classical
  apply Finset.card_le_one.mpr
  intro q hq r hr
  have hqf := family_formula hq
  have hrf := family_formula hr
  let b : TruthBlock σ P (timedFormula kind (.unbounded a) φ) :=
    ⟨O.last q,by rw [←hqf]; exact O.is_end q⟩
  let c : TruthBlock σ P (timedFormula kind (.unbounded a) φ) :=
    ⟨O.last r,by rw [←hrf]; exact O.is_end r⟩
  have he := unbounded_truthBlock_unique σ P kind a φ b c
  exact O.injective_per_formula q r (hqf.trans hrf.symm) (congrArg Subtype.val he)

/-- An upper credit true now excludes every ended source of this unbounded
formula. This is the exclusivity needed to count full retained labels. -/
theorem unbounded_endedFamily_empty_of_truth (O : InputOrigins σ P α k N)
    (kind : TemporalKind) (a : NNReal) (φ : Formula Var) (hk : k.val<P.size)
    (ht : PieceTrue σ P (timedFormula kind (.unbounded a) φ) ⟨k.val,hk⟩) :
    O.endedFamily kind (.unbounded a) φ=∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  obtain ⟨hFamily,hNotConnected⟩ := Finset.mem_filter.mp hq
  have hBefore := (O.classification q).resolve_left hNotConnected
  have hqf := family_formula hFamily
  let b : TruthBlock σ P (timedFormula kind (.unbounded a) φ) :=
    ⟨O.last q,by rw [←hqf]; exact O.is_end q⟩
  let c := truthBlockOf σ P (timedFormula kind (.unbounded a) φ) ⟨k.val,hk⟩ ht
  have he := unbounded_truthBlock_unique σ P kind a φ b c
  have heLast : O.last q=c.val := congrArg Subtype.val he
  have hGe : k.val≤c.val.val := connected_le_end c ⟨k.val,hk⟩ (blockOf_connected _ _ ht)
  have hv := congrArg Fin.val heLast
  omega

end InputOrigins
end STLTableau.Section4.Finiteness
