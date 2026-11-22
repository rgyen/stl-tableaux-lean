import STLTableaux.Finiteness.Derivation.Selection.SelectedPathOrigins
import STLTableaux.Finiteness.Derivation.DerivationRelation

/-! Actual successor origin assignment from the SAME selected derivation.
Every local cause is constructed from its actual normalized next predicate. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
open TruthPartitionIntervals
namespace InputOrigins
variable {Clock Var : Type*} [DecidableEq Clock]
variable {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}
    {N : Section3.StateForm Clock Var}
    {J : MixedJ Clock Var} {W : Set Clock} {owned : OwnedPending J N.resets W}
    {O : InputOrigins σ P α k N} {H Er : MixedJ Clock Var}
    {T : SelectedTree O.eligible O.strictClocks owned H Er}
    {M : Section3.StateForm Clock Var}

omit [DecidableEq Clock] in
private theorem successor_params (q : BoundedLocal M) :
    ∃ c d m r kind I φ, q.val = .bounded c d m r kind I φ := by
  rcases q with ⟨p,hp,hb⟩
  cases p with
  | bounded c d m r kind I φ => exact ⟨c,d,m,r,kind,I,φ,rfl⟩
  | plain | upper => cases hb

private theorem upper_family {q : BoundedLocal M}
    (w : NextBoundedWitness owned O T q)
    (hu : ∃ c b kind I φ, w.entry.source = .upper c b kind I φ)
    (c d : Clock) (m r : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hq : q.val = .bounded c d m r kind I φ) :
    ∃ b, w.entry.source = .upper c b kind I φ := by
  have hraw : Predicate.bounded c d m r kind I φ ∈ w.payload.currentPredicates := by rw [← hq]; exact w.current
  rcases w.entry.actual.next_bounded_source w.occurrence c d m r kind I φ hraw with
    ⟨b,hs,hcd⟩ | ⟨b,hs,hcd⟩
  · exact ⟨b,hs⟩
  · obtain ⟨c',b',kind',I',φ',hs'⟩ := hu
    have he := hs.symm.trans hs'
    cases he

private theorem bounded_family {q : BoundedLocal M}
    (w : NextBoundedWitness owned O T q) (hb : IsBoundedPredicate w.entry.source)
    (c d : Clock) (m r : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hq : q.val = .bounded c d m r kind I φ) :
    ∃ b, w.entry.source = .bounded c d b r kind I φ := by
  have hraw : Predicate.bounded c d m r kind I φ ∈ w.payload.currentPredicates := by rw [← hq]; exact w.current
  rcases w.entry.actual.next_bounded_source w.occurrence c d m r kind I φ hraw with
    ⟨b,hs,hcd⟩ | ⟨b,hs,hcd⟩
  · rw [hs] at hb
    cases hb
  · exact ⟨b,hs⟩

private theorem cause_classification {hk : k.val < P.size} {q : BoundedLocal M}
    (cause : NextOriginCause owned O T hk q) (hnext : k.val+1 < P.size) :
    originConnected σ P ⟨k.val+1,by omega⟩ q.val.formula cause.last ∨ cause.last.val < k.val+1 := by
  cases cause with
  | ended w source hs hf hb => exact Or.inr (by change (O.last source).val < k.val+1; omega)
  | born w hu hf ht =>
    let b := truthBlockOf σ P q.val.formula ⟨k.val,hk⟩ ht
    have hc : Connected (PieceTrue σ P q.val.formula) ⟨k.val,hk⟩ b.val := blockOf_connected _ _ ht
    have hlast : k.val ≤ b.val.val := connected_le_end b _ hc
    change originConnected σ P ⟨k.val+1,by omega⟩ q.val.formula b.val ∨ b.val.val < k.val+1
    by_cases he : k.val+1 ≤ b.val.val
    · left
      refine ⟨hnext,?_⟩
      intro j hl hr
      apply hc j
      · simp only [Nat.min_eq_left hlast]
        have hmin : min (k.val+1) b.val.val = k.val+1 := Nat.min_eq_left he
        change min (k.val+1) b.val.val ≤ j.val at hl
        omega
      · simp only [Nat.max_eq_right hlast]
        have hmax : max (k.val+1) b.val.val = b.val.val := Nat.max_eq_right he
        change j.val ≤ max (k.val+1) b.val.val at hr
        omega
    · exact Or.inr (by omega)

private theorem cause_current_entry {hk : k.val < P.size} {q : BoundedLocal M}
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization H F)
    (hn : F.nextPart = some M) (cause : NextOriginCause owned O T hk q)
    (hM : M.holds σ P
      (ClockResetSet.elapse (F.current.resets.apply α) (STLTableau.Judgement.duration P ⟨k.val,hk⟩))
      ⟨k.val+1,by omega⟩)
    (hconn : originConnected σ P ⟨k.val+1,by omega⟩ q.val.formula cause.last) :
    Nonempty (CurrentOriginEntry σ P
      (ClockResetSet.elapse (F.current.resets.apply α) (STLTableau.Judgement.duration P ⟨k.val,hk⟩))
      ⟨k.val+1,by omega⟩ M q.val) := by
  obtain ⟨hnext,hconn⟩ := hconn
  cases cause with
  | ended w source hs hf hb =>
    have hEnd : IsEnd (PieceTrue σ P q.val.formula) (O.last source) := by rw [← hf]; exact O.is_end source
    have hle := connected_le_end ⟨O.last source,hEnd⟩ ⟨k.val+1,hnext⟩ hconn
    exact False.elim (by change k.val+1 ≤ (O.last source).val at hle; omega)
  | born w hu hf ht =>
    obtain ⟨c,d,m,r,kind,I,φ,hq⟩ := successor_params q
    obtain ⟨b,hs⟩ := upper_family w hu c d m r kind I φ hq
    have hraw : Predicate.bounded c d m r kind I φ ∈ w.payload.currentPredicates := by rw [← hq]; exact w.current
    obtain ⟨ell,hr,hm,hmLocal,hd,hvalue,hc,hcomp,hfrozen⟩ :=
      T.ledger_upper_successor_conditions hSafe hn w.in_ledger w.occurrence c d m r kind I φ
        ⟨b,hs⟩ hraw σ P (F.current.resets.apply α) ⟨k.val,hk⟩ hnext hM
    exact ⟨⟨c,d,m,ell,kind,I,φ,hq.trans (congrArg (fun a => Predicate.bounded c d m a kind I φ) hr),
      hfrozen,hmLocal,hd,hc,hcomp⟩⟩

private theorem cause_ended_endpoint {hk : k.val < P.size} {q : BoundedLocal M}
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization H F)
    (hn : F.nextPart = some M) (cause : NextOriginCause owned O T hk q)
    (hnext : k.val+1 < P.size) (hEnded : cause.last.val < k.val+1)
    (c d : Clock) (m r : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hq : q.val = .bounded c d m r kind I φ) :
    RightClockAge.endpoint d (P.interval ⟨k.val+1,hnext⟩).left
      (M.resets.apply (ClockResetSet.elapse (F.current.resets.apply α)
        (STLTableau.Judgement.duration P ⟨k.val,hk⟩))) = (P.interval cause.last).right := by
  have hraw : ∀ w : NextBoundedWitness owned O T q,
      Predicate.bounded c d m r kind I φ ∈ w.payload.currentPredicates := by intro w; rw [← hq]; exact w.current
  cases cause with
  | ended w source hs hf hb =>
    have hbounded : IsBoundedPredicate w.entry.source := hs ▸ source.property.2
    obtain ⟨b,hsource⟩ := bounded_family w hbounded c d m r kind I φ hq
    have hsourceShape : source.val = .bounded c d b r kind I φ := hs.symm.trans hsource
    have htransfer := T.ledger_bounded_endpoint hSafe hn w.in_ledger w.occurrence
      c d b r m r kind I φ hsource (hraw w) σ P α ⟨k.val,hk⟩ hnext
    exact htransfer.trans (O.ended_endpoint source hk hb c d b r kind I φ hsourceShape)
  | born w hu hf ht =>
    let b := truthBlockOf σ P q.val.formula ⟨k.val,hk⟩ ht
    have hle : k.val ≤ b.val.val := connected_le_end b _ (blockOf_connected _ _ ht)
    have hlt : b.val.val < k.val+1 := hEnded
    have hlast : b.val = ⟨k.val,hk⟩ := Fin.ext (Nat.le_antisymm (Nat.lt_succ_iff.mp hlt) hle)
    obtain ⟨sourceMarker,hsource⟩ := upper_family w hu c d m r kind I φ hq
    obtain ⟨ell,hr,hm,hd,hc,hfrozen⟩ := T.ledger_upper_entry hSafe hn w.in_ledger w.occurrence
      c d m r kind I φ ⟨sourceMarker,hsource⟩ (hraw w)
    change _ = (P.interval b.val).right
    rw [hlast]
    change (P.interval ⟨k.val+1,hnext⟩).left -
      (M.resets.apply (ClockResetSet.elapse (F.current.resets.apply α)
        (STLTableau.Judgement.duration P ⟨k.val,hk⟩)) d : ℝ) = _
    simp only [ClockResetSet.apply,hd,NNReal.coe_zero,sub_zero]
    exact (P.adjacent_right_eq_left ⟨k.val,hk⟩ hnext).symm

/-- Assemble the actual successor assignment from constructed causes. Both
ended and born causes preserve injection; all entry/endpoint fields are proved
against the complete normalized successor and its actual post-reset valuation. -/
noncomputable def successor_origins
    (O : InputOrigins σ P α k N) (owned : OwnedPending J N.resets W)
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (hLocal : ∀ l, l ∈ owned.locals ↔ l ∈ N.locals) (hnil : owned.nextInputs = [])
    {F : Section3.TransitionForm Clock Var}
    (facts : SelectedOutputFacts owned ∅ O.strictClocks σ P α k H Er F)
    (hk : k.val < P.size) (hn : F.nextPart = some M) :
    InputOrigins σ P
      (ClockResetSet.elapse (F.current.resets.apply α) (STLTableau.Judgement.duration P ⟨k.val,hk⟩))
      ⟨k.val+1,by omega⟩ M := by
  classical
  rcases facts with ⟨hSafe,hEr,hHolds,hInv,hStable,hReady,hNPH,hNPE,hPrivate,hGuard,hReset,hMap⟩
  have hM : M.holds σ P
      (ClockResetSet.elapse (F.current.resets.apply α) (STLTableau.Judgement.duration P ⟨k.val,hk⟩))
      ⟨k.val+1,by omega⟩ := by
    simpa only [hn,dif_pos hk] using hHolds.2
  let causes : ∀ q : BoundedLocal M, NextOriginCause owned O T hk q := fun q =>
    Classical.choice (next_cause_exists owned O T hLocal hnil hSafe hHolds hk hn q)
  refine {
    ready := ⟨hReady.2 M hn,by intro L hL; cases hL⟩
    holds := hM
    fullInvariant := hInv.2 M hn hk
    stable := ?_
    private_current := hPrivate M hn
    no_upper := ?_
    last := fun q => (causes q).last
    is_end := fun q => (causes q).is_end
    injective_per_formula := ?_
    classification := ?_
    current_entry := ?_
    ended_endpoint := ?_ }
  · simpa only [Section3.StateForm.UnderlyingStable,Section3.TransitionForm.UnderlyingStable,Section3.TransitionForm.underlyingFormulas,
      Section3.TransitionForm.ofState,Set.union_empty] using hStable.next M hn
  · intro c m kind I φ hp
    rcases (T.normalized_next_provenance hSafe hn (.upper c m kind I φ)).1 hp with
      ⟨K,hK,_⟩ | ⟨entry,he,K,hK,hpK⟩
    · rw [hnil] at hK
      cases hK
    · exact entry.actual.literal_next_no_upper hK c m kind I φ hpK
  · intro q r hf hl
    exact next_cause_injective O T hLocal (causes q) (causes r) hf hl
  · intro q
    by_cases hnext : k.val+1 < P.size
    · exact cause_classification (causes q) hnext
    · right
      have hlast := (causes q).last.isLt
      change (causes q).last.val < k.val+1
      omega
  · intro q hconn
    exact cause_current_entry hSafe hn (causes q) hM hconn
  · intro q hnext hEnded c d m r kind I φ hq
    exact cause_ended_endpoint hSafe hn (causes q) hnext hEnded c d m r kind I φ hq

/-- The actual nonempty-state step, including ALL successor origin invariants.
Canonical representation, exact eligibility, selected tree and source causes are
all constructed; no future-origin or representative assumption is supplied. -/
theorem nonempty_selected_origin_step [Infinite Clock] (O : InputOrigins σ P α k N)
    (hne : N.locals.Nonempty) :
    ∃ (J : MixedJ Clock Var) (W : Set Clock) (owned : OwnedPending J N.resets W)
      (H Er : MixedJ Clock Var) (F : Section3.TransitionForm Clock Var)
      (_T : SelectedTree O.eligible O.strictClocks owned H Er),
      owned.nextInputs = [] ∧ SafeNormalization J (.ofState N) ∧ NextPrivate J ∧
      SelectedOutputFacts owned ∅ O.strictClocks σ P α k H Er F ∧
      F.current.guards ⊆ N.guards ∪ strictBoundaryGuards O.strictClocks ∧
      ∀ (hk : k.val < P.size) (M : Section3.StateForm Clock Var), F.nextPart = some M →
        Nonempty (InputOrigins σ P
          (ClockResetSet.elapse (F.current.resets.apply α) (STLTableau.Judgement.duration P ⟨k.val,hk⟩))
          ⟨k.val+1,by omega⟩ M) := by
  obtain ⟨J,W,owned,hnil,hInput,hNext⟩ := exists_owned_state_input N hne O.private_current
  obtain ⟨H,Er,F,T,hFacts,hGuards⟩ := O.selected_output owned hInput hNext
    (owned.local_mem_of_safe hInput)
  refine ⟨J,W,owned,H,Er,F,T,hnil,hInput,hNext,hFacts,hGuards,?_⟩
  intro hk M hn
  exact ⟨successor_origins O owned T (owned.local_mem_of_safe hInput) hnil hFacts hk hn⟩

theorem nonempty_origin_step [Infinite Clock] (O : InputOrigins σ P α k N)
    (hne : N.locals.Nonempty) :
    ∃ (J : MixedJ Clock Var) (W : Set Clock) (owned : OwnedPending J N.resets W)
      (H Er : MixedJ Clock Var) (F : Section3.TransitionForm Clock Var)
      (_T : SelectedTree O.eligible O.strictClocks owned H Er),
      owned.nextInputs = [] ∧ SafeNormalization J (.ofState N) ∧ NextPrivate J ∧
      Derives N F ∧ SelectedOutputFacts owned ∅ O.strictClocks σ P α k H Er F ∧
      F.current.guards ⊆ N.guards ∪ strictBoundaryGuards O.strictClocks ∧
      ∀ (hk : k.val < P.size) (M : Section3.StateForm Clock Var), F.nextPart = some M →
        Nonempty (InputOrigins σ P
          (ClockResetSet.elapse (F.current.resets.apply α) (STLTableau.Judgement.duration P ⟨k.val,hk⟩))
          ⟨k.val+1,by omega⟩ M) := by
  obtain ⟨J,W,owned,H,Er,F,T,hnil,hInput,hNext,hFacts,hGuards,hSuccessor⟩ :=
    O.nonempty_selected_origin_step hne
  exact ⟨J,W,owned,H,Er,F,T,hnil,hInput,hNext,.resolved T.realize hInput hFacts.1 hFacts.2.1,
    hFacts,hGuards,hSuccessor⟩
end InputOrigins
end STLTableau.Section4.Finiteness
