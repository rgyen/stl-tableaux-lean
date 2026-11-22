import STLTableaux.Finiteness.Derivation.Selection.CombinedSelection
import STLTableaux.Finiteness.Bounds.TruthPartitionIntervals
import STLTableaux.Finiteness.Derivation.Selection.NextEntryConditions
import STLTableaux.Finiteness.Derivation.Selection.SelectedUpperTruth
import STLTableaux.Finiteness.Derivation.StateInputOwnership
import STLTableaux.Finiteness.Derivation.StateInputLocals
import STLTableaux.Finiteness.Derivation.Selection.SelectedBoundedLedger
import STLTableaux.Finiteness.Derivation.Selection.SelectedLedgerEligibility
import STLTableaux.Finiteness.Derivation.Selection.SelectedUpperConsumption

/-! Proof-only origin data for actual input states on a fixed signal/partition.
No origin condition is added to tableau state or edge admission. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
open TruthPartitionIntervals
variable {Clock Var : Type*} [DecidableEq Clock]

/-- The origin domain consists of the local predicates in the `↑↓` form. -/
abbrev BoundedLocal (N : Section3.StateForm Clock Var) :=
  {q : Predicate Clock Var // Local.predicate q ∈ N.locals ∧ IsBoundedPredicate q}

def originConnected (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (k : STLTableau.Judgement.Position P) (θ : Formula Var) (last : Fin P.size) : Prop :=
  ∃ hk : k.val < P.size, Connected (PieceTrue σ P θ) ⟨k.val,hk⟩ last

/-- Eligibility data inherited from an actual preceding upper successor.
The current block itself supplies satisfaction of the unclocked temporal predicate, so it
is not a field. -/
structure CurrentOriginEntry (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (N : Section3.StateForm Clock Var) (p : Predicate Clock Var) where
  c : Clock
  d : Clock
  m : Marker
  ell : Marker
  kind : TemporalKind
  I : TimeInterval
  phi : Formula Var
  shape : p = .bounded c d m (¬ₘ ell) kind I phi
  frozen : Nonempty (FrozenByUpper c d m ell kind I phi)
  marker : Local.marker ell ∈ N.locals
  right_zero : N.resets.value d = some 0
  strict_unreset : Marker.imp ell m = Marker.open → N.resets.value c = none
  comparison : (0 : ℝ) <[Marker.imp ell m] (N.resets.apply α c : ℝ)

/-- Actual input semantics plus a per-formula injective assignment to canonical
truth blocks. Connected and ended origins are distinguished by partition index,
including at zero-duration pieces and at the terminal Position. -/
structure InputOrigins (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (N : Section3.StateForm Clock Var) where
  ready : (Section3.TransitionForm.ofState N).Ready
  holds : N.holds σ P α k
  fullInvariant : N.EvaluatedInvariant σ P α k
  stable : (Section3.TransitionForm.ofState N).UnderlyingStable σ P
  private_current : ∀ p q, Local.predicate p ∈ N.locals → Local.predicate q ∈ N.locals → p ≠ q →
    Disjoint (syntaxClocks (.predicate p)) (syntaxClocks (.predicate q))
  no_upper : ∀ c m kind I φ, Local.predicate (.upper c m kind I φ) ∉ N.locals
  last : BoundedLocal N → Fin P.size
  is_end : ∀ q, IsEnd (PieceTrue σ P q.val.formula) (last q)
  injective_per_formula : ∀ q r, q.val.formula = r.val.formula → last q = last r → q = r
  classification : ∀ q, originConnected σ P k q.val.formula (last q) ∨ (last q).val < k.val
  current_entry : ∀ q, originConnected σ P k q.val.formula (last q) →
    Nonempty (CurrentOriginEntry σ P α k N q.val)
  ended_endpoint : ∀ q (hk : k.val < P.size), (last q).val < k.val →
    ∀ c d m r kind I φ, q.val = .bounded c d m r kind I φ →
      RightClockAge.endpoint d (P.interval ⟨k.val,hk⟩).left (N.resets.apply α) =
        (P.interval (last q)).right

namespace InputOrigins
variable {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}
    {N : Section3.StateForm Clock Var}

/-- The assigned value is an actual maximal consecutive truth block. -/
def block (O : InputOrigins σ P α k N) (q : BoundedLocal N) : TruthBlock σ P q.val.formula :=
  ⟨O.last q,O.is_end q⟩

/-- The eligible set contains the local predicates in the `↑↓` form
whose truth intervals connect to the current interval. -/
def eligible (O : InputOrigins σ P α k N) : Set (Predicate Clock Var) :=
  {p | ∃ q : BoundedLocal N, q.val = p ∧ originConnected σ P k q.val.formula (O.last q)}

/-- Strict comparison clocks of the exact connected origin family. -/
def strictClocks (O : InputOrigins σ P α k N) : Set Clock :=
  {c | ∃ q : BoundedLocal N, originConnected σ P k q.val.formula (O.last q) ∧
    ∃ d m r kind I φ, q.val = .bounded c d m r kind I φ ∧
      Marker.imp (Marker.complement r) m = Marker.open}

/-- At the terminal Position actual state truth excludes every local predicate in the `↑↓` form;
the origin domain is therefore empty, without coercing Position to Fin size. -/
theorem no_bounded_at_terminal (O : InputOrigins σ P α k N) (hk : k.val = P.size)
    (p : Predicate Clock Var) : Local.predicate p ∉ N.locals := by
  intro hp
  have hs := O.holds.2 (.predicate p) hp
  simp only [Local.holds,Local.toJudgement,Section3.Judgement.holds,
    dif_neg (by omega : ¬k.val < P.size)] at hs

/-- Exact eligibility has the required `↑↓` source property. -/
theorem eligible_bounded (O : InputOrigins σ P α k N) {p : Predicate Clock Var}
    (hp : p ∈ O.eligible) : IsBoundedPredicate p := by
  obtain ⟨q,rfl,hq⟩ := hp
  exact q.property.2

/-- Two connected origins of one temporal formula belong to the same actual
truth block, so the original origin injection makes their locals equal. -/
theorem eligible_unique_formula (O : InputOrigins σ P α k N)
    {p q : Predicate Clock Var} (hp : p ∈ O.eligible) (hq : q ∈ O.eligible)
    (hf : p.formula = q.formula) : p = q := by
  obtain ⟨p',rfl,hp'⟩ := hp
  obtain ⟨q',rfl,hq'⟩ := hq
  obtain ⟨hk,hcp⟩ := hp'
  obtain ⟨hk',hcq⟩ := hq'
  have hendq : IsEnd (PieceTrue σ P p'.val.formula) (O.last q') := by
    rw [hf]
    exact O.is_end q'
  have hconn : Connected (PieceTrue σ P p'.val.formula) (O.last p') (O.last q') := by
    rw [← hf] at hcq
    exact connected_trans (connected_symm hcp) hcq
  have he := end_unique (O.block p') ⟨O.last q',hendq⟩ hconn
  have helast : O.last p' = O.last q' := congrArg Subtype.val he
  exact congrArg Subtype.val (O.injective_per_formula p' q' hf helast)

/-- The connected block supplies satisfaction of the unclocked predicate on the
current piece, independently of reset valuations. -/
theorem connected_plain_truth (O : InputOrigins σ P α k N) (q : BoundedLocal N)
    (hq : originConnected σ P k q.val.formula (O.last q)) :
    Judgement.holds σ P α k (.predicate (.plain q.val.formula)) := by
  obtain ⟨hk,hconn⟩ := hq
  have ht := connected_left hconn
  simpa only [Judgement.holds,dif_pos hk,Predicate.holds,STLTableau.predicateSatisfies,PieceTrue] using ht

/-- The fixed strict-clock set is actually absent from the input reset map. -/
theorem strictClocks_unreset (O : InputOrigins σ P α k N) {c : Clock}
    (hc : c ∈ O.strictClocks) : N.resets.value c = none := by
  obtain ⟨q,hq,d,m,r,kind,I,φ,hshape,hstrict⟩ := hc
  obtain ⟨entry⟩ := O.current_entry q hq
  have he := hshape.symm.trans entry.shape
  cases he
  apply entry.strict_unreset
  simpa only [Marker.complement_complement] using hstrict

/-- Disjointness required by selected completion follows from actual entry
reset values, rather than being assumed for an unrelated protection set. -/
theorem strictClocks_disjoint (O : InputOrigins σ P α k N) :
    Disjoint N.resets.clocks O.strictClocks := by
  apply Set.disjoint_left.2
  rintro c ⟨v,hv⟩ hc
  rw [O.strictClocks_unreset hc] at hv
  cases hv

/-- Exact connected origins derive the existing local selector's eligibility.
The local equivalence is merely the explicit raw/state representation interface;
the final state constructor discharges it. -/
theorem eligibility (O : InputOrigins σ P α k N)
    {J : MixedJ Clock Var} {W : Set Clock} (owned : OwnedPending J N.resets W)
    (hLocal : ∀ l, l ∈ owned.locals ↔ l ∈ N.locals) :
    Eligibility O.eligible owned O.strictClocks σ P α k := by
  refine ⟨fun _ hp => O.eligible_bounded hp,?_,?_⟩
  · intro p hp q hq hf
    exact O.eligible_unique_formula hp hq hf
  · intro p hp _
    obtain ⟨q,hqp,hq⟩ := hp
    obtain ⟨entry⟩ := O.current_entry q hq
    refine ⟨entry.c,entry.d,entry.m,entry.ell,entry.kind,entry.I,entry.phi,
      hqp.symm.trans entry.shape,entry.frozen,(hLocal _).2 entry.marker,
      entry.right_zero,?_,entry.comparison,?_⟩
    · have ht := O.connected_plain_truth q hq
      have hf : q.val.formula = timedFormula entry.kind entry.I entry.phi := by
        calc
          q.val.formula = (Predicate.bounded entry.c entry.d entry.m (Marker.complement entry.ell)
              entry.kind entry.I entry.phi).formula := congrArg Predicate.formula entry.shape
          _ = timedFormula entry.kind entry.I entry.phi := by cases entry.kind <;> rfl
      rw [hf] at ht
      exact ht
    · intro hs
      refine ⟨q,hq,entry.d,entry.m,Marker.complement entry.ell,entry.kind,entry.I,entry.phi,
        entry.shape,?_⟩
      simpa only [Marker.complement_complement] using hs

/-- Every strict comparison clock is in the actual canonical input budget. -/
theorem strictClocks_subset_budget (O : InputOrigins σ P α k N)
    {J : MixedJ Clock Var} {W : Set Clock} (owned : OwnedPending J N.resets W)
    (hLocal : ∀ l, l ∈ owned.locals ↔ l ∈ N.locals) : O.strictClocks ⊆ W := by
  rintro c ⟨q,hq,d,m,r,kind,I,φ,hshape,hstrict⟩
  have hm : Local.predicate q.val ∈ owned.locals := (hLocal _).2 q.property.1
  have hc : c ∈ syntaxClocks (.predicate q.val) := by rw [hshape]; simp [syntaxClocks]
  exact owned.covers_input (Or.inl (Or.inr (canonical_local_support owned.shape hm hc)))

/-- Actual origins determine eligibility and the same selected output tree. -/
theorem selected_output [Infinite Clock] (O : InputOrigins σ P α k N)
    {J : MixedJ Clock Var} {W : Set Clock} (owned : OwnedPending J N.resets W)
    (hInput : SafeNormalization J (.ofState N)) (hNext : NextPrivate J)
    (hLocal : ∀ l, l ∈ owned.locals ↔ l ∈ N.locals) :
    ∃ (H Er : MixedJ Clock Var) (F : Section3.TransitionForm Clock Var)
      (_T : SelectedTree O.eligible O.strictClocks owned H Er),
      SelectedOutputFacts owned ∅ O.strictClocks σ P α k H Er F ∧
      F.current.guards ⊆ N.guards ∪ strictBoundaryGuards O.strictClocks := by
  exact selected_output_exists O.eligible hInput owned ∅ O.strictClocks
    (Set.empty_subset _) (Set.disjoint_empty _) (Set.disjoint_empty _)
    (O.strictClocks_subset_budget owned hLocal) O.strictClocks_disjoint hNext
    σ P α k O.ready ⟨O.holds,trivial⟩
    ⟨O.fullInvariant,by intro M hm; cases hm⟩ O.stable (O.eligibility owned hLocal)

omit [DecidableEq Clock] in
private theorem bounded_params {M : Section3.StateForm Clock Var} (q : BoundedLocal M) :
    ∃ c d m r kind I φ, q.val = .bounded c d m r kind I φ := by
  rcases q with ⟨p,hp,hb⟩
  cases p with
  | bounded c d m r kind I φ => exact ⟨c,d,m,r,kind,I,φ,rfl⟩
  | plain | upper => cases hb

omit [DecidableEq Clock] in
private theorem bounded_formula (c d : Clock) (m r : Marker) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var) :
    (Predicate.bounded c d m r kind I φ).formula = timedFormula kind I φ := by cases kind <;> rfl

omit [DecidableEq Clock] in
private theorem upper_formula (c : Clock) (m : Marker) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var) :
    (Predicate.upper c m kind I φ).formula = timedFormula kind I φ := by cases kind <;> rfl

/-- Constructed literal source evidence for one actual successor local predicate in the
`↑↓` form. -/
structure NextBoundedWitness
    {J : MixedJ Clock Var} {W : Set Clock} (owned : OwnedPending J N.resets W)
    {H Er : MixedJ Clock Var} (O : InputOrigins σ P α k N)
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    {M : Section3.StateForm Clock Var} (q : BoundedLocal M) where
  entry : RawLedgerEntry (Clock := Clock) (Var := Var)
  in_ledger : entry ∈ T.rawLedger
  payload : MixedJ Clock Var
  occurrence : Conjunct entry.body (.next payload)
  current : q.val ∈ payload.currentPredicates

private theorem next_witness_exists
    {J : MixedJ Clock Var} {W : Set Clock} (owned : OwnedPending J N.resets W)
    (O : InputOrigins σ P α k N) {H Er : MixedJ Clock Var}
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (hnil : owned.nextInputs = [])
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization H F)
    {M : Section3.StateForm Clock Var} (hn : F.nextPart = some M) (q : BoundedLocal M) :
    Nonempty (NextBoundedWitness owned O T q) := by
  rcases (T.normalized_next_provenance hSafe hn q.val).1 q.property.1 with
    ⟨K,hK,_⟩ | ⟨entry,he,K,hK,hq⟩
  · rw [hnil] at hK
    cases hK
  · exact ⟨⟨entry,he,K,hK,hq⟩⟩

/-- The two actual causal alternatives. Ended sources are original bounded
locals; born sources use truth of a genuine upper credit on this piece. -/
inductive NextOriginCause
    {J : MixedJ Clock Var} {W : Set Clock} (owned : OwnedPending J N.resets W)
    (O : InputOrigins σ P α k N) {H Er : MixedJ Clock Var}
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (hk : k.val < P.size) {M : Section3.StateForm Clock Var} (q : BoundedLocal M) : Type _
  | ended (w : NextBoundedWitness owned O T q) (source : BoundedLocal N)
      (source_eq : w.entry.source = source.val)
      (formula_eq : source.val.formula = q.val.formula)
      (before : (O.last source).val < k.val) : NextOriginCause owned O T hk q
  | born (w : NextBoundedWitness owned O T q)
      (upper : ∃ c b kind I φ, w.entry.source = .upper c b kind I φ)
      (formula_eq : w.entry.source.formula = q.val.formula)
      (truth : PieceTrue σ P q.val.formula ⟨k.val,hk⟩) : NextOriginCause owned O T hk q

/-- Actual selected-output provenance constructs the causal alternative for
EVERY successor local predicate in the `↑↓` form; none is supplied as a premise. -/
theorem next_cause_exists
    {J : MixedJ Clock Var} {W : Set Clock} (owned : OwnedPending J N.resets W)
    (O : InputOrigins σ P α k N) {H Er : MixedJ Clock Var}
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (hLocal : ∀ l, l ∈ owned.locals ↔ l ∈ N.locals) (hnil : owned.nextInputs = [])
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization H F)
    (hHolds : F.holds σ P α k) (hk : k.val < P.size)
    {M : Section3.StateForm Clock Var} (hn : F.nextPart = some M) (q : BoundedLocal M) :
    Nonempty (NextOriginCause owned O T hk q) := by
  classical
  obtain ⟨w⟩ := next_witness_exists owned O T hnil hSafe hn q
  obtain ⟨c,d,m,r,kind,I,φ,hq⟩ := bounded_params q
  have hqraw : Predicate.bounded c d m r kind I φ ∈ w.payload.currentPredicates := by
    rw [← hq]
    exact w.current
  have hqformula : q.val.formula = timedFormula kind I φ :=
    (congrArg Predicate.formula hq).trans (bounded_formula _ _ _ _ _ _ _)
  rcases w.entry.actual.next_bounded_source w.occurrence c d m r kind I φ hqraw with
    ⟨b,hs,hcd⟩ | ⟨b,hs,hcd⟩
  · have ht := T.upper_ledger_plain_truth σ P α k (O.eligibility owned hLocal)
      ((hSafe.holds σ P α k).1 hHolds)
      (fun c m kind I φ hm => O.no_upper c m kind I φ ((hLocal _).1 hm))
      w.in_ledger c b kind I φ hs
    have htrue : PieceTrue σ P q.val.formula ⟨k.val,hk⟩ := by
      rw [hqformula]
      simpa only [PieceTrue,Judgement.holds,dif_pos hk,Predicate.holds,STLTableau.predicateSatisfies] using ht
    have hf : w.entry.source.formula = q.val.formula :=
      (congrArg Predicate.formula hs).trans ((upper_formula _ _ _ _ _).trans hqformula.symm)
    exact ⟨.born w ⟨c,b,kind,I,φ,hs⟩ hf htrue⟩
  · have hb : IsBoundedPredicate w.entry.source := by rw [hs]; trivial
    have hm : Local.predicate w.entry.source ∈ N.locals :=
      (hLocal _).1 (T.bounded_ledger_origin w.in_ledger hb)
    let source : BoundedLocal N := ⟨w.entry.source,hm,hb⟩
    have hc : ¬ originConnected σ P k source.val.formula (O.last source) := by
      intro hconn
      exact T.ledger_source_not_eligible w.in_ledger ⟨source,rfl,hconn⟩
    have hbefore := (O.classification source).resolve_left hc
    have hf : source.val.formula = q.val.formula :=
      (congrArg Predicate.formula hs).trans ((bounded_formula _ _ _ _ _ _ _).trans hqformula.symm)
    exact ⟨.ended w source rfl hf hbefore⟩


namespace NextOriginCause
variable {J : MixedJ Clock Var} {W : Set Clock} {owned : OwnedPending J N.resets W}
    {O : InputOrigins σ P α k N} {H Er : MixedJ Clock Var}
    {T : SelectedTree O.eligible O.strictClocks owned H Er} {hk : k.val < P.size}
    {M : Section3.StateForm Clock Var} {q : BoundedLocal M}

noncomputable def last (cause : NextOriginCause owned O T hk q) : Fin P.size :=
  match cause with
  | .ended _ source _ _ _ => O.last source
  | .born _ _ _ ht => (truthBlockOf σ P q.val.formula ⟨k.val,hk⟩ ht).val

theorem is_end (cause : NextOriginCause owned O T hk q) :
    IsEnd (PieceTrue σ P q.val.formula) cause.last := by
  cases cause with
  | ended w source hs hf hb =>
    have he := O.is_end source
    rw [hf] at he
    exact he
  | born w hu hf ht => exact (truthBlockOf σ P q.val.formula ⟨k.val,hk⟩ ht).property
end NextOriginCause

omit [DecidableEq Clock] in
private theorem filterMap_fiber_unique {A B : Type*} (f : A → Option B)
    (L : List A) (hn : (L.filterMap f).Nodup) {a b : A} {v : B}
    (ha : a ∈ L) (hb : b ∈ L) (hfa : f a = some v) (hfb : f b = some v) : a = b := by
  induction L with
  | nil => cases ha
  | cons x L ih =>
    cases hx : f x with
    | none =>
      have hn' : (L.filterMap f).Nodup := by simpa only [List.filterMap_cons,hx] using hn
      have ha' : a ∈ L := by
        rcases List.mem_cons.mp ha with rfl | ha
        · rw [hx] at hfa; cases hfa
        · exact ha
      have hb' : b ∈ L := by
        rcases List.mem_cons.mp hb with rfl | hb
        · rw [hx] at hfb; cases hfb
        · exact hb
      exact ih hn' ha' hb'
    | some y =>
      have hn' : y ∉ L.filterMap f ∧ (L.filterMap f).Nodup :=
        List.nodup_cons.mp (by simpa only [List.filterMap_cons,hx] using hn)
      rcases List.mem_cons.mp ha with hax | haTail
      · rcases List.mem_cons.mp hb with hbx | hbTail
        · exact hax.trans hbx.symm
        · have hfx : f x = some v := by rw [← hax]; exact hfa
          have hv : y = v := Option.some.inj (hx.symm.trans hfx)
          have hmem : y ∈ L.filterMap f := by rw [hv]; exact List.mem_filterMap.mpr ⟨b,hbTail,hfb⟩
          exact False.elim (hn'.1 hmem)
      · rcases List.mem_cons.mp hb with hbx | hbTail
        · have hfx : f x = some v := by rw [← hbx]; exact hfb
          have hv : y = v := Option.some.inj (hx.symm.trans hfx)
          have hmem : y ∈ L.filterMap f := by rw [hv]; exact List.mem_filterMap.mpr ⟨a,haTail,hfa⟩
          exact False.elim (hn'.1 hmem)
        · exact ih hn'.2 haTail hbTail

private theorem witness_target_unique
    {J : MixedJ Clock Var} {W : Set Clock} {owned : OwnedPending J N.resets W}
    {O : InputOrigins σ P α k N} {H Er : MixedJ Clock Var}
    {T : SelectedTree O.eligible O.strictClocks owned H Er}
    {M : Section3.StateForm Clock Var} {q r : BoundedLocal M}
    (w : NextBoundedWitness owned O T q) (v : NextBoundedWitness owned O T r)
    (he : w.entry = v.entry) : q = r := by
  obtain ⟨c,d,m,b,kind,I,φ,hq⟩ := bounded_params q
  obtain ⟨c',d',m',b',kind',I',φ',hr⟩ := bounded_params r
  have hqc : Predicate.bounded c d m b kind I φ ∈ w.payload.currentPredicates := by rw [← hq]; exact w.current
  have hrc : Predicate.bounded c' d' m' b' kind' I' φ' ∈ v.payload.currentPredicates := by rw [← hr]; exact v.current
  have hvo : Conjunct w.entry.body (.next v.payload) := by rw [he]; exact v.occurrence
  have hpred := w.entry.actual.next_bounded_unique w.occurrence hvo
    c d m b kind I φ c' d' m' b' kind' I' φ' hqc hrc
  exact Subtype.ext (hq.trans (hpred.trans hr.symm))

/-- The chosen actual causes assign distinct block endpoints to distinct
successor locals of the same formula. No source-entry identity is assumed. -/
theorem next_cause_injective
    {J : MixedJ Clock Var} {W : Set Clock} {owned : OwnedPending J N.resets W}
    (O : InputOrigins σ P α k N) {H Er : MixedJ Clock Var}
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (hLocal : ∀ l, l ∈ owned.locals ↔ l ∈ N.locals)
    {hk : k.val < P.size} {M : Section3.StateForm Clock Var} {q r : BoundedLocal M}
    (cause : NextOriginCause owned O T hk q) (other : NextOriginCause owned O T hk r)
    (hf : q.val.formula = r.val.formula) (hl : cause.last = other.last) : q = r := by
  classical
  cases cause with
  | ended w source hs hform hb =>
    cases other with
    | ended v source' hs' hform' hb' =>
      have hsource := O.injective_per_formula source source'
        (hform.trans (hf.trans hform'.symm)) hl
      have hproj : w.entry.boundedSource = some source.val := by
        obtain ⟨c,d,m,b,kind,I,φ,hshape⟩ := bounded_params source
        simp only [RawLedgerEntry.boundedSource,hs,hshape]
      have hproj' : v.entry.boundedSource = some source.val := by
        have hsame : source'.val = source.val := congrArg Subtype.val hsource.symm
        obtain ⟨c,d,m,b,kind,I,φ,hshape⟩ := bounded_params source
        simp only [RawLedgerEntry.boundedSource,hs',hsame,hshape]
      have he := filterMap_fiber_unique RawLedgerEntry.boundedSource T.rawLedger T.bounded_ledger_nodup
        w.in_ledger v.in_ledger hproj hproj'
      exact witness_target_unique w v he
    | born v hu hform' ht =>
      have hge : k.val ≤ (truthBlockOf σ P r.val.formula ⟨k.val,hk⟩ ht).val.val :=
        connected_le_end _ _ (blockOf_connected _ _ ht)
      change O.last source = (truthBlockOf σ P r.val.formula ⟨k.val,hk⟩ ht).val at hl
      have := congrArg Fin.val hl
      omega
  | born w hu hform ht =>
    cases other with
    | ended v source hs hform' hb =>
      have hge : k.val ≤ (truthBlockOf σ P q.val.formula ⟨k.val,hk⟩ ht).val.val :=
        connected_le_end _ _ (blockOf_connected _ _ ht)
      change (truthBlockOf σ P q.val.formula ⟨k.val,hk⟩ ht).val = O.last source at hl
      have := congrArg Fin.val hl
      omega
    | born v hu' hform' ht' =>
      let f : RawLedgerEntry (Clock := Clock) (Var := Var) → Option (Formula Var) := fun entry =>
        match entry.source with | .upper _ _ kind I φ => some (timedFormula kind I φ) | _ => none
      have hn : (T.rawLedger.filterMap f).Nodup :=
        T.upper_ledger_formulas_nodup (fun p hp q hq he => O.eligible_unique_formula hp hq he)
          (fun c m kind I φ hm => O.no_upper c m kind I φ ((hLocal _).1 hm))
      have hp : f w.entry = some q.val.formula := by
        obtain ⟨c,b,kind,I,φ,hs⟩ := hu
        have hformula := ((congrArg Predicate.formula hs).trans (upper_formula _ _ _ _ _)).symm.trans hform
        simpa only [f,hs] using congrArg some hformula
      have hp' : f v.entry = some q.val.formula := by
        obtain ⟨c,b,kind,I,φ,hs⟩ := hu'
        have hformula := ((congrArg Predicate.formula hs).trans (upper_formula _ _ _ _ _)).symm.trans
          (hform'.trans hf.symm)
        simpa only [f,hs] using congrArg some hformula
      exact witness_target_unique w v
        (filterMap_fiber_unique f T.rawLedger hn w.in_ledger v.in_ledger hp hp')

end InputOrigins
end STLTableau.Section4.Finiteness
