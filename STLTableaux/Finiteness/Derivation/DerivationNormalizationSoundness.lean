import STLTableaux.Finiteness.Derivation.DerivationNormalization
import STLTableaux.Rules.Invariants.NumericBranchPreservation
import STLTableaux.Closure.Normalization.FaithfulUnionSemantics
import STLTableaux.Closure.Subsumption.NumericGuardSubsumption
import STLTableaux.Syntax.FaithfulNormalizedSyntax

/-! Syntactic safety certificates for the actual mixed normalizer. Resolution
alone does not imply these certificates: arbitrary reset/conjunction contexts
can move guards out of reset scope or capture another conjunct's clocks. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

/-- A recursively checkable structural normalization certificate. In a reset,
current guards must avoid the enclosing reset's clock support. In a conjunction,
the existing exact syntactic UnionCompatible condition prevents capture. -/
inductive SafeNormalization : MixedJ Clock Var → Section3.TransitionForm Clock Var → Prop
  | terminal : SafeNormalization .terminal (.ofState (.ofLocal .terminal))
  | clock (c r a) : SafeNormalization (.clock c r a) (.ofState (.ofGuard ⟨c,r,a⟩))
  | marker (m) : SafeNormalization (.marker m) (.ofState (.ofLocal (.marker m)))
  | predicate (p) : SafeNormalization (.predicate p) (.ofState (.ofLocal (.predicate p)))
  | conj {J K F G} : SafeNormalization J F → SafeNormalization K G →
      F.UnionCompatible G → SafeNormalization (.conj J K) (F.union G)
  | reset (R) {J F} : SafeNormalization J F →
      Disjoint R.clocks F.current.guardClocks → SafeNormalization (.reset R J) (F.underReset R)
  | next {J F} : SafeNormalization J F → F.nextPart = none →
      SafeNormalization (.next J) (.ofNextState F.current)

/-- Successful normalization reflects readiness as well as preserving it.
This is syntactic and does not require a semantic safety certificate. -/
theorem normalize_ready_reverse (J : MixedJ Clock Var) {F : Section3.TransitionForm Clock Var}
    (hn : Section3.TransitionForm.normalize? J = some F) (hf : F.Ready) : J.Ready := by
  induction J generalizing F with
  | terminal => trivial
  | clock => trivial
  | marker => trivial
  | predicate p =>
    cases hn
    simpa only [Section3.TransitionForm.ready_ofState,Section3.StateForm.ready_ofLocal,
      Local.Ready,Judgement.Ready] using hf
  | reset R J ih =>
    cases he : Section3.TransitionForm.normalize? J with
    | none => simp [Section3.TransitionForm.normalize?,he] at hn
    | some G =>
      simp [Section3.TransitionForm.normalize?,he] at hn
      subst F
      exact ih he ((Section3.TransitionForm.ready_underReset G R).1 hf)
  | conj J K ih ig =>
    cases he : Section3.TransitionForm.normalize? J with
    | none => simp [Section3.TransitionForm.normalize?,he] at hn
    | some G =>
      cases he' : Section3.TransitionForm.normalize? K with
      | none => simp [Section3.TransitionForm.normalize?,he,he'] at hn
      | some H =>
        simp [Section3.TransitionForm.normalize?,he,he'] at hn
        subst F
        have hs := (Section3.TransitionForm.ready_union G H).1 hf
        exact ⟨ih he hs.1,ig he' hs.2⟩
  | next J ih =>
    cases he : Section3.TransitionForm.normalize? J with
    | none => simp [Section3.TransitionForm.normalize?,he] at hn
    | some G =>
      cases hx : G.nextPart with
      | some N => simp [Section3.TransitionForm.normalize?,he,hx] at hn
      | none =>
        simp [Section3.TransitionForm.normalize?,he,hx] at hn
        subst F
        apply ih he
        have hcur := (Section3.TransitionForm.ready_ofNextState G.current).1 hf
        exact ⟨hcur,by intro N hN; rw [hx] at hN; cases hN⟩

theorem normalize_ready_iff (J : MixedJ Clock Var) {F : Section3.TransitionForm Clock Var}
    (hn : Section3.TransitionForm.normalize? J = some F) : F.Ready ↔ J.Ready :=
  ⟨normalize_ready_reverse J hn,Section3.TransitionForm.normalize_ready J hn⟩

namespace SafeNormalization

theorem normalizes {J : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : SafeNormalization J F) : Section3.TransitionForm.normalize? J = some F := by
  induction h with
  | terminal => rfl
  | clock => rfl
  | marker => rfl
  | predicate => rfl
  | conj h g hc ih ig => simp [Section3.TransitionForm.normalize?,ih,ig]
  | reset R h hd ih => simp [Section3.TransitionForm.normalize?,ih]
  | next h hn ih => simp [Section3.TransitionForm.normalize?,ih,hn]

theorem ready {J : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : SafeNormalization J F) : F.Ready ↔ J.Ready :=
  normalize_ready_iff J h.normalizes

private theorem reset_guard_agree (F : Section3.TransitionForm Clock Var)
    (R : ClockResetSet Clock) (hd : Disjoint R.clocks F.current.guardClocks)
    (α : ClockValuation Clock) (g : Guard Clock) (hg : g ∈ F.current.guards) :
    R.apply α g.clock = α g.clock := by
  have hn : R.value g.clock = none := by
    cases hr : R.value g.clock with
    | none => rfl
    | some a => exact False.elim (Set.disjoint_left.1 hd ⟨a,hr⟩ ⟨g,hg,rfl⟩)
  unfold ClockResetSet.apply
  rw [hn]

theorem underReset_holds (F : Section3.TransitionForm Clock Var)
    (R : ClockResetSet Clock) (hd : Disjoint R.clocks F.current.guardClocks)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (F.underReset R).holds σ P α k ↔ F.holds σ P (R.apply α) k := by
  simp only [Section3.TransitionForm.underReset,Section3.TransitionForm.holds,
    Section3.StateForm.holds,ClockResetSet.apply_union_eq_comp]
  apply and_congr (and_congr ?_ Iff.rfl) Iff.rfl
  apply forall_congr'; intro g
  apply forall_congr'; intro hg
  simp only [Guard.holds,reset_guard_agree F R hd α g hg]

theorem underReset_nonPredicate (F : Section3.TransitionForm Clock Var)
    (R : ClockResetSet Clock) (hd : Disjoint R.clocks F.current.guardClocks)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (F.underReset R).nonPredicateHolds σ P α k ↔ F.nonPredicateHolds σ P (R.apply α) k := by
  simp only [Section3.TransitionForm.underReset,Section3.TransitionForm.nonPredicateHolds,
    Section3.StateForm.nonPredicateHolds,ClockResetSet.apply_union_eq_comp]
  apply and_congr (and_congr ?_ Iff.rfl) Iff.rfl
  apply forall_congr'; intro g
  apply forall_congr'; intro hg
  simp only [Guard.holds,reset_guard_agree F R hd α g hg]

theorem union_nonPredicate_of_agree (S T : Section3.StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α β γ : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hS : ∀ c ∈ S.localClocks, S.resets.apply α c = (S.union T).resets.apply γ c)
    (hT : ∀ c ∈ T.localClocks, T.resets.apply β c = (S.union T).resets.apply γ c)
    (hgS : ∀ c ∈ S.guardClocks, α c = γ c)
    (hgT : ∀ c ∈ T.guardClocks, β c = γ c)
    (hs : S.nonPredicateHolds σ P α k) (ht : T.nonPredicateHolds σ P β k) : (S.union T).nonPredicateHolds σ P γ k := by
  constructor
  · intro g hg
    rcases hg with hg | hg
    · simpa only [Guard.holds,← hgS g.clock ⟨g,hg,rfl⟩] using hs.1 g hg
    · simpa only [Guard.holds,← hgT g.clock ⟨g,hg,rfl⟩] using ht.1 g hg
  · intro l hl
    rcases hl with hl | hl
    · exact (l.nonPredicate_congr_of_agree σ P _ _ k (fun c hc => hS c ⟨l,hl,hc⟩)).1 (hs.2 l hl)
    · exact (l.nonPredicate_congr_of_agree σ P _ _ k (fun c hc => hT c ⟨l,hl,hc⟩)).1 (ht.2 l hl)

theorem union_numeric_of_agree (S T : Section3.StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α β γ : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hS : ∀ c ∈ S.localClocks, S.resets.apply α c = (S.union T).resets.apply γ c)
    (hT : ∀ c ∈ T.localClocks, T.resets.apply β c = (S.union T).resets.apply γ c)
    (hs : S.EvaluatedNumeric σ P α k) (ht : T.EvaluatedNumeric σ P β k) :
    (S.union T).EvaluatedNumeric σ P γ k := by
  intro l hl
  rcases hl with hl | hl
  · exact (l.evaluatedNumeric_congr σ P _ _ k (fun c hc => hS c ⟨l,hl,hc⟩)).1 (hs l hl)
  · exact (l.evaluatedNumeric_congr σ P _ _ k (fun c hc => hT c ⟨l,hl,hc⟩)).1 (ht l hl)
private theorem outer_agree {Φ Ψ : Section3.TransitionForm Clock Var}
    (h : Section3.SyntacticallySubsumed Φ Ψ) (α : ClockValuation Clock) :
    ∀ c ∈ Φ.bodyFreeClocks, Φ.current.resets.apply α c = Ψ.current.resets.apply α c :=
  Section3.reset_apply_agree h.current.resets α α Φ.bodyFreeClocks h.outerFresh (fun _ _ => rfl)

private theorem current_agree {Φ Ψ : Section3.TransitionForm Clock Var}
    (h : Section3.SyntacticallySubsumed Φ Ψ) (α : ClockValuation Clock) :
    ∀ c ∈ Φ.current.localClocks, Φ.current.resets.apply α c = Ψ.current.resets.apply α c :=
  fun c hc => outer_agree h α c (Or.inl hc)

private theorem next_incoming_agree {Φ Ψ : Section3.TransitionForm Clock Var}
    (h : Section3.SyntacticallySubsumed Φ Ψ) {N : Section3.StateForm Clock Var} (hn : Φ.nextPart = some N)
    (α : ClockValuation Clock) (δ : NNReal) :
    ∀ c ∈ N.freeClocks,
      ClockResetSet.elapse (Φ.current.resets.apply α) δ c =
      ClockResetSet.elapse (Ψ.current.resets.apply α) δ c := by
  intro c hc
  exact congrArg (fun x => x+δ) (outer_agree h α c (Or.inr (by simpa only [hn] using hc)))

theorem union_nonPredicate {Φ Ψ : Section3.TransitionForm Clock Var} (h : Φ.UnionCompatible Ψ)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (Φ.union Ψ).nonPredicateHolds σ P α k ↔ Φ.nonPredicateHolds σ P α k ∧ Ψ.nonPredicateHolds σ P α k := by
  constructor
  · intro hs; exact ⟨h.left.nonPredicateHolds σ P α k hs,h.right.nonPredicateHolds σ P α k hs⟩
  · rintro ⟨hf,hg⟩
    refine ⟨union_nonPredicate_of_agree _ _ σ P α α α k
      (current_agree h.left α) (current_agree h.right α)
      (fun _ _ => rfl) (fun _ _ => rfl) hf.1 hg.1,?_⟩
    cases hn : Φ.nextPart with
    | none =>
        cases hm : Ψ.nextPart with
        | none => simp [Section3.TransitionForm.union,Section3.TransitionForm.unionNext,hn,hm]
        | some M =>
            simp only [Section3.TransitionForm.nonPredicateHolds,hm] at hg
            simp only [Section3.TransitionForm.union,Section3.TransitionForm.unionNext,hn,hm]
            by_cases hk : k.1 < P.size
            · simp only [dif_pos hk] at hg ⊢
              exact (M.nonPredicate_congr_of_agree σ P _ _ _ (next_incoming_agree h.right hm α _)).1 hg.2
            · simpa only [dif_neg hk] using hg.2
    | some N =>
        simp only [Section3.TransitionForm.nonPredicateHolds,hn] at hf
        cases hm : Ψ.nextPart with
        | none =>
            simp only [Section3.TransitionForm.union,Section3.TransitionForm.unionNext,hn,hm]
            by_cases hk : k.1 < P.size
            · simp only [dif_pos hk] at hf ⊢
              exact (N.nonPredicate_congr_of_agree σ P _ _ _ (next_incoming_agree h.left hn α _)).1 hf.2
            · simpa only [dif_neg hk] using hf.2
        | some M =>
            simp only [Section3.TransitionForm.nonPredicateHolds,hm] at hg
            simp only [Section3.TransitionForm.union,Section3.TransitionForm.unionNext,hn,hm]
            by_cases hk : k.1 < P.size
            · simp only [dif_pos hk] at hf hg ⊢
              obtain ⟨K,hK,hNK,hfreshN⟩ := h.left.next N hn
              obtain ⟨L,hL,hML,hfreshM⟩ := h.right.next M hm
              have hKN : K = N.union M := by simpa [Section3.TransitionForm.union,Section3.TransitionForm.unionNext,hn,hm] using hK.symm
              have hLM : L = N.union M := by simpa [Section3.TransitionForm.union,Section3.TransitionForm.unionNext,hn,hm] using hL.symm
              subst K; subst L
              apply union_nonPredicate_of_agree _ _ σ P _ _ _ _ _ _ _ _ hf.2 hg.2
              · exact Section3.reset_apply_agree hNK.resets _ _ N.localClocks hfreshN
                  (fun c hc => next_incoming_agree h.left hn α _ c (Or.inr hc))
              · exact Section3.reset_apply_agree hML.resets _ _ M.localClocks hfreshM
                  (fun c hc => next_incoming_agree h.right hm α _ c (Or.inr hc))
              · exact fun c hc => next_incoming_agree h.left hn α _ c (Or.inl hc)
              · exact fun c hc => next_incoming_agree h.right hm α _ c (Or.inl hc)
            · simpa only [dif_neg hk] using hf.2
theorem union_numeric_forward {Φ Ψ : Section3.TransitionForm Clock Var}
    (h : Φ.UnionCompatible Ψ)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hf : Φ.EvaluatedNumeric σ P α k) (hg : Ψ.EvaluatedNumeric σ P α k) :
    (Φ.union Ψ).EvaluatedNumeric σ P α k := by
  refine ⟨union_numeric_of_agree _ _ σ P α α α k
    (current_agree h.left α) (current_agree h.right α) hf.1 hg.1,?_⟩
  intro K hK hk
  cases hn : Φ.nextPart with
  | none =>
      cases hm : Ψ.nextPart with
      | none => simp [Section3.TransitionForm.union,Section3.TransitionForm.unionNext,hn,hm] at hK
      | some M =>
          have he : K = M := by simpa [Section3.TransitionForm.union,Section3.TransitionForm.unionNext,hn,hm] using hK.symm
          subst K
          exact (M.evaluatedNumeric_congr σ P _ _ _
            (next_incoming_agree h.right hm α _)).1 (hg.2 M hm hk)
  | some N =>
      cases hm : Ψ.nextPart with
      | none =>
          have he : K = N := by simpa [Section3.TransitionForm.union,Section3.TransitionForm.unionNext,hn,hm] using hK.symm
          subst K
          exact (N.evaluatedNumeric_congr σ P _ _ _
            (next_incoming_agree h.left hn α _)).1 (hf.2 N hn hk)
      | some M =>
          have he : K = N.union M := by simpa [Section3.TransitionForm.union,Section3.TransitionForm.unionNext,hn,hm] using hK.symm
          subst K
          obtain ⟨K,hKN,hNK,hfreshN⟩ := h.left.next N hn
          obtain ⟨L,hLM,hML,hfreshM⟩ := h.right.next M hm
          have hKN' : K = N.union M := by simpa [Section3.TransitionForm.union,Section3.TransitionForm.unionNext,hn,hm] using hKN.symm
          have hLM' : L = N.union M := by simpa [Section3.TransitionForm.union,Section3.TransitionForm.unionNext,hn,hm] using hLM.symm
          subst K; subst L
          apply union_numeric_of_agree _ _ σ P _ _ _ _ _ _ (hf.2 N hn hk) (hg.2 M hm hk)
          · exact Section3.reset_apply_agree hNK.resets _ _ N.localClocks hfreshN
              (fun c hc => next_incoming_agree h.left hn α _ c (Or.inr hc))
          · exact Section3.reset_apply_agree hML.resets _ _ M.localClocks hfreshM
              (fun c hc => next_incoming_agree h.right hm α _ c (Or.inr hc))

theorem subsumed_numeric {F G : Section3.TransitionForm Clock Var}
    (h : Section3.SyntacticallySubsumed F G) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : G.EvaluatedNumeric σ P α k) : F.EvaluatedNumeric σ P α k := by
  constructor
  · intro l hl
    exact (l.evaluatedNumeric_congr σ P _ _ k
      (fun c hc => current_agree h α c ⟨l,hl,hc⟩)).2 (hs.1 l (h.current.locals hl))
  · intro N hN hk l hl
    obtain ⟨M,hM,hNM,hfresh⟩ := h.next N hN
    have he := Section3.reset_apply_agree hNM.resets
      (ClockResetSet.elapse (F.current.resets.apply α) (STLTableau.Judgement.duration P ⟨k.1,hk⟩))
      (ClockResetSet.elapse (G.current.resets.apply α) (STLTableau.Judgement.duration P ⟨k.1,hk⟩))
      N.localClocks hfresh
      (fun c hc => next_incoming_agree h hN α _ c (Or.inr hc))
    exact (l.evaluatedNumeric_congr σ P _ _ _
      (fun c hc => he c ⟨l,hl,hc⟩)).2 (hs.2 M hM hk l (hNM.locals hl))

theorem union_numeric {F G : Section3.TransitionForm Clock Var} (h : F.UnionCompatible G)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (F.union G).EvaluatedNumeric σ P α k ↔
      F.EvaluatedNumeric σ P α k ∧ G.EvaluatedNumeric σ P α k :=
  ⟨fun hs => ⟨subsumed_numeric h.left σ P α k hs,subsumed_numeric h.right σ P α k hs⟩,
    fun hs => union_numeric_forward h σ P α k hs.1 hs.2⟩

/-- Semantic normalization is proved from syntactic safety, never placed as a
field in a graph relation or presumed from a successful normalize? equation. -/
theorem holds {J : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : SafeNormalization J F) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :
    F.holds σ P α k ↔ Judgement.holds σ P α k J := by
  induction h generalizing α k with
  | terminal => simp [Section3.TransitionForm.ofState,Section3.TransitionForm.holds,
      Section3.StateForm.ofLocal,Section3.StateForm.holds,Local.holds,Local.toJudgement,
      Judgement.holds,ClockResetSet.apply_empty]
  | clock c r a => simp [Section3.TransitionForm.ofState,Section3.TransitionForm.holds,
      Section3.StateForm.ofGuard,Section3.StateForm.holds,Guard.holds,Judgement.holds]
  | marker m => simp [Section3.TransitionForm.ofState,Section3.TransitionForm.holds,
      Section3.StateForm.ofLocal,Section3.StateForm.holds,Local.holds,Local.toJudgement,
      Judgement.holds,ClockResetSet.apply_empty]
  | predicate p => simp [Section3.TransitionForm.ofState,Section3.TransitionForm.holds,
      Section3.StateForm.ofLocal,Section3.StateForm.holds,Local.holds,Local.toJudgement,
      Judgement.holds,ClockResetSet.apply_empty]
  | conj h g hc ih ig => exact (hc.holds σ P α k).trans (and_congr (ih α k) (ig α k))
  | reset R h hd ih => exact (underReset_holds _ R hd σ P α k).trans (ih (R.apply α) k)
  | @next J F h hn ih =>
    simp only [Section3.TransitionForm.ofNextState,Section3.TransitionForm.holds,
      Section3.StateForm.empty,Section3.StateForm.holds,Set.mem_empty_iff_false,
      IsEmpty.forall_iff,implies_true,true_and,ClockResetSet.apply_empty,Judgement.holds]
    split
    · simpa only [Section3.TransitionForm.holds,Section3.StateForm.holds,hn,and_true] using ih _ _
    · rfl

/-- Numeric correspondence uses only capture-safe component agreement; it does
not strengthen numeric hypotheses to the full invariant for no past satisfaction. -/
theorem numeric {J : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : SafeNormalization J F) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :
    F.EvaluatedNumeric σ P α k ↔ Judgement.EvaluatedNumeric σ P α k J := by
  induction h generalizing α k with
  | terminal => simp [Section3.TransitionForm.ofState,Section3.TransitionForm.EvaluatedNumeric,
      Section3.StateForm.ofLocal,Section3.StateForm.EvaluatedNumeric,Local.Numeric,
      Local.toJudgement,Judgement.EvaluatedNumeric]
  | clock c r a => simp [Section3.TransitionForm.ofState,Section3.TransitionForm.EvaluatedNumeric,
      Section3.StateForm.ofGuard,Section3.StateForm.EvaluatedNumeric,Judgement.EvaluatedNumeric]
  | marker m => simp [Section3.TransitionForm.ofState,Section3.TransitionForm.EvaluatedNumeric,
      Section3.StateForm.ofLocal,Section3.StateForm.EvaluatedNumeric,Local.Numeric,
      Local.toJudgement,Judgement.EvaluatedNumeric]
  | predicate p => simp [Section3.TransitionForm.ofState,Section3.TransitionForm.EvaluatedNumeric,
      Section3.StateForm.ofLocal,Section3.StateForm.EvaluatedNumeric,Local.Numeric,
      Local.toJudgement,Judgement.EvaluatedNumeric,ClockResetSet.apply_empty]
  | conj h g hc ih ig => exact (union_numeric hc σ P α k).trans (and_congr (ih α k) (ig α k))
  | reset R h hd ih => exact (Section3.TransitionForm.underReset_numeric _ R σ P α k).trans (ih (R.apply α) k)
  | @next J F h hn ih =>
    simp only [Section3.TransitionForm.ofNextState,Section3.TransitionForm.EvaluatedNumeric,
      Section3.StateForm.empty,Section3.StateForm.EvaluatedNumeric,Set.mem_empty_iff_false,
      IsEmpty.forall_iff,implies_true,true_and,Option.some.injEq,forall_eq',ClockResetSet.apply_empty,
      Judgement.EvaluatedNumeric]
    apply forall_congr'; intro hk
    simpa [Section3.TransitionForm.EvaluatedNumeric,Section3.StateForm.EvaluatedNumeric,hn] using ih _ _

/-- Guard/marker correspondence likewise follows from the syntactic safety
certificate, including the precise enclosing-reset guard support condition. -/
theorem nonPredicate {J : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : SafeNormalization J F) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :
    F.nonPredicateHolds σ P α k ↔ Judgement.nonPredicateHolds σ P α k J := by
  induction h generalizing α k with
  | terminal => simp [Section3.TransitionForm.ofState,Section3.TransitionForm.nonPredicateHolds,
      Section3.StateForm.ofLocal,Section3.StateForm.nonPredicateHolds,Local.nonPredicateHolds,
      Local.toJudgement,Judgement.nonPredicateHolds,ClockResetSet.apply_empty]
  | clock c r a => simp [Section3.TransitionForm.ofState,Section3.TransitionForm.nonPredicateHolds,
      Section3.StateForm.ofGuard,Section3.StateForm.nonPredicateHolds,Guard.holds,Judgement.nonPredicateHolds]
  | marker m => simp [Section3.TransitionForm.ofState,Section3.TransitionForm.nonPredicateHolds,
      Section3.StateForm.ofLocal,Section3.StateForm.nonPredicateHolds,Local.nonPredicateHolds,
      Local.toJudgement,Judgement.nonPredicateHolds,ClockResetSet.apply_empty]
  | predicate p => simp [Section3.TransitionForm.ofState,Section3.TransitionForm.nonPredicateHolds,
      Section3.StateForm.ofLocal,Section3.StateForm.nonPredicateHolds,Local.nonPredicateHolds,
      Local.toJudgement,Judgement.nonPredicateHolds]
  | conj h g hc ih ig => exact (union_nonPredicate hc σ P α k).trans (and_congr (ih α k) (ig α k))
  | reset R h hd ih => exact (underReset_nonPredicate _ R hd σ P α k).trans (ih (R.apply α) k)
  | @next J F h hn ih =>
    simp only [Section3.TransitionForm.ofNextState,Section3.TransitionForm.nonPredicateHolds,
      Section3.StateForm.empty,Section3.StateForm.nonPredicateHolds,Set.mem_empty_iff_false,
      IsEmpty.forall_iff,implies_true,true_and,ClockResetSet.apply_empty,Judgement.nonPredicateHolds]
    split
    · simpa only [Section3.TransitionForm.nonPredicateHolds,Section3.StateForm.nonPredicateHolds,hn,and_true] using ih _ _
    · rfl

private theorem reset_ext {R S : ClockResetSet Clock} (h : R.value = S.value) : R = S := by
  cases R
  cases S
  cases h
  rfl

/-- Splitting the actual paired check reset into two singleton scopes leaves
its normalized transition form identical when the two clock names differ. -/
theorem underReset_pair [DecidableEq Clock] (F : Section3.TransitionForm Clock Var)
    (c d : Clock) (a : NNReal) (hcd : c ≠ d) :
    (F.underReset (ClockResetSet.singleton d 0)).underReset (ClockResetSet.singleton c a) =
      F.underReset ((ClockResetSet.singleton c a).union (ClockResetSet.singleton d 0)) := by
  apply congrArg₂ Section3.TransitionForm.mk
  · apply Section3.StateForm.ext_components
    · rfl
    · apply reset_ext
      funext x
      change ((F.current.resets.union (ClockResetSet.singleton d 0)).union
        (ClockResetSet.singleton c a)).value x =
        (F.current.resets.union ((ClockResetSet.singleton c a).union
          (ClockResetSet.singleton d 0))).value x
      cases hx : F.current.resets.value x with
      | some v => simp only [ClockResetSet.union,hx]
      | none =>
        simp only [ClockResetSet.union,hx]
        by_cases hxc : x = c
        · subst x
          simp only [ClockResetSet.singleton,if_true,if_neg hcd]
        · by_cases hxd : x = d
          · subst x
            simp only [ClockResetSet.singleton,if_true,if_neg hcd.symm]
          · simp only [ClockResetSet.singleton,if_neg hxc,if_neg hxd]
    · rfl
  · rfl

theorem paired_reset [DecidableEq Clock]
    {J : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var} (h : SafeNormalization J F)
    (c d : Clock) (a : NNReal)
    (hc : Disjoint (ClockResetSet.singleton c a).clocks F.current.guardClocks)
    (hd : Disjoint (ClockResetSet.singleton d 0).clocks F.current.guardClocks) :
    SafeNormalization (.reset ((ClockResetSet.singleton c a).union (ClockResetSet.singleton d 0)) J)
      (F.underReset ((ClockResetSet.singleton c a).union (ClockResetSet.singleton d 0))) := by
  apply SafeNormalization.reset _ h
  rw [ClockResetSet.clocks_union]
  exact hc.union_left hd

/-- A nested singleton check-reset certificate can target exactly the same
normal form as the literal paired-reset branch. All three semantic laws above
then apply to both presentations, with no assumed semantic equivalence. -/
theorem nested_pair_reset [DecidableEq Clock]
    {J : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var} (h : SafeNormalization J F)
    (c d : Clock) (a : NNReal) (hcd : c ≠ d)
    (hc : Disjoint (ClockResetSet.singleton c a).clocks F.current.guardClocks)
    (hd : Disjoint (ClockResetSet.singleton d 0).clocks F.current.guardClocks) :
    SafeNormalization (.reset (ClockResetSet.singleton c a)
      (.reset (ClockResetSet.singleton d 0) J))
      (F.underReset ((ClockResetSet.singleton c a).union (ClockResetSet.singleton d 0))) := by
  have hn := SafeNormalization.reset (ClockResetSet.singleton c a)
    (SafeNormalization.reset (ClockResetSet.singleton d 0) h hd) hc
  rw [underReset_pair F c d a hcd] at hn
  exact hn

end SafeNormalization

/-- A lawful resolution witness can still be unsafe to normalize: the raw
reset makes the guard true, while normalization moves that guard outside it.
Thus Resolve alone cannot establish semantic normalization correspondence. -/
theorem unsafe_resolve_normalization [DecidableEq Clock] (c : Clock)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (k : STLTableau.Judgement.Position P) :
    ∃ (J : MixedJ Clock Var) (F : Section3.TransitionForm Clock Var),
      Nonempty (Resolve J J J) ∧ Section3.TransitionForm.normalize? J = some F ∧
      Judgement.holds σ P (fun _ => 1) k J ∧ ¬ F.holds σ P (fun _ => 1) k := by
  let R := ClockResetSet.singleton c 0
  let J : MixedJ Clock Var := .reset R (.clock c .eq 0)
  let F : Section3.TransitionForm Clock Var := (Section3.TransitionForm.ofState (Section3.StateForm.ofGuard (⟨c,.eq,0⟩ : Guard Clock))).underReset R
  refine ⟨J,F,⟨.reset R (.leaf (.clock c .eq 0))⟩,rfl,?_,?_⟩
  · simp [J,R,Judgement.holds,ClockRelation.Holds]
  · simp [F,Section3.TransitionForm.underReset,Section3.TransitionForm.ofState,
      Section3.TransitionForm.holds,Section3.StateForm.ofGuard,Section3.StateForm.holds,
      Guard.holds,ClockRelation.Holds]

end STLTableau.Section4.Finiteness
