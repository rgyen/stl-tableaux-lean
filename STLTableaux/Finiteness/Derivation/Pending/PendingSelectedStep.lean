import STLTableaux.Finiteness.Derivation.Pending.PendingOrdinaryChild

/-! Source facts extracted from the actual owned input, before selecting a rule. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

/-- A selected local exposes the original residual list, with source/residual
truth and full invariant derived from the input rather than assumed. -/
theorem owned_selected_facts
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (p : Predicate Clock Var)
    (left right : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate p :: right)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hReady : J.Ready) (hHolds : Judgement.holds σ P α k J)
    (hInv : J.EvaluatedInvariant σ P α k) (hStable : J.UnderlyingStable σ P) :
    p.Ready ∧ Judgement.holds σ P (R.apply α) k (.predicate p) ∧
      (∀ hk : k.val < P.size, p.Invariant σ P (R.apply α) k hk) ∧
      σ.StablePartition p.formula P ∧
      ∀ Γ, foldCurrent ((left ++ right).map Local.toJudgement ++
          owned.nextInputs.map Section3.Judgement.next) = some Γ →
        Γ.Ready ∧ Judgement.holds σ P (R.apply α) k Γ ∧
          Γ.EvaluatedInvariant σ P (R.apply α) k ∧ Γ.UnderlyingStable σ P := by
  have hnonempty : owned.locals.map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next ≠ [] := by
    rw [hsplit]
    simp only [List.map_append,List.map_cons,List.append_assoc]
    simp
  obtain ⟨Body,hBody⟩ : ∃ Body, foldCurrent (owned.locals.map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) = some Body := by
    cases h : foldCurrent (owned.locals.map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) with
    | some Body => exact ⟨Body,rfl⟩
    | none => exact False.elim (hnonempty ((foldCurrent_none_iff _).1 h))
  have hsplitFold : foldCurrent (left.map Local.toJudgement ++ .predicate p ::
      (right.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next)) = some Body := by
    simpa only [hsplit,List.map_append,List.map_cons,List.append_assoc,List.cons_append,Local.toJudgement] using hBody
  have hExpose := (foldCurrent_expose_split (left.map Local.toJudgement)
    (right.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next)
    (.predicate p) Body hsplitFold).1
  have hFacts := canonical_body_facts owned.shape owned.regroup hBody σ P α k
    hReady hHolds hInv hStable
  have hSource := exposed_predicate_facts hExpose σ P (R.apply α) k
    hFacts.1 hFacts.2.1 hFacts.2.2.1 hFacts.2.2.2
  refine ⟨hSource.1,hSource.2.1,hSource.2.2.1,hSource.2.2.2.1,?_⟩
  intro Γ hΓ
  apply hSource.2.2.2.2 Γ
  simpa only [List.map_append,List.append_assoc] using hΓ

private theorem guards_weight_zero (G : List (Section3.Guard Clock))
    (C : MixedJ Clock Var)
    (h : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) = some C) :
    pendingWeight C = 0 := by
  induction G generalizing C with
  | nil => simp [foldCurrent] at h
  | cons g gs ih =>
    rw [List.map_cons,foldCurrent_cons] at h
    have he := Option.some.inj h
    subst C
    cases ht : foldCurrent (gs.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
    | none => cases g; rfl
    | some T =>
      have hz := ih T ht
      cases g; simpa only [prependCurrent,pendingWeight,Section3.Guard.toJudgement,
        Nat.zero_add] using hz

/-- Current guards and the inherited reset contribute no pending weight. -/
theorem canonical_body_weight
    {R : ClockResetSet Clock} {G : List (Section3.Guard Clock)}
    {L : List (Local Clock Var)} {Ns : List (MixedJ Clock Var)} {C Body : MixedJ Clock Var}
    (hshape : canonicalSyntax R G L Ns = some C)
    (hBody : foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next) = some Body) :
    pendingWeight C = pendingWeight Body := by
  cases hg : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
  | none =>
    have he : .reset R Body = C := by
      simpa only [canonicalSyntax,hg,hBody,Option.map_some,optionalConj,Option.some.injEq] using hshape
    subst C
    rfl
  | some Guards =>
    have he : .conj Guards (.reset R Body) = C := by
      simpa only [canonicalSyntax,hg,hBody,Option.map_some,optionalConj,Option.some.injEq] using hshape
    subst C
    simp only [pendingWeight,guards_weight_zero G Guards hg,Nat.zero_add]

theorem owned_selected_weight
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (p : Predicate Clock Var)
    (left right : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate p :: right) (Γ : MixedJ Clock Var)
    (hΓ : foldCurrent ((left ++ right).map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) = some Γ) :
    pendingWeight owned.canonical = pendingWeight (.conj (.predicate p) Γ) := by
  cases hBody : foldCurrent (owned.locals.map Local.toJudgement ++
    owned.nextInputs.map Section3.Judgement.next) with
  | none =>
    have he := (foldCurrent_none_iff _).1 hBody
    have hm : (.predicate p : MixedJ Clock Var) ∈ owned.locals.map Local.toJudgement ++
        owned.nextInputs.map Section3.Judgement.next := by
      rw [hsplit]
      simp [Local.toJudgement]
    rw [he] at hm
    cases hm
  | some Body =>
    have hsplitFold : foldCurrent (left.map Local.toJudgement ++ .predicate p ::
        (right.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next)) = some Body := by
      simpa only [hsplit,List.map_append,List.map_cons,List.append_assoc,List.cons_append,
        Local.toJudgement] using hBody
    have hw := (foldCurrent_expose_split (left.map Local.toJudgement)
      (right.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next)
      (.predicate p) Body hsplitFold).2
    have hΓ' : foldCurrent (left.map Local.toJudgement ++
        (right.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next)) = some Γ := by
      simpa only [List.map_append,List.append_assoc] using hΓ
    rw [canonical_body_weight owned.shape hBody,hw,hΓ']
    rfl

variable [DecidableEq Clock] [Infinite Clock]

/-- Actual positive step with every source and residual premise extracted from
the original ready, true, fully invariant owned input. -/
theorem exists_ordinary_child_present_of_input
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (A : Set Clock) (hA : A ⊆ W)
    (hprotected : protectedActive owned A) (hNext : NextPrivate J)
    (p : Predicate Clock Var) (left right : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate p :: right) (hn : ¬ p.IsAtomic)
    (Γ : MixedJ Clock Var)
    (hΓfold : foldCurrent ((left ++ right).map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) = some Γ)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hReady : J.Ready) (hHolds : Judgement.holds σ P α k J)
    (hInv : J.EvaluatedInvariant σ P α k) (hStable : J.UnderlyingStable σ P) :
    ∃ (x : Clock) (B : MixedJ Clock Var) (Rc : ClockResetSet Clock) (W' : Set Clock)
      (child : OwnedPending (.conj B (.reset (copyActiveResets R (left ++ right)) Γ)) Rc W'),
      x ∉ W ∧ RawBranch p B ∧
      FreshFor p B (.reset (copyActiveResets R (left ++ right)) Γ) ∧
      W ⊆ W' ∧ protectedActive child (A ∪ syntaxClocks (.predicate p)) ∧
      Disjoint Rc.clocks (A ∪ syntaxClocks (.predicate p)) ∧
      pendingWeight child.canonical < pendingWeight owned.canonical ∧
      (.conj B (.reset (copyActiveResets R (left ++ right)) Γ) : MixedJ Clock Var).Ready ∧
      Judgement.holds σ P (R.apply α) k (.conj B (.reset (copyActiveResets R (left ++ right)) Γ)) ∧
      (.conj B (.reset (copyActiveResets R (left ++ right)) Γ) : MixedJ Clock Var).EvaluatedInvariant σ P (R.apply α) k ∧
      (.conj B (.reset (copyActiveResets R (left ++ right)) Γ) : MixedJ Clock Var).UnderlyingStable σ P ∧
      NextPrivate (.conj B (.reset (copyActiveResets R (left ++ right)) Γ)) := by
  have h := owned_selected_facts owned p left right hsplit σ P α k
    hReady hHolds hInv hStable
  have hΓ := h.2.2.2.2 Γ hΓfold
  rw [owned_selected_weight owned p left right hsplit Γ hΓfold]
  exact exists_ordinary_child_present owned A hA hprotected hNext p left right hsplit hn Γ hΓfold
    σ P α k h.1 hΓ.1 h.2.2.1 h.2.2.2.1 h.2.1 hΓ.2.1 hΓ.2.2.1 hΓ.2.2.2

end STLTableau.Section4.Finiteness
