import STLTableaux.Finiteness.Derivation.Pending.PendingOwnership
import STLTableaux.Finiteness.Derivation.DerivationReady
import STLTableaux.Finiteness.Derivation.CompletionInvariantTransport

/-! Inversion of actual input presentation certificates. These facts provide
semantic premises for selecting one branch; they assume no completion or branch
existence. Optional residual absence is retained literally. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

/-- Current guards stay outside the common reset. Inverting the canonical
presentation evaluates its actual pending body at the reset valuation. -/
theorem canonical_body_facts
    {R : ClockResetSet Clock} {G : List (Section3.Guard Clock)}
    {L : List (Local Clock Var)} {Ns : List (MixedJ Clock Var)} {J C Body : MixedJ Clock Var}
    (hshape : canonicalSyntax R G L Ns = some C) (hJC : StructuralEq J C)
    (hBody : foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next) = some Body)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hReady : J.Ready)
    (hHolds : Section3.Judgement.holds σ P α k J)
    (hInv : J.EvaluatedInvariant σ P α k) (hStable : J.UnderlyingStable σ P) :
    Body.Ready ∧ Section3.Judgement.holds σ P (R.apply α) k Body ∧
      Body.EvaluatedInvariant σ P (R.apply α) k ∧ Body.UnderlyingStable σ P := by
  have hr := hJC.ready_iff.1 hReady
  have hs := (hJC.holds_iff σ P α k).1 hHolds
  have hi := (hJC.invariant_iff σ P α k).1 hInv
  have ht := (hJC.stable_iff σ P).1 hStable
  cases hg : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
  | none =>
    have he : .reset R Body = C := by
      simpa only [canonicalSyntax,hg,hBody,Option.map_some,optionalConj,Option.some.injEq] using hshape
    subst C
    exact ⟨hr,hs,hi,ht⟩
  | some Guards =>
    have he : .conj Guards (.reset R Body) = C := by
      simpa only [canonicalSyntax,hg,hBody,Option.map_some,optionalConj,Option.some.injEq] using hshape
    subst C
    exact ⟨hr.2,hs.2,hi.2,fun φ hφ => ht φ (Or.inr hφ)⟩

/-- Extract the exact selected source and every present residual from a proved
structural exposure. The empty residual branch requires no invented judgement. -/
theorem exposed_predicate_facts
    {Body : MixedJ Clock Var} {p : Predicate Clock Var} {residual : Option (MixedJ Clock Var)}
    (hExpose : StructuralEq Body (prependCurrent (.predicate p) residual))
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (β : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hReady : Body.Ready)
    (hHolds : Section3.Judgement.holds σ P β k Body)
    (hInv : Body.EvaluatedInvariant σ P β k) (hStable : Body.UnderlyingStable σ P) :
    p.Ready ∧ Section3.Judgement.holds σ P β k (.predicate p) ∧
      (∀ hk : k.val < P.size, p.Invariant σ P β k hk) ∧ σ.StablePartition p.formula P ∧
      ∀ Γ, residual = some Γ → Γ.Ready ∧ Section3.Judgement.holds σ P β k Γ ∧
        Γ.EvaluatedInvariant σ P β k ∧ Γ.UnderlyingStable σ P := by
  have hr := hExpose.ready_iff.1 hReady
  have hs := (hExpose.holds_iff σ P β k).1 hHolds
  have hi := (hExpose.invariant_iff σ P β k).1 hInv
  have ht := (hExpose.stable_iff σ P).1 hStable
  cases residual with
  | none =>
    refine ⟨hr,hs,hi,?_,?_⟩
    · exact ht p.formula rfl
    · intro Γ hΓ
      cases hΓ
  | some Γ =>
    refine ⟨hr.1,hs.1,hi.1,?_,?_⟩
    · exact ht p.formula (Or.inl rfl)
    · intro Δ hΔ
      have he : Γ = Δ := Option.some.inj hΔ
      subst Δ
      exact ⟨hr.2,hs.2,hi.2,fun φ hφ => ht φ (Or.inr hφ)⟩

end STLTableau.Section4.Finiteness
