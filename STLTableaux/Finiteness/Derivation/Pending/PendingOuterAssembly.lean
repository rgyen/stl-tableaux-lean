import STLTableaux.Finiteness.Derivation.Pending.PendingGeneralOuterAssembly

/-! Reattach the original outside guard spine after completing its inherited
pending body. Current guards may overlap the body's reset support. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

/-- Outside guards are retained literally and normalized by capture-free
compatibility; no separation from inherited reset names is assumed. -/
theorem assemble_owned_outside_guards
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (A : Set Clock)
    (Body : MixedJ Clock Var)
    (hBody : foldCurrent (owned.locals.map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) = some Body)
    {H E : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (tail : Resolve (.reset R Body) H E)
    (hH : SafeNormalization H F) (hE : SafeNormalization E F.atomicProjection)
    (hEmpty : F.current.guards = ∅) (hReset : Disjoint F.current.resets.clocks A)
    (hPrivate : nextCurrentPrivate F) (hNextH : NextPrivate H) (hNextE : NextPrivate E)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hReady : J.Ready) (hHolds : Judgement.holds σ P α k J)
    (hInv : J.EvaluatedInvariant σ P α k) (hStable : J.UnderlyingStable σ P)
    (hf : F.holds σ P α k) (hif : F.EvaluatedInvariant σ P α k)
    (hsf : F.UnderlyingStable σ P) (hNextJ : NextPrivate J) :
    OrdinaryCompletion J σ P α k A := by
  obtain ⟨Hout,Eout,Fout,hD,hHout,hEout,hfout,hifout,hsfout,hrout,hnH,hnE,hguards,hr,hn,_⟩ :=
    assemble_owned_outside_guards_general owned A Body hBody tail hH hE hReset
      hPrivate hNextH hNextE σ P α k hReady hHolds hInv hStable hf hif hsf hNextJ
  refine ⟨Hout,Eout,Fout,hD,hHout,hEout,hfout,hifout,hsfout,hrout,hnH,hnE,?_,hr,hn⟩
  simpa only [hEmpty,Set.union_empty] using hguards

end STLTableau.Section4.Finiteness
