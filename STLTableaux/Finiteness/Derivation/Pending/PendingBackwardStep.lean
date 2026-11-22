import STLTableaux.Finiteness.Derivation.Pending.PendingStep
import STLTableaux.Finiteness.Derivation.RetainedSourceNormalization

/-! Backward assembly of an actual recursively resolved ordinary child.
The inherited frame is retained once, around the completed inner derivation. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

/-- Copying only the residual active assignments gives the exact input scope
needed by expandCtx, while its completed output remains under the old frame. -/
theorem assemble_inherited_ordinary
    (R : ClockResetSet Clock) (remaining : List (Local Clock Var))
    {p : Predicate Clock Var} {B Γ H E : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var}
    (raw : RawBranch p B) (hp : ¬ p.IsAtomic)
    (fresh : FreshFor p B (.reset (copyActiveResets R remaining) Γ))
    (hdSource : Disjoint (copyActiveResets R remaining).clocks
      (Section3.Judgement.freeClocks (.predicate p)))
    (tail : Resolve (.conj B (.reset (copyActiveResets R remaining) Γ)) H E)
    (hH : SafeNormalization H F) (hE : SafeNormalization E F.atomicProjection)
    (hdRetain : Disjoint F.current.resets.clocks
      (Section3.Judgement.freeClocks (.predicate p)))
    (hdFullGuard : Disjoint R.clocks (retainedSource p F).current.guardClocks)
    (hdErasedGuard : Disjoint R.clocks F.atomicProjection.current.guardClocks) :
    Nonempty (Resolve (.reset R (.conj (.predicate p) Γ))
      (.reset R (.conj (.predicate p) H)) (.reset R E)) ∧
    SafeNormalization (.reset R (.conj (.predicate p) H)) ((retainedSource p F).underReset R) ∧
    SafeNormalization (.reset R E) ((retainedSource p F).underReset R).atomicProjection := by
  have D : Resolve (.conj (.predicate p) (.reset (copyActiveResets R remaining) Γ))
      (.conj (.predicate p) H) E := .expandCtx raw hp fresh tail
  refine ⟨⟨.structural (copied_source_exposure R remaining p Γ hdSource) (.reset R D)⟩,
    .reset R (hH.retain_source p hdRetain) hdFullGuard,?_⟩
  rw [DerivationNormalization.projection_underReset,retainedSource_projection p hp]
  exact .reset R hE hdErasedGuard

end STLTableau.Section4.Finiteness
