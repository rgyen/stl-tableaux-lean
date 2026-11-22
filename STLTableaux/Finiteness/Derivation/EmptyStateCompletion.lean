import STLTableaux.Finiteness.Derivation.NextInputNormalization
import STLTableaux.Finiteness.Derivation.Pending.PendingCompletionBase
import STLTableaux.Finiteness.Derivation.DerivationRelation

/-! A safely presented state with no locals needs no pending ownership:
its actual raw input has zero current potential and closes to the same state. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

theorem SafeNormalization.current_predicate_mem {J : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : SafeNormalization J F) (p : Predicate Clock Var) :
    Local.predicate p ∈ F.current.locals ↔ p ∈ J.currentPredicates := by
  induction h with
  | terminal => simp [Section3.TransitionForm.ofState,Section3.StateForm.ofLocal,Section3.Judgement.currentPredicates]
  | clock => simp [Section3.TransitionForm.ofState,Section3.StateForm.ofGuard,Section3.Judgement.currentPredicates]
  | marker => simp [Section3.TransitionForm.ofState,Section3.StateForm.ofLocal,Section3.Judgement.currentPredicates]
  | predicate q => simp [Section3.TransitionForm.ofState,Section3.StateForm.ofLocal,Section3.Judgement.currentPredicates]
  | conj h g hc ih ig => exact or_congr ih ig
  | reset R h hd ih => exact ih
  | next h hn ih => simp [Section3.TransitionForm.ofNextState,Section3.StateForm.empty,Section3.Judgement.currentPredicates]

theorem SafeNormalization.weight_zero_of_locals_empty {J : MixedJ Clock Var}
    {N : Section3.StateForm Clock Var} (h : SafeNormalization J (.ofState N)) (he : N.locals = ∅) :
    pendingWeight J = 0 := by
  apply pendingWeight_zero_of_no_current
  intro p hp
  have hm := (h.current_predicate_mem p).2 hp
  change Local.predicate p ∈ N.locals at hm
  rw [he] at hm
  exact hm

theorem Derives.empty_locals_terminal [DecidableEq Clock] {J : MixedJ Clock Var}
    {N : Section3.StateForm Clock Var} (h : SafeNormalization J (.ofState N)) (he : N.locals = ∅) :
    Derives N (.ofState N) := by
  have hz := h.weight_zero_of_locals_empty he
  exact .resolved (PendingCompletionBase.resolve_zero J hz) h h
    (PendingCompletionBase.erased_safe J hz h)

/-- In particular the actual next-input certificate suffices for the empty
case; neither guards nor unused reset assignments are discarded. -/
theorem Derives.empty_next_terminal [DecidableEq Clock] {J : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : SafeNormalization J F)
    {N : Section3.StateForm Clock Var} (hn : F.nextPart = some N) (he : N.locals = ∅) :
    Derives N (.ofState N) := by
  obtain ⟨K,hK⟩ := h.next_input hn
  exact .empty_locals_terminal hK he

end STLTableau.Section4.Finiteness
