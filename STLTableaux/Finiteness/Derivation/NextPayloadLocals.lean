import STLTableaux.Finiteness.Derivation.NextResetProvenance

/-! Normalization retains the local judgements of each next judgement in
the combined next state, including markers and the terminal constant. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

def currentLocalSet : MixedJ Clock Var → Set (Local Clock Var)
  | .terminal => {.terminal}
  | .marker m => {.marker m}
  | .predicate p => {.predicate p}
  | .conj J K => currentLocalSet J ∪ currentLocalSet K
  | .reset _ J => currentLocalSet J
  | _ => ∅

theorem SafeNormalization.current_locals_eq {J : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : SafeNormalization J F) :
    F.current.locals = currentLocalSet J := by
  induction h with
  | terminal | clock | marker | predicate => rfl
  | conj h g hc ih ig => exact congrArg₂ Set.union ih ig
  | reset R h hd ih => exact ih
  | next h hn ih => rfl

private def nextLocalSet : MixedJ Clock Var → Set (Local Clock Var)
  | .next K => currentLocalSet K
  | .conj J K => nextLocalSet J ∪ nextLocalSet K
  | .reset _ J => nextLocalSet J
  | _ => ∅

private def normalizedNextLocals (F : Section3.TransitionForm Clock Var) : Set (Local Clock Var) :=
  match F.nextPart with | none => ∅ | some N => N.locals

private theorem normalized_union_locals (F G : Section3.TransitionForm Clock Var) :
    normalizedNextLocals (F.union G) = normalizedNextLocals F ∪ normalizedNextLocals G := by
  cases hf : F.nextPart <;> cases hg : G.nextPart <;>
    simp [normalizedNextLocals,Section3.TransitionForm.union,Section3.TransitionForm.unionNext,
      Section3.StateForm.union,hf,hg]

private theorem safe_next_locals {J : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : SafeNormalization J F) : normalizedNextLocals F = nextLocalSet J := by
  induction h with
  | terminal | clock | marker | predicate => rfl
  | conj h g hc ih ig => exact (normalized_union_locals _ _).trans (congrArg₂ Set.union ih ig)
  | reset R h hd ih => exact ih
  | next h hn ih => exact h.current_locals_eq

private theorem next_local_origin (J : MixedJ Clock Var) (l : Local Clock Var) :
    l ∈ nextLocalSet J ↔ ∃K∈nextPayloads J, l ∈ currentLocalSet K := by
  induction J with
  | terminal | clock | marker | predicate => simp [nextLocalSet,nextPayloads]
  | next K => simp [nextLocalSet,nextPayloads]
  | reset R J ih => exact ih
  | conj J K ih ik =>
      simp only [nextLocalSet,nextPayloads,Set.mem_union,ih,ik]
      constructor
      · rintro (⟨L,hL,hl⟩ | ⟨L,hL,hl⟩)
        · exact ⟨L,Or.inl hL,hl⟩
        · exact ⟨L,Or.inr hL,hl⟩
      · rintro ⟨L,(hL | hL),hl⟩
        · exact Or.inl ⟨L,hL,hl⟩
        · exact Or.inr ⟨L,hL,hl⟩

/-- Exact current-local provenance for a safely normalized next state. -/
theorem SafeNormalization.next_local_iff {J : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var} {N : Section3.StateForm Clock Var}
    (h : SafeNormalization J F) (hn : F.nextPart = some N) (l : Local Clock Var) :
    l∈N.locals ↔ ∃K∈nextPayloads J, l∈currentLocalSet K := by
  have he := safe_next_locals h
  simp only [normalizedNextLocals,hn] at he
  rw [he]
  exact next_local_origin J l

theorem SafeNormalization.next_local_of_payload {J K : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var} {N : Section3.StateForm Clock Var}
    (h : SafeNormalization J F) (hn : F.nextPart = some N) (hK : K∈nextPayloads J)
    {l : Local Clock Var} (hl : l∈currentLocalSet K) : l∈N.locals :=
  (h.next_local_iff hn l).2 ⟨K,hK,hl⟩

/-- A separately normalized literal payload contributes all its actual locals. -/
theorem SafeNormalization.next_local_of_safe_payload {J K : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var} {N M : Section3.StateForm Clock Var}
    (h : SafeNormalization J F) (hn : F.nextPart = some N) (hK : K∈nextPayloads J)
    (hPayload : SafeNormalization K (.ofState M)) {l : Local Clock Var} (hl : l∈M.locals) : l∈N.locals := by
  apply h.next_local_of_payload hn hK
  rw [← hPayload.current_locals_eq]
  exact hl

variable [DecidableEq Clock]

/-- Local inclusion for an actual payload recorded by this same selected tree. -/
theorem SelectedTree.ledger_next_local
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization H F)
    {N : Section3.StateForm Clock Var} (hn : F.nextPart = some N)
    {entry : RawLedgerEntry (Clock := Clock) (Var := Var)} (he : entry∈T.rawLedger)
    {K : MixedJ Clock Var} (hK : K∈nextPayloads entry.body)
    {l : Local Clock Var} (hl : l∈currentLocalSet K) : l∈N.locals :=
  hSafe.next_local_of_payload hn ((T.nextPayloads_iff K).2 (Or.inr ⟨entry,he,hK⟩)) hl

end STLTableau.Section4.Finiteness
