import STLTableaux.Finiteness.Derivation.Selection.SelectedResetConstants
import STLTableaux.Finiteness.Derivation.NextResetProvenance
import STLTableaux.Finiteness.Derivation.CurrentGuardProjection

/-! Whole-next guard and reset provenance of the same selected tree, including
 guard-only payloads. Only surviving normalized assignments are traced; literal
 overwritten assignments are not asserted to survive normalization. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

private def nextGuards : MixedJ Clock Var → Set (Section3.Guard Clock)
  | .next K => currentGuards K
  | .conj J K => nextGuards J ∪ nextGuards K
  | .reset _ J => nextGuards J
  | _ => ∅

private def normalizedNextGuards (F : Section3.TransitionForm Clock Var) : Set (Section3.Guard Clock) :=
  match F.nextPart with | none => ∅ | some N => N.guards

private theorem next_guards_union (F G : Section3.TransitionForm Clock Var) :
    normalizedNextGuards (F.union G)=normalizedNextGuards F ∪ normalizedNextGuards G := by
  cases hf : F.nextPart <;> cases hg : G.nextPart <;>
    simp [normalizedNextGuards,Section3.TransitionForm.union,Section3.TransitionForm.unionNext,
      Section3.StateForm.union,hf,hg]

private theorem safe_next_guards {J : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : SafeNormalization J F) : normalizedNextGuards F=nextGuards J := by
  induction h with
  | terminal | clock | marker | predicate => rfl
  | conj h g hc ih ig => exact (next_guards_union _ _).trans (congrArg₂ Set.union ih ig)
  | reset R h hd ih => exact ih
  | next h hn ih => exact h.currentGuards_eq

private theorem next_guard_payload (J : MixedJ Clock Var) (g : Section3.Guard Clock) :
    g∈nextGuards J ↔ ∃K∈nextPayloads J,g∈currentGuards K := by
  induction J with
  | terminal | clock | marker | predicate => simp [nextGuards,nextPayloads]
  | next => simp [nextGuards,nextPayloads]
  | reset R J ih => exact ih
  | conj J K ih ik =>
      simp only [nextGuards,nextPayloads,Set.mem_union,ih,ik]
      aesop

private theorem current_guard_literal {J : MixedJ Clock Var} {g : Section3.Guard Clock}
    (h : g∈currentGuards J) : RawGuardAt g.clock g.bound J := by
  induction J with
  | terminal | marker | predicate | next => cases h
  | clock c r a => have he : g=⟨c,r,a⟩ := h; subst g; exact ⟨rfl,rfl⟩
  | reset R J ih => exact ih h
  | conj J K ih ik =>
      rcases h with h | h
      · exact Or.inl (ih h)
      · exact Or.inr (ik h)

private def nextResets : MixedJ Clock Var → ClockResetSet Clock
  | .next K => currentResetMap K
  | .conj J K => (nextResets J).union (nextResets K)
  | .reset _ J => nextResets J
  | _ => ClockResetSet.empty

private def normalizedNextResets (F : Section3.TransitionForm Clock Var) : ClockResetSet Clock :=
  match F.nextPart with | none => ClockResetSet.empty | some N => N.resets

private theorem reset_ext {R S : ClockResetSet Clock} (h : R.value=S.value) : R=S := by
  cases R
  cases S
  cases h
  rfl

private theorem reset_union_empty (R : ClockResetSet Clock) : R=R.union ClockResetSet.empty := by
  apply reset_ext
  funext c
  change R.value c = match R.value c with | some a => some a | none => none
  cases R.value c <;> rfl

private theorem next_resets_union (F G : Section3.TransitionForm Clock Var) :
    normalizedNextResets (F.union G)=(normalizedNextResets F).union (normalizedNextResets G) := by
  cases hf : F.nextPart <;> cases hg : G.nextPart <;>
    simp [normalizedNextResets,Section3.TransitionForm.union,Section3.TransitionForm.unionNext,
      Section3.StateForm.union,hf,hg]
  all_goals first | exact reset_union_empty _ | rfl

private theorem safe_next_resets {J : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : SafeNormalization J F) : normalizedNextResets F=nextResets J := by
  induction h with
  | terminal | clock | marker | predicate => rfl
  | conj h g hc ih ig => exact (next_resets_union _ _).trans (congrArg₂ ClockResetSet.union ih ig)
  | reset R h hd ih => exact ih
  | next h hn ih => exact safe_reset_map h

private theorem next_reset_payload {J : MixedJ Clock Var} {c : Clock} {a : NNReal}
    (h : (nextResets J).value c=some a) :
    ∃K∈nextPayloads J,(currentResetMap K).value c=some a := by
  induction J with
  | terminal | clock | marker | predicate => cases h
  | next K => exact ⟨K,rfl,h⟩
  | reset R J ih => exact ih h
  | conj J K ih ik =>
      cases he : (nextResets J).value c with
      | none =>
          obtain ⟨K,hK,ha⟩ := ik (by simpa only [nextResets,ClockResetSet.union,he] using h)
          exact ⟨K,Or.inr hK,ha⟩
      | some b =>
          have hb : b=a := by simpa only [nextResets,ClockResetSet.union,he,Option.some.injEq] using h
          obtain ⟨K,hK,ha⟩ := ih (hb ▸ he)
          exact ⟨K,Or.inl hK,ha⟩

theorem RawGuardAt.of_payload {J K : MixedJ Clock Var} (hK : K∈nextPayloads J)
    {c a} (h : RawGuardAt c a K) : RawGuardAt c a J := by
  induction J with
  | terminal | clock | marker | predicate => cases hK
  | next L => have he : K=L := hK; subst K; exact h
  | reset R J ih => exact ih hK
  | conj J L ih il =>
      rcases hK with hK | hK
      · exact Or.inl (ih hK)
      · exact Or.inr (il hK)

theorem RawResetAt.of_payload {J K : MixedJ Clock Var} (hK : K∈nextPayloads J)
    {c a} (h : RawResetAt c a K) : RawResetAt c a J := by
  induction J with
  | terminal | clock | marker | predicate => cases hK
  | next L => have he : K=L := hK; subst K; exact h
  | reset R J ih => exact Or.inr (ih hK)
  | conj J L ih il =>
      rcases hK with hK | hK
      · exact Or.inl (ih hK)
      · exact Or.inr (il hK)

theorem SafeNormalization.next_guard_payload_origin
    {J : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : SafeNormalization J F) {N : Section3.StateForm Clock Var}
    (hn : F.nextPart=some N) {g : Section3.Guard Clock} (hg : g∈N.guards) :
    ∃K∈nextPayloads J,RawGuardAt g.clock g.bound K := by
  have hh : g∈nextGuards J := by
    rw [← safe_next_guards h]
    simpa only [normalizedNextGuards,hn] using hg
  obtain ⟨K,hK,hg⟩ := (next_guard_payload J g).1 hh
  exact ⟨K,hK,current_guard_literal hg⟩

theorem SafeNormalization.next_reset_payload_origin
    {J : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : SafeNormalization J F) {N : Section3.StateForm Clock Var}
    (hn : F.nextPart=some N) {c : Clock} {a : NNReal} (ha : N.resets.value c=some a) :
    ∃K∈nextPayloads J,RawResetAt c a K := by
  have hh : (nextResets J).value c=some a := by
    rw [← safe_next_resets h]
    simpa only [normalizedNextResets,hn] using ha
  obtain ⟨K,hK,hv⟩ := next_reset_payload hh
  exact ⟨K,hK,currentResetMap_value_literal hv⟩

variable [DecidableEq Clock]

theorem SelectedTree.normalized_next_guard_provenance
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) (hEmpty : owned.nextInputs=[])
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization H F)
    {N : Section3.StateForm Clock Var} (hn : F.nextPart=some N)
    {g : Section3.Guard Clock} (hg : g∈N.guards) :
    ∃entry∈T.rawLedger,RawGuardAt g.clock g.bound entry.body ∧ g.bound∈branchConstants entry.source := by
  obtain ⟨K,hK,hg⟩ := hSafe.next_guard_payload_origin hn hg
  rcases (T.nextPayloads_iff K).1 hK with hK | ⟨entry,he,hK⟩
  · rw [owned.nextPayloads_eq] at hK
    simp [hEmpty] at hK
  · have hb := hg.of_payload hK
    exact ⟨entry,he,hb,entry.guard_constant hb⟩

theorem SelectedTree.normalized_next_reset_provenance
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) (hEmpty : owned.nextInputs=[])
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization H F)
    {N : Section3.StateForm Clock Var} (hn : F.nextPart=some N)
    {c : Clock} {a : NNReal} (ha : N.resets.value c=some a) :
    ∃entry∈T.rawLedger,RawResetAt c a entry.body ∧ a∈branchConstants entry.source := by
  obtain ⟨K,hK,ha⟩ := hSafe.next_reset_payload_origin hn ha
  rcases (T.nextPayloads_iff K).1 hK with hK | ⟨entry,he,hK⟩
  · rw [owned.nextPayloads_eq] at hK
    simp [hEmpty] at hK
  · have hb := ha.of_payload hK
    exact ⟨entry,he,hb,entry.reset_constant hb⟩

end STLTableau.Section4.Finiteness
