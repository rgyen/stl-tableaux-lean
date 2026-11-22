import STLTableaux.Finiteness.Derivation.Pending.PendingOwnership

/-! Current reset support for safe canonical pending inputs. Unlike current
guards, reset support is not invariant under unused-reset removal. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

def currentResetClocks : MixedJ Clock Var → Set Clock
  | .reset R J => currentResetClocks J ∪ R.clocks
  | .conj J K => currentResetClocks J ∪ currentResetClocks K
  | _ => ∅

theorem SafeNormalization.currentResetClocks_eq {J : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : SafeNormalization J F) :
    F.current.resets.clocks = currentResetClocks J := by
  induction h with
  | terminal => exact empty_reset_clocks
  | clock => exact empty_reset_clocks
  | marker => exact empty_reset_clocks
  | predicate => exact empty_reset_clocks
  | @conj J K F G h g hc ih ig =>
    change (F.current.resets.union G.current.resets).clocks = _
    rw [ClockResetSet.clocks_union,ih,ig]
    rfl
  | @reset R J F h hd ih =>
    change (F.current.resets.union R).clocks = _
    rw [ClockResetSet.clocks_union,ih]
    rfl
  | next => exact empty_reset_clocks

private def optionResets : Option (MixedJ Clock Var) → Set Clock
  | none => ∅
  | some J => currentResetClocks J

private theorem optional_resets (J K : Option (MixedJ Clock Var)) :
    optionResets (optionalConj J K) = optionResets J ∪ optionResets K := by
  cases J <;> cases K <;> simp [optionalConj,optionResets,currentResetClocks]

private theorem fold_resets (Js : List (MixedJ Clock Var)) (c : Clock) :
    c ∈ optionResets (foldCurrent Js) ↔ ∃ J ∈ Js, c ∈ currentResetClocks J := by
  induction Js with
  | nil => simp [foldCurrent,optionResets]
  | cons J Js ih =>
    change c ∈ optionResets (optionalConj (some J) (foldCurrent Js)) ↔ _
    rw [optional_resets,Set.mem_union,ih]
    simp [optionResets]

/-- Only the common inherited map can contribute a CURRENT reset to a
canonical input; next-payload reset clocks remain next-scoped. -/
theorem canonical_currentResetClocks_subset
    {R : ClockResetSet Clock} {G : List (Section3.Guard Clock)}
    {L : List (Local Clock Var)} {Ns : List (MixedJ Clock Var)} {C : MixedJ Clock Var}
    (h : canonicalSyntax R G L Ns = some C) : currentResetClocks C ⊆ R.clocks := by
  have hz : optionResets (foldCurrent (L.map Local.toJudgement ++
      Ns.map Section3.Judgement.next)) = ∅ := by
    ext c
    rw [fold_resets]
    simp only [List.mem_append,List.mem_map]
    constructor
    · rintro ⟨J,(⟨l,hl,rfl⟩ | ⟨N,hN,rfl⟩),hc⟩
      · cases l <;> exact hc
      · exact hc
    · exact False.elim
  have hg : optionResets (foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var)))) = ∅ := by
    ext c
    rw [fold_resets]
    constructor
    · rintro ⟨J,hJ,hc⟩
      obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hJ
      cases g
      exact hc
    · exact False.elim
  have he := congrArg optionResets h
  change optionResets (optionalConj
    (foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))))
    ((foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next)).map
      (Section3.Judgement.reset R))) = currentResetClocks C at he
  rw [optional_resets,hg,Set.empty_union] at he
  rw [← he]
  cases hb : foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next) with
  | none => exact Set.empty_subset _
  | some Body =>
    have hBody : currentResetClocks Body = ∅ := by simpa only [hb,optionResets] using hz
    change currentResetClocks Body ∪ R.clocks ⊆ R.clocks
    rw [hBody,Set.empty_union]

 theorem canonical_safe_reset_protection
    {R : ClockResetSet Clock} {G : List (Section3.Guard Clock)}
    {L : List (Local Clock Var)} {Ns : List (MixedJ Clock Var)} {C : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var} {A : Set Clock}
    (hshape : canonicalSyntax R G L Ns = some C) (hsafe : SafeNormalization C F)
    (hR : Disjoint R.clocks A) : Disjoint F.current.resets.clocks A := by
  rw [hsafe.currentResetClocks_eq]
  exact hR.mono_left (canonical_currentResetClocks_subset hshape)

end STLTableau.Section4.Finiteness
