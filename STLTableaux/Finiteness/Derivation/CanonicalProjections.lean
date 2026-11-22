import STLTableaux.Finiteness.Derivation.Pending.PendingOwnership
import STLTableaux.Finiteness.Derivation.Branches.RawBranchPrivacy

/-! Projections of actual canonical input spines and inversion of their safe
normalization. No encoding of arbitrary normalized states is assumed. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

 theorem ACIdem.currentPredicates_eq {J K : MixedJ Clock Var} (h : StructuralEq J K) :
    J.currentPredicates = K.currentPredicates := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig
  | assoc => exact Set.union_assoc _ _ _
  | comm => exact Set.union_comm _ _
  | idem => exact Set.union_self _
  | conj h g ih ig => exact congrArg₂ Set.union ih ig
  | reset R h ih => exact ih
  | resetDistrib R J K => rfl
  | resetUnused R J hd => rfl
  | resetNested R S J => rfl

namespace CanonicalObservation

def observedOption {α : Type*} (f : MixedJ Clock Var → Set α) : Option (MixedJ Clock Var) → Set α
  | none => ∅
  | some J => f J
def observedList {α : Type*} (f : MixedJ Clock Var → Set α) : List (MixedJ Clock Var) → Set α
  | [] => ∅
  | J :: Js => f J ∪ observedList f Js

theorem observed_mem {α : Type*} (f : MixedJ Clock Var → Set α)
    (Js : List (MixedJ Clock Var)) (a : α) :
    a ∈ observedList f Js ↔ ∃ J ∈ Js, a ∈ f J := by
  induction Js with
  | nil => simp [observedList]
  | cons J Js ih => simp [observedList,ih]

theorem fold_observe {α : Type*} (f : MixedJ Clock Var → Set α)
    (hc : ∀ J K, f (.conj J K) = f J ∪ f K) (Js : List (MixedJ Clock Var)) :
    observedOption f (foldCurrent Js) = observedList f Js := by
  induction Js with
  | nil => rfl
  | cons J Js ih =>
    cases ht : foldCurrent Js with
    | none =>
      have he : observedList f Js = ∅ := by simpa only [ht,observedOption] using ih.symm
      simp only [foldCurrent,ht,optionalConj,observedOption,observedList,he,Set.union_empty]
    | some K =>
      have he : f K = observedList f Js := by simpa only [ht,observedOption] using ih
      simp only [foldCurrent,ht,optionalConj,observedOption,observedList,hc,he]

theorem optional_observe {α : Type*} (f : MixedJ Clock Var → Set α)
    (hc : ∀ J K, f (.conj J K) = f J ∪ f K) (J K : Option (MixedJ Clock Var)) :
    observedOption f (optionalConj J K) = observedOption f J ∪ observedOption f K := by
  cases J <;> cases K <;> simp [optionalConj,observedOption,hc]

theorem reset_observe {α : Type*} (f : MixedJ Clock Var → Set α)
    (hr : ∀ R J, f (.reset R J) = f J) (R : ClockResetSet Clock) (J : Option (MixedJ Clock Var)) :
    observedOption f (J.map (.reset R)) = observedOption f J := by
  cases J <;> simp [observedOption,hr]

theorem canonical_observe {α : Type*} (f : MixedJ Clock Var → Set α)
    (hc : ∀ J K, f (.conj J K) = f J ∪ f K)
    (hr : ∀ R J, f (.reset R J) = f J)
    (hg : ∀ g : Section3.Guard Clock, f g.toJudgement = ∅)
    {R : ClockResetSet Clock} {G : List (Section3.Guard Clock)}
    {L : List (Local Clock Var)} {Ns : List (MixedJ Clock Var)} {C : MixedJ Clock Var}
    (h : canonicalSyntax R G L Ns = some C) :
    f C = observedList f (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next) := by
  have hguards : observedList f (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) = ∅ := by
    clear h
    induction G with
    | nil => rfl
    | cons g G ih => simp [observedList,hg,ih]
  have he := congrArg (observedOption f) h
  simp only [canonicalSyntax] at he
  rw [optional_observe f hc,reset_observe f hr,fold_observe f hc,fold_observe f hc,
    hguards,Set.empty_union] at he
  exact he.symm

end CanonicalObservation

open CanonicalObservation

private theorem local_predicate (l : Local Clock Var) (p : Predicate Clock Var) :
    p ∈ l.toJudgement.currentPredicates ↔ l = .predicate p := by
  cases l <;> simp [Local.toJudgement,Section3.Judgement.currentPredicates,eq_comm]

 theorem canonical_currentPredicates_iff
    {R : ClockResetSet Clock} {G : List (Section3.Guard Clock)}
    {L : List (Local Clock Var)} {Ns : List (MixedJ Clock Var)} {C : MixedJ Clock Var}
    (h : canonicalSyntax R G L Ns = some C) (p : Predicate Clock Var) :
    p ∈ C.currentPredicates ↔ Local.predicate p ∈ L := by
  rw [canonical_observe Section3.Judgement.currentPredicates (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) h]
  rw [observed_mem]
  constructor
  · rintro ⟨J,hJ,hp⟩
    rcases List.mem_append.mp hJ with hL | hN
    · obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hL
      have he := (local_predicate l p).1 hp
      subst l
      exact hl
    · obtain ⟨K,_,rfl⟩ := List.mem_map.mp hN
      cases hp
  · intro hp
    exact ⟨.predicate p,List.mem_append_left _ (List.mem_map.mpr ⟨.predicate p,hp,rfl⟩),rfl⟩

private theorem local_next_support (l : Local Clock Var) : nextSyntaxClocks l.toJudgement = ∅ := by
  cases l <;> rfl

 theorem canonical_nextSyntaxClocks
    {R : ClockResetSet Clock} {G : List (Section3.Guard Clock)}
    {L : List (Local Clock Var)} {Ns : List (MixedJ Clock Var)} {C : MixedJ Clock Var}
    (h : canonicalSyntax R G L Ns = some C) :
    nextSyntaxClocks C = ⋃ K ∈ Ns, syntaxClocks K := by
  rw [canonical_observe nextSyntaxClocks (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) h]
  ext c
  rw [observed_mem]
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨J,hJ,hc⟩
    rcases List.mem_append.mp hJ with hL | hN
    · obtain ⟨l,_,rfl⟩ := List.mem_map.mp hL
      rw [local_next_support] at hc
      exact False.elim hc
    · obtain ⟨K,hK,rfl⟩ := List.mem_map.mp hN
      exact ⟨K,hK,hc⟩
  · rintro ⟨K,hK,hc⟩
    exact ⟨.next K,List.mem_append_right _ (List.mem_map.mpr ⟨K,hK,rfl⟩),hc⟩

/-- A folded conjunction contains the clocks occurring in its members. -/
theorem mem_syntaxClocks_foldCurrent_iff {Js : List (MixedJ Clock Var)} {J : MixedJ Clock Var}
    (hf : foldCurrent Js = some J) (c : Clock) :
    c ∈ syntaxClocks J ↔ ∃ K ∈ Js, c ∈ syntaxClocks K := by
  have he := fold_observe syntaxClocks (fun _ _ => rfl) Js
  rw [hf] at he
  change syntaxClocks J = observedList syntaxClocks Js at he
  rw [he]
  exact observed_mem syntaxClocks Js c

theorem syntaxClocks_foldCurrent_subset {Js : List (MixedJ Clock Var)} {J : MixedJ Clock Var}
    {W : Set Clock} (hf : foldCurrent Js = some J)
    (h : ∀ K ∈ Js, syntaxClocks K ⊆ W) : syntaxClocks J ⊆ W := by
  intro c hc
  obtain ⟨K, hK, hc⟩ := (mem_syntaxClocks_foldCurrent_iff hf c).1 hc
  exact h K hK hc

private theorem canonical_body_support
    {R : ClockResetSet Clock} {G : List (Section3.Guard Clock)}
    {L : List (Local Clock Var)} {Ns : List (MixedJ Clock Var)} {C K : MixedJ Clock Var}
    (h : canonicalSyntax R G L Ns = some C)
    (hm : K ∈ L.map Local.toJudgement ++ Ns.map Section3.Judgement.next) :
    syntaxClocks K ⊆ syntaxClocks C := by
  cases hb : foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next) with
  | none =>
    have he := (foldCurrent_none_iff _).1 hb
    rw [he] at hm
    cases hm
  | some B =>
    have hs : syntaxClocks K ⊆ syntaxClocks B :=
      fun c hc => (mem_syntaxClocks_foldCurrent_iff hb c).2 ⟨K, hm, hc⟩
    cases hg : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
    | none =>
      have he : .reset R B = C := by simpa only [canonicalSyntax,hg,hb,Option.map_some,optionalConj,Option.some.injEq] using h
      subst C
      exact fun c hc => Or.inr (hs hc)
    | some A =>
      have he : .conj A (.reset R B) = C := by simpa only [canonicalSyntax,hg,hb,Option.map_some,optionalConj,Option.some.injEq] using h
      subst C
      exact fun c hc => Or.inr (Or.inr (hs hc))

 theorem canonical_local_support
    {R : ClockResetSet Clock} {G : List (Section3.Guard Clock)}
    {L : List (Local Clock Var)} {Ns : List (MixedJ Clock Var)} {C : MixedJ Clock Var}
    (h : canonicalSyntax R G L Ns = some C) {l : Local Clock Var} (hl : l ∈ L) :
    syntaxClocks l.toJudgement ⊆ syntaxClocks C :=
  canonical_body_support h (List.mem_append_left _ (List.mem_map.mpr ⟨l,hl,rfl⟩))

 theorem canonical_payload_support
    {R : ClockResetSet Clock} {G : List (Section3.Guard Clock)}
    {L : List (Local Clock Var)} {Ns : List (MixedJ Clock Var)} {C : MixedJ Clock Var}
    (h : canonicalSyntax R G L Ns = some C) {K : MixedJ Clock Var} (hK : K ∈ Ns) :
    syntaxClocks K ⊆ syntaxClocks C :=
  canonical_body_support (K := .next K) h (List.mem_append_right _ (List.mem_map.mpr ⟨K,hK,rfl⟩))

private theorem fold_safe_member {Js : List (MixedJ Clock Var)} {J K : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var} (hf : foldCurrent Js = some J)
    (hs : SafeNormalization J F) (hm : K ∈ Js) : ∃ G, SafeNormalization K G := by
  induction Js generalizing J F with
  | nil => cases hm
  | cons A As ih =>
    cases ht : foldCurrent As with
    | none =>
      have he := (foldCurrent_none_iff As).1 ht
      subst As
      have he : A = J := by simpa only [foldCurrent,optionalConj,Option.some.injEq] using hf
      subst J
      have he : K = A := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hm
      subst K
      exact ⟨F,hs⟩
    | some B =>
      have he : .conj A B = J := by simpa only [foldCurrent,ht,optionalConj,Option.some.injEq] using hf
      subst J
      cases hs with
      | conj hA hB hc =>
        rcases List.mem_cons.mp hm with he | hm
        · subst K; exact ⟨_,hA⟩
        · exact ih ht hB hm

private theorem canonical_fold_safe
    {R : ClockResetSet Clock} {G : List (Section3.Guard Clock)}
    {L : List (Local Clock Var)} {Ns : List (MixedJ Clock Var)} {C B : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var}
    (h : canonicalSyntax R G L Ns = some C)
    (hb : foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next) = some B)
    (hs : SafeNormalization C F) : ∃ N, SafeNormalization B N := by
  cases hg : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
  | none =>
    have he : .reset R B = C := by simpa only [canonicalSyntax,hg,hb,Option.map_some,optionalConj,Option.some.injEq] using h
    subst C
    cases hs with
    | reset R hB hd => exact ⟨_,hB⟩
  | some A =>
    have he : .conj A (.reset R B) = C := by simpa only [canonicalSyntax,hg,hb,Option.map_some,optionalConj,Option.some.injEq] using h
    subst C
    cases hs with
    | conj hA hB hc =>
      cases hB with
      | reset R hB hd => exact ⟨_,hB⟩

/-- Each actual literal next payload has a safe state-form raw presentation.
This is inversion of its given containing certificate, not arbitrary encoding. -/
theorem canonical_payload_safe
    {R : ClockResetSet Clock} {G : List (Section3.Guard Clock)}
    {L : List (Local Clock Var)} {Ns : List (MixedJ Clock Var)} {C : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var}
    (h : canonicalSyntax R G L Ns = some C) (hs : SafeNormalization C F)
    {K : MixedJ Clock Var} (hK : K ∈ Ns) :
    ∃ N, SafeNormalization K (Section3.TransitionForm.ofState N) := by
  have hm : .next K ∈ L.map Local.toJudgement ++ Ns.map Section3.Judgement.next :=
    List.mem_append_right _ (List.mem_map.mpr ⟨K,hK,rfl⟩)
  cases hb : foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next) with
  | none =>
    have he := (foldCurrent_none_iff _).1 hb
    rw [he] at hm
    cases hm
  | some B =>
    obtain ⟨N,hN⟩ := canonical_fold_safe h hb hs
    obtain ⟨T,hT⟩ := fold_safe_member hb hN hm
    cases hT with
    | @next J F hF hn =>
      have he : F = Section3.TransitionForm.ofState F.current := by
        cases F
        simp_all [Section3.TransitionForm.ofState]
      exact ⟨F.current,he ▸ hF⟩

end STLTableau.Section4.Finiteness
