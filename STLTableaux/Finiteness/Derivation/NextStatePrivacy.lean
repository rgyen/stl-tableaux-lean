import STLTableaux.Finiteness.Derivation.CanonicalProjections

/-! Distinct predicates of the normalized next state have disjoint clock
supports when these supports are disjoint within and between the next
judgements. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

def nextCurrentPrivate (F : Section3.TransitionForm Clock Var) : Prop :=
  ∀ N, F.nextPart = some N → ∀ p q,
    Local.predicate p ∈ N.locals → Local.predicate q ∈ N.locals → p ≠ q →
    Disjoint (syntaxClocks (.predicate p)) (syntaxClocks (.predicate q))

private def nextPredicates : MixedJ Clock Var → Set (Predicate Clock Var)
  | .next J => J.currentPredicates
  | .conj J K => nextPredicates J ∪ nextPredicates K
  | .reset _ J => nextPredicates J
  | _ => ∅

private def normalizedNextPredicates (F : Section3.TransitionForm Clock Var) : Set (Predicate Clock Var) :=
  match F.nextPart with
  | none => ∅
  | some N => {p | Local.predicate p ∈ N.locals}

private theorem current_predicates_safe {J : MixedJ Clock Var}
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

private theorem next_predicates_union (F G : Section3.TransitionForm Clock Var) :
    normalizedNextPredicates (F.union G) = normalizedNextPredicates F ∪ normalizedNextPredicates G := by
  cases hf : F.nextPart <;> cases hg : G.nextPart <;>
    ext p <;> simp [normalizedNextPredicates,Section3.TransitionForm.union,Section3.TransitionForm.unionNext,
      Section3.StateForm.union,hf,hg]

private theorem next_predicates_safe {J : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : SafeNormalization J F) :
    normalizedNextPredicates F = nextPredicates J := by
  induction h with
  | terminal => rfl
  | clock => rfl
  | marker => rfl
  | predicate => rfl
  | conj h g hc ih ig => exact (next_predicates_union _ _).trans (congrArg₂ Set.union ih ig)
  | reset R h hd ih => exact ih
  | @next J F h hn ih =>
      ext p
      exact current_predicates_safe h p

private theorem current_predicate_support {J : MixedJ Clock Var} {p : Predicate Clock Var}
    (hp : p ∈ J.currentPredicates) : syntaxClocks (.predicate p) ⊆ syntaxClocks J := by
  induction J with
  | terminal | clock | marker | next => cases hp
  | predicate q =>
      have he : p = q := hp
      subst p
      exact Set.Subset.rfl
  | conj J K ih ik =>
      rcases hp with hp | hp
      · exact (ih hp).trans Set.subset_union_left
      · exact (ik hp).trans Set.subset_union_right
  | reset R J ih => exact (ih hp).trans Set.subset_union_right

open CanonicalObservation

private theorem canonical_next_predicates
    {R : ClockResetSet Clock} {G : List (Section3.Guard Clock)}
    {L : List (Local Clock Var)} {Ns : List (MixedJ Clock Var)} {C : MixedJ Clock Var}
    (h : canonicalSyntax R G L Ns = some C) (p : Predicate Clock Var) :
    p ∈ nextPredicates C ↔ ∃ K ∈ Ns, p ∈ K.currentPredicates := by
  rw [canonical_observe nextPredicates (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) h,
    observed_mem]
  constructor
  · rintro ⟨J,hJ,hp⟩
    rcases List.mem_append.mp hJ with hL | hN
    · obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hL
      cases l <;> exact False.elim hp
    · obtain ⟨K,hK,rfl⟩ := List.mem_map.mp hN
      exact ⟨K,hK,hp⟩
  · rintro ⟨K,hK,hp⟩
    exact ⟨.next K,List.mem_append_right _ (List.mem_map.mpr ⟨K,hK,rfl⟩),hp⟩

/-- Each normalized next predicate belongs to an actual canonical payload. -/
theorem canonical_next_predicate_origin
    {R : ClockResetSet Clock} {G : List (Section3.Guard Clock)}
    {L : List (Local Clock Var)} {Ns : List (MixedJ Clock Var)} {C : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var} {N : Section3.StateForm Clock Var}
    (hshape : canonicalSyntax R G L Ns = some C) (hsafe : SafeNormalization C F)
    (hn : F.nextPart = some N) (p : Predicate Clock Var) :
    Local.predicate p ∈ N.locals ↔ ∃ K ∈ Ns, p ∈ K.currentPredicates := by
  have he := next_predicates_safe hsafe
  have hp := canonical_next_predicates hshape p
  rw [← he] at hp
  simpa only [normalizedNextPredicates,hn,Set.mem_setOf_eq] using hp

private theorem pairwise_disjoint_members {Ns : List (MixedJ Clock Var)}
    (h : Ns.Pairwise (fun J K => Disjoint (syntaxClocks J) (syntaxClocks K)))
    {J K : MixedJ Clock Var} (hJ : J ∈ Ns) (hK : K ∈ Ns) (hne : J ≠ K) :
    Disjoint (syntaxClocks J) (syntaxClocks K) := by
  induction Ns with
  | nil => cases hJ
  | cons A As ih =>
      obtain ⟨ha,ht⟩ := List.pairwise_cons.1 h
      rcases List.mem_cons.1 hJ with rfl | hJtail
      · rcases List.mem_cons.1 hK with rfl | hKtail
        · exact False.elim (hne rfl)
        · exact ha K hKtail
      · rcases List.mem_cons.1 hK with rfl | hKtail
        · exact (ha J hJtail).symm
        · exact ih ht hJtail hKtail

/-- Internal payload privacy plus pairwise payload separation gives privacy
of the actual combined normalized next state. -/
theorem canonical_next_state_private
    {R : ClockResetSet Clock} {G : List (Section3.Guard Clock)}
    {L : List (Local Clock Var)} {Ns : List (MixedJ Clock Var)} {C : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var}
    (hshape : canonicalSyntax R G L Ns = some C) (hsafe : SafeNormalization C F)
    (hpw : Ns.Pairwise (fun J K => Disjoint (syntaxClocks J) (syntaxClocks K)))
    (hprivate : ∀ K ∈ Ns, privateRawCurrent K) : nextCurrentPrivate F := by
  intro N hn p q hp hq hpq
  obtain ⟨J,hJ,hp⟩ := (canonical_next_predicate_origin hshape hsafe hn p).1 hp
  obtain ⟨K,hK,hq⟩ := (canonical_next_predicate_origin hshape hsafe hn q).1 hq
  by_cases he : J = K
  · subst K
    exact hprivate J hJ p hp q hq hpq
  · exact (pairwise_disjoint_members hpw hJ hK he).mono
      (current_predicate_support hp) (current_predicate_support hq)

end STLTableau.Section4.Finiteness
