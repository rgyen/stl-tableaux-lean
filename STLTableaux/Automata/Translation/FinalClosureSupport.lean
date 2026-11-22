import STLTableaux.Automata.Translation.LocalClosureGraph
import STLTableaux.Finiteness.Derivation.EmptyStateCompletion

namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

/-- No predicate to expand and no next judgement to preserve. -/
private def Inert : MixedJ Clock Var → Prop
  | .predicate _ | .next _ => False
  | .conj J K => Inert J ∧ Inert K
  | .reset _ J => Inert J
  | _ => True

private theorem inert_structural {J K : MixedJ Clock Var} (h : ACIdem J K) :
    Inert J ↔ Inert K := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | assoc => exact and_assoc
  | comm => exact and_comm
  | idem => exact and_self_iff
  | conj _ _ ih ik => exact and_congr ih ik
  | reset _ _ ih => exact ih
  | resetDistrib | resetUnused | resetNested => rfl

private theorem resolve_inert [DecidableEq Clock] {J H A : MixedJ Clock Var}
    (d : Resolve J H A) : Inert J → Inert H := by
  induction d with
  | leaf => exact id
  | conj _ _ ih ik => exact fun h => ⟨ih h.1,ik h.2⟩
  | reset _ _ ih | unusedReset _ _ _ _ _ ih => exact ih
  | structural hs _ ih => exact fun h => ih ((inert_structural hs).mp h)
  | expandCtx => exact fun h => h.1.elim
  | expandSolo => exact False.elim
  | boundaryOptional => exact fun h => h.1.elim
  | boundaryRequired => exact fun h => h.1.1.elim

private theorem inert_normal {J : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : SafeNormalization J F) :
    Inert J ↔ F.nextPart = none ∧ ∀ p, Local.predicate p ∉ F.current.locals := by
  induction h with
  | terminal | marker | clock | predicate =>
    simp [Inert,Section3.TransitionForm.ofState,Section3.StateForm.ofLocal,
      Section3.StateForm.ofGuard]
  | reset _ _ _ ih => exact ih
  | next => simp [Inert,Section3.TransitionForm.ofNextState]
  | @conj J K F G _ _ _ ih ik =>
    change (Inert J ∧ Inert K) ↔ _
    rw [ih,ik]
    cases hf : F.nextPart <;> cases hg : G.nextPart <;>
      simp [Section3.TransitionForm.union,Section3.TransitionForm.unionNext,
        Section3.StateForm.union,hf,hg]
    all_goals grind

/-- For a generator with no interval predicates, `Derives` yields a
transition form with an empty next part. -/
theorem no_next_from_predicate_free [DecidableEq Clock]
    {N : Section3.StateForm Clock Var} {F : Section3.TransitionForm Clock Var}
    (hd : Derives N F) (hn : ∀ p, Local.predicate p ∉ N.locals) : F.nextPart = none := by
  cases hd with
  | original hc _ =>
    have hclosed : ConcreteContextual.catalogue.IsClosed (.ofState N) :=
      fun p hp => (hn p hp).elim
    have hsub := hc.minimal (.ofState N) (Section3.SyntacticallySubsumed.refl _) hclosed hc.extension
    cases he : F.nextPart with
    | none => rfl
    | some M =>
      obtain ⟨K,hK,_⟩ := hsub.next M he
      cases hK
  | resolved d hi hf _ =>
    exact ((inert_normal hf).mp (resolve_inert d ((inert_normal hi).mpr ⟨rfl,hn⟩))).1

variable [DecidableEq Clock] [Infinite Clock]
variable (X : Set Var) (root : Formula.NormalizedInput Var)
local notation "U" => (localClosureGraph (Clock := Clock) X root)

theorem reached_terminal_state_form {s t : Section3.TransitionForm Clock Var} {l : EdgeLabel Clock}
    (he : (s,l,t) ∈ (U).edges) (ht : Local.terminal ∈ (U).label t) : t.nextPart = none := by
  obtain ⟨N,_,hd,_,hn⟩ := terminal_entry_generator X root he ht
  apply no_next_from_predicate_free hd
  intro p hp
  rcases hn _ hp with h | h <;> cases h

/-- The graph retains the empty continuation; it is the only possible
outgoing target of a reached terminal visit. -/
theorem terminal_successor_empty {s t u : Section3.TransitionForm Clock Var}
    {l m : EdgeLabel Clock} (he : (s,l,t) ∈ (U).edges) (ht : Local.terminal ∈ (U).label t)
    (he' : (t,m,u) ∈ (U).edges) : m = emptyIncoming ∧ u = emptyMode := by
  rcases he'.1 with old | added
  · obtain ⟨_,_,N,hn,_,_⟩ := old.1
    have hnone := reached_terminal_state_form X root he ht
    change t.nextPart = some N at hn
    rw [hnone] at hn
    cases hn
  · exact ⟨added.2.2.1,added.2.2.2⟩

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``no_next_from_predicate_free] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do throwError "{name} uses unexpected axiom {ax}"

end STLTableau.Section4.Finiteness
