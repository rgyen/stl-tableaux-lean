import STLTableaux.Closure.Correctness.ClosureSoundness
import STLTableaux.Rules.Finite.Correctness

/-! Canonical faithful transition representations of the finite concrete
catalogue. The structural converter is not asserted correct on arbitrary
judgements: scope preservation is checked on actual rule-generated branches. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}

namespace StateForm

def empty : StateForm Clock Var :=
  ⟨∅, Set.finite_empty, ClockResetSet.empty, ∅, Set.finite_empty⟩

def ofLocal (l : Local Clock Var) : StateForm Clock Var :=
  ⟨∅, Set.finite_empty, ClockResetSet.empty, {l}, Set.finite_singleton l⟩

def ofGuard (g : Guard Clock) : StateForm Clock Var :=
  ⟨{g}, Set.finite_singleton g, ClockResetSet.empty, ∅, Set.finite_empty⟩

def union (S T : StateForm Clock Var) : StateForm Clock Var :=
  ⟨S.guards ∪ T.guards, S.guards_finite.union T.guards_finite,
    S.resets.union T.resets, S.locals ∪ T.locals, S.locals_finite.union T.locals_finite⟩

end StateForm

namespace TransitionForm

def ofState (S : StateForm Clock Var) : TransitionForm Clock Var := ⟨S, none⟩

def ofNextState (S : StateForm Clock Var) : TransitionForm Clock Var :=
  ⟨StateForm.empty, some S⟩

def unionNext : Option (StateForm Clock Var) → Option (StateForm Clock Var) →
    Option (StateForm Clock Var)
  | none, N | N, none => N
  | some S, some T => some (S.union T)

def union (Φ Ψ : TransitionForm Clock Var) : TransitionForm Clock Var :=
  ⟨Φ.current.union Ψ.current, unionNext Φ.nextPart Ψ.nextPart⟩

/-- Inner assignments retain precedence over enclosing assignments. -/
def underReset (Λ : ClockResetSet Clock) (Φ : TransitionForm Clock Var) :
    TransitionForm Clock Var :=
  { Φ with current := { Φ.current with resets := Φ.current.resets.union Λ } }

def normalize? : Judgement Clock Var → Option (TransitionForm Clock Var)
  | .terminal => some (ofState (StateForm.ofLocal .terminal))
  | .marker m => some (ofState (StateForm.ofLocal (.marker m)))
  | .predicate p => some (ofState (StateForm.ofLocal (.predicate p)))
  | .clock c r a => some (ofState (StateForm.ofGuard ⟨c, r, a⟩))
  | .reset Λ Ψ => (normalize? Ψ).map (underReset Λ)
  | .conj Φ Ψ => do
      let F ← normalize? Φ
      let G ← normalize? Ψ
      pure (F.union G)
  | .next Ψ => do
      let F ← normalize? Ψ
      match F.nextPart with
      | none => some (ofNextState F.current)
      | some _ => none

end TransitionForm

namespace Judgement

def currentPredicates : Judgement Clock Var → Set (Predicate Clock Var)
  | .predicate p => {p}
  | .conj Φ Ψ => currentPredicates Φ ∪ currentPredicates Ψ
  | .reset _ Ψ => currentPredicates Ψ
  | _ => ∅

end Judgement

namespace TransitionForm

/-- Normalization retains exact current-predicate provenance. -/
theorem normalize_currentPredicates (Ψ : Judgement Clock Var)
    {F : TransitionForm Clock Var} (h : normalize? Ψ = some F) (q : Predicate Clock Var) :
    Local.predicate q ∈ F.current.locals ↔ q ∈ Ψ.currentPredicates := by
  induction Ψ generalizing F with
  | terminal => cases h; simp [ofState, StateForm.ofLocal, Judgement.currentPredicates]
  | clock c r a => cases h; simp [ofState, StateForm.ofGuard, Judgement.currentPredicates]
  | marker m => cases h; simp [ofState, StateForm.ofLocal, Judgement.currentPredicates]
  | predicate p => cases h; simp [ofState, StateForm.ofLocal, Judgement.currentPredicates]
  | reset Λ Ψ ih =>
      cases he : normalize? Ψ with
      | none => simp [normalize?, he] at h
      | some G =>
          simp only [normalize?, he, Option.map_some, Option.some.injEq] at h
          subst F
          simpa only [underReset, Judgement.currentPredicates] using ih he
  | conj Ψ Χ ihΨ ihΧ =>
      cases he : normalize? Ψ with
      | none => simp [normalize?, he] at h
      | some G =>
          cases hf : normalize? Χ with
          | none => simp [normalize?, he, hf] at h
          | some H =>
              simp [normalize?, he, hf] at h
              subst F
              simpa only [union, StateForm.union, Set.mem_union, Judgement.currentPredicates]
                using or_congr (ihΨ he) (ihΧ hf)
  | next Ψ ih =>
      cases he : normalize? Ψ with
      | none => simp [normalize?, he] at h
      | some G =>
          cases hn : G.nextPart with
          | some N => simp [normalize?, he, hn] at h
          | none =>
              simp [normalize?, he, hn] at h
              subst F
              simp [ofNextState, StateForm.empty, Judgement.currentPredicates]

end TransitionForm

namespace ConcreteFinite
open scoped STL
open STLTableau.ExpansionRule

-- Enumerating every concrete branch elaborates many nested finite-set unions.
set_option maxHeartbeats 12000000 in
set_option linter.unusedSimpArgs false in
/-- Faithful normalization on every actual finite rule branch, under any
outer reset set, including terminal evaluation positions. -/
theorem branch_normalization [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : STLTableau.ConcreteRule p R) {Ψ : STLTableau.Judgement Clock Var}
    (hΨ : Ψ ∈ R.branches) (Λ : ClockResetSet Clock) :
    ∃ F, TransitionForm.normalize? (Judgement.ofFinite Ψ) = some F ∧
      ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
        (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P),
        (F.underReset Λ).holds σ P α k ↔ STLTableau.satisfies σ P (Λ.apply α) k Ψ := by
  classical
  (cases hr <;>
    simp only [plainAnd, plainOr, plainUntil, plainRelease, openEventually, openAlways,
      upperAlways, boundedAlways, upperEventually, boundedEventually,
      List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at hΨ <;>
    (try split_ifs at hΨ) <;>
    (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hΨ) <;>
    rcases hΨ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    (try simp only [upperAlways_defer, upperAlways_check, boundedAlways_defer,
      boundedAlways_check, boundedAlways_finish, upperEventually_defer,
      upperEventually_check, boundedEventually_defer, boundedEventually_check,
      boundedEventually_finish, STLTableau.Judgement.markedLT_eq_clock,
      STLTableau.Judgement.markedGT_eq_clock]) <;>
    (try simp only [Judgement.ofFinite, TransitionForm.normalize?, Option.bind_some,
      Option.map_some, TransitionForm.unionNext, TransitionForm.ofState,
      TransitionForm.ofNextState, TransitionForm.union, TransitionForm.underReset]) <;>
    refine ⟨_, rfl, ?_⟩ <;> intro σ P α k <;>
    by_cases hk : k.1 < P.size <;>
    simp only [TransitionForm.normalize?, Judgement.ofFinite, TransitionForm.underReset,
      TransitionForm.union, TransitionForm.unionNext, TransitionForm.ofNextState,
      TransitionForm.ofState, StateForm.ofLocal, StateForm.ofGuard, StateForm.empty,
      StateForm.union, TransitionForm.holds, StateForm.holds, Guard.holds,
      Local.holds, Local.toJudgement, Judgement.holds, Predicate.holds_ofFinite,
      STLTableau.satisfies, hk, dif_pos, dif_neg, ClockResetSet.apply_union_eq_comp,
      ClockResetSet.apply_empty, Set.mem_union, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, forall_eq, forall_const, or_imp, forall_and,
      true_and, and_true, false_and, and_false, and_assoc, and_comm,
      and_left_comm, false_implies, implies_true, ↓reduceDIte, iff_self, and_self]

end ConcreteFinite
end STLTableau.Section3
