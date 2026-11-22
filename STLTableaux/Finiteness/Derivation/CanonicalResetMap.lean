import STLTableaux.Finiteness.Derivation.Pending.PendingOwnership

/-! Exact inherited reset map of a safely normalized owned canonical spine.
This includes the genuinely absent body case; no reset-domain approximation. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

def currentResetMap : MixedJ Clock Var → ClockResetSet Clock
  | .conj J K => (currentResetMap J).union (currentResetMap K)
  | .reset R J => (currentResetMap J).union R
  | _ => ClockResetSet.empty

theorem safe_reset_map {J : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : SafeNormalization J F) :
    F.current.resets = currentResetMap J := by
  induction h with
  | conj h g hc ih ig => exact congrArg₂ ClockResetSet.union ih ig
  | reset R h hd ih => exact congrArg (fun S => S.union R) ih
  | terminal | clock | marker | predicate | next => rfl

private theorem fold_reset_empty (Xs : List (MixedJ Clock Var))
    (h : ∀ X ∈ Xs, currentResetMap X = ClockResetSet.empty)
    {J : MixedJ Clock Var} (hf : foldCurrent Xs = some J) :
    currentResetMap J = ClockResetSet.empty := by
  induction Xs generalizing J with
  | nil => cases hf
  | cons X Xs ih =>
    rw [foldCurrent_cons] at hf
    have he := Option.some.inj hf
    subst J
    cases ht : foldCurrent Xs with
    | none => exact h X List.mem_cons_self
    | some T =>
      change (currentResetMap X).union (currentResetMap T) = ClockResetSet.empty
      rw [h X List.mem_cons_self,ih (fun K hK => h K (List.mem_cons_of_mem X hK)) ht]
      rfl

private theorem local_reset_empty (l : Local Clock Var) :
    currentResetMap l.toJudgement = ClockResetSet.empty := by cases l <;> rfl

/-- Exact map equality, including values, for the given owned canonical input.
Literal next payload resets do not become current resets. -/
theorem OwnedPending.current_resets_of_safe
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) {F : Section3.TransitionForm Clock Var}
    (hSafe : SafeNormalization owned.canonical F) : F.current.resets = R := by
  rw [safe_reset_map hSafe]
  have hg : ∀ G, foldCurrent (owned.guards.map (fun g => (g.toJudgement : MixedJ Clock Var))) = some G →
      currentResetMap G = ClockResetSet.empty := by
    intro G hG
    apply fold_reset_empty _ _ hG
    intro X hX
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hX
    cases g
    rfl
  have hb : ∀ Body, foldCurrent (owned.locals.map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) = some Body →
      currentResetMap Body = ClockResetSet.empty := by
    intro Body hBody
    apply fold_reset_empty _ _ hBody
    intro X hX
    rcases List.mem_append.mp hX with hl | hn
    · obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hl
      exact local_reset_empty l
    · obtain ⟨K,hK,rfl⟩ := List.mem_map.mp hn
      rfl
  cases hG : foldCurrent (owned.guards.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
  | none =>
    cases hBody : foldCurrent (owned.locals.map Local.toJudgement ++
        owned.nextInputs.map Section3.Judgement.next) with
    | none =>
      have hs := owned.shape
      simp only [canonicalSyntax,hG,hBody,Option.map_none,optionalConj] at hs
      cases hs
    | some Body =>
      have he : .reset R Body = owned.canonical := by
        simpa only [canonicalSyntax,hG,hBody,Option.map_some,optionalConj,Option.some.injEq] using owned.shape
      rw [← he,currentResetMap,hb Body hBody]
      rfl
  | some G =>
    cases hBody : foldCurrent (owned.locals.map Local.toJudgement ++
        owned.nextInputs.map Section3.Judgement.next) with
    | none =>
      have he : G = owned.canonical := by
        simpa only [canonicalSyntax,hG,hBody,Option.map_none,optionalConj,Option.some.injEq] using owned.shape
      have hempty := (foldCurrent_none_iff _).1 hBody
      have hempty' : owned.locals = [] ∧ owned.nextInputs = [] := by
        simpa only [List.append_eq_nil_iff,List.map_eq_nil_iff] using hempty
      rw [← he,hg G hG,owned.absent_body_reset hempty'.1 hempty'.2]
    | some Body =>
      have he : .conj G (.reset R Body) = owned.canonical := by
        simpa only [canonicalSyntax,hG,hBody,Option.map_some,optionalConj,Option.some.injEq] using owned.shape
      rw [← he,currentResetMap,currentResetMap,hg G hG,hb Body hBody]
      rfl

end STLTableau.Section4.Finiteness
