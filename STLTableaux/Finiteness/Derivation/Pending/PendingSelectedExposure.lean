import STLTableaux.Finiteness.Derivation.Pending.PendingStep
import STLTableaux.Finiteness.Derivation.CurrentGuardProjection

/-! Exact source exposure and residual guard projection for the ordinary
completion induction. All syntax is taken from the given owned pending spine. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

/-- The selected actual local makes the body nonempty. Expose that occurrence
and the exact original residual fold, retaining literal optional absence. -/
theorem owned_selected_exposure
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (p : Predicate Clock Var)
    (left right : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate p :: right) :
    ∃ Body, foldCurrent (owned.locals.map Local.toJudgement ++
        owned.nextInputs.map Section3.Judgement.next) = some Body ∧
      StructuralEq Body (prependCurrent (.predicate p)
        (foldCurrent ((left ++ right).map Local.toJudgement ++
          owned.nextInputs.map Section3.Judgement.next))) := by
  have hmem : (.predicate p : MixedJ Clock Var) ∈ owned.locals.map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next := by
    rw [hsplit]
    simp [Local.toJudgement]
  cases hBody : foldCurrent (owned.locals.map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) with
  | none =>
    have he := (foldCurrent_none_iff _).1 hBody
    rw [he] at hmem
    cases hmem
  | some Body =>
    have hsplitFold : foldCurrent (left.map Local.toJudgement ++ .predicate p ::
        (right.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next)) = some Body := by
      simpa only [hsplit,List.map_append,List.map_cons,List.append_assoc,List.cons_append,
        Local.toJudgement] using hBody
    have hExpose := (foldCurrent_expose_split (left.map Local.toJudgement)
      (right.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next)
      (.predicate p) Body hsplitFold).1
    refine ⟨Body,rfl,?_⟩
    simpa only [List.map_append,List.append_assoc] using hExpose

/-- A residual made only of current locals and literal next leaves has no
current guards. The proof projects an actual synthetic canonical presentation;
no semantic premise or arbitrary state encoding is involved. -/
theorem residual_guard_empty {L : List (Local Clock Var)} {Ns : List (MixedJ Clock Var)}
    {Γ : MixedJ Clock Var}
    (hΓfold : foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next) = some Γ) :
    currentGuards Γ = ∅ := by
  have hshape : canonicalSyntax ClockResetSet.empty [] L Ns = some (.reset ClockResetSet.empty Γ) := by
    simp only [canonicalSyntax,List.map_nil,foldCurrent,optionalConj,hΓfold,Option.map_some]
  have hguards := canonical_currentGuards hshape
  simpa [currentGuards] using hguards

end STLTableau.Section4.Finiteness
