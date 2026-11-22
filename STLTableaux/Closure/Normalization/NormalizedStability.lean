import STLTableaux.Tableau.Stability.GeneratorStability

/-! Formula provenance through the structural parser, in both current and
next parts. Clock renaming and reset assignments cannot change these sets. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}

def StateForm.underlyingFormulas (S : StateForm Clock Var) : Set (Formula Var) :=
  {φ | ∃ p, Local.predicate p ∈ S.locals ∧ φ = p.formula}

def TransitionForm.underlyingFormulas (F : TransitionForm Clock Var) : Set (Formula Var) :=
  F.current.underlyingFormulas ∪ match F.nextPart with
    | none => ∅
    | some N => N.underlyingFormulas

def StateForm.UnderlyingStable (S : StateForm Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) : Prop :=
  ∀ φ ∈ S.underlyingFormulas, σ.StablePartition φ P

def TransitionForm.UnderlyingStable (F : TransitionForm Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) : Prop :=
  ∀ φ ∈ F.underlyingFormulas, σ.StablePartition φ P

@[simp] theorem TransitionForm.underlyingFormulas_underReset (F : TransitionForm Clock Var)
    (Λ : ClockResetSet Clock) : (F.underReset Λ).underlyingFormulas = F.underlyingFormulas := rfl

@[simp] theorem TransitionForm.underlyingFormulas_ofState (S : StateForm Clock Var) :
    (ofState S).underlyingFormulas = S.underlyingFormulas := by
  simp [underlyingFormulas, ofState]

theorem TransitionForm.UnderlyingStable.current {F : TransitionForm Clock Var}
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    (h : F.UnderlyingStable σ P) : F.current.UnderlyingStable σ P :=
  fun φ hφ => h φ (Or.inl hφ)

theorem TransitionForm.UnderlyingStable.next {F : TransitionForm Clock Var}
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    (h : F.UnderlyingStable σ P) (N : StateForm Clock Var) (hN : F.nextPart = some N) :
    N.UnderlyingStable σ P := by
  intro φ hφ
  apply h φ
  right
  simpa [TransitionForm.underlyingFormulas, hN] using hφ

theorem StateForm.underlyingFormulas_union (S T : StateForm Clock Var) :
    (S.union T).underlyingFormulas = S.underlyingFormulas ∪ T.underlyingFormulas := by
  ext φ
  simp only [underlyingFormulas, union, Set.mem_setOf_eq, Set.mem_union]
  aesop

theorem TransitionForm.underlyingFormulas_union (F G : TransitionForm Clock Var) :
    (F.union G).underlyingFormulas = F.underlyingFormulas ∪ G.underlyingFormulas := by
  cases hF : F.nextPart <;> cases hG : G.nextPart <;>
    simp [underlyingFormulas, union, unionNext, hF, hG, StateForm.underlyingFormulas_union,
      Set.union_assoc, Set.union_comm, Set.union_left_comm]

theorem TransitionForm.UnderlyingStable.union {F G : TransitionForm Clock Var}
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    (hF : F.UnderlyingStable σ P) (hG : G.UnderlyingStable σ P) :
    (F.union G).UnderlyingStable σ P := by
  intro φ hφ
  rw [TransitionForm.underlyingFormulas_union] at hφ
  exact hφ.elim (hF φ) (hG φ)

theorem TransitionForm.normalize_underlyingFormulas (Ψ : Judgement Clock Var)
    {F : TransitionForm Clock Var} (h : normalize? Ψ = some F) :
    F.underlyingFormulas = Ψ.underlyingFormulas := by
  induction Ψ generalizing F with
  | terminal => cases h; simp [underlyingFormulas, ofState, StateForm.ofLocal,
      StateForm.underlyingFormulas, Judgement.underlyingFormulas]
  | clock c r a => cases h; simp [underlyingFormulas, ofState, StateForm.ofGuard,
      StateForm.underlyingFormulas, Judgement.underlyingFormulas]
  | marker m => cases h; simp [underlyingFormulas, ofState, StateForm.ofLocal,
      StateForm.underlyingFormulas, Judgement.underlyingFormulas]
  | predicate p => cases h; simp [underlyingFormulas, ofState, StateForm.ofLocal,
      StateForm.underlyingFormulas, Judgement.underlyingFormulas]
  | reset Λ Ψ ih =>
      cases he : normalize? Ψ with
      | none => simp [normalize?, he] at h
      | some G =>
          simp only [normalize?, he, Option.map_some, Option.some.injEq] at h
          subst F
          simpa only [underlyingFormulas, underReset, StateForm.underlyingFormulas, Judgement.underlyingFormulas] using (ih (F := G) he)
  | conj Ψ Χ ihΨ ihΧ =>
      cases he : normalize? Ψ with
      | none => simp [normalize?, he] at h
      | some G =>
          cases hf : normalize? Χ with
          | none => simp [normalize?, he, hf] at h
          | some H =>
              simp [normalize?, he, hf] at h
              subst F
              simpa only [underlyingFormulas_union, Judgement.underlyingFormulas]
                using congrArg₂ (fun A B : Set (Formula Var) => A ∪ B) (ihΨ he) (ihΧ hf)
  | next Ψ ih =>
      cases he : normalize? Ψ with
      | none => simp [normalize?, he] at h
      | some G =>
          cases hn : G.nextPart with
          | some N => simp [normalize?, he, hn] at h
          | none =>
              simp [normalize?, he, hn] at h
              subst F
              simpa [underlyingFormulas, ofNextState, StateForm.empty,
                StateForm.underlyingFormulas, hn, Judgement.underlyingFormulas] using ih he

theorem TransitionForm.normalize_underlyingStable (Ψ : Judgement Clock Var)
    {F : TransitionForm Clock Var} (h : normalize? Ψ = some F)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) :
    F.UnderlyingStable σ P ↔ Ψ.UnderlyingStable σ P := by
  unfold UnderlyingStable Judgement.UnderlyingStable
  rw [normalize_underlyingFormulas Ψ h]

end STLTableau.Section3
