import STLTableaux.Finiteness.Derivation.NextPayloadLocals
import STLTableaux.Finiteness.Derivation.CanonicalProjections

/-! Exact local membership of an owned input safely presenting a state form.
Markers are retained as syntax; reset erasure removes only reset wrappers. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

theorem ACIdem.currentLocalSet_eq {J K : MixedJ Clock Var} (h : StructuralEq J K) :
    currentLocalSet J = currentLocalSet K := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig
  | assoc => exact Set.union_assoc _ _ _
  | comm => exact Set.union_comm _ _
  | idem => exact Set.union_self _
  | conj h g ih ig => exact congrArg₂ Set.union ih ig
  | reset R h ih => exact ih
  | resetDistrib => rfl
  | resetUnused => rfl
  | resetNested => rfl

private def optionLocals : Option (MixedJ Clock Var) → Set (Local Clock Var)
  | none => ∅
  | some J => currentLocalSet J

private theorem optional_locals (J K : Option (MixedJ Clock Var)) :
    optionLocals (optionalConj J K) = optionLocals J ∪ optionLocals K := by
  cases J <;> cases K <;> simp [optionalConj,optionLocals,currentLocalSet]

private theorem fold_locals (Js : List (MixedJ Clock Var)) (l : Local Clock Var) :
    l ∈ optionLocals (foldCurrent Js) ↔ ∃ J ∈ Js, l ∈ currentLocalSet J := by
  induction Js with
  | nil => simp [foldCurrent,optionLocals]
  | cons J Js ih =>
      rw [foldCurrent,optional_locals]
      change (l ∈ currentLocalSet J ∨ l ∈ optionLocals (foldCurrent Js)) ↔ _
      simp only [ih,List.mem_cons,exists_eq_or_imp]

theorem canonical_currentLocalSet
    {R : ClockResetSet Clock} {G : List (Section3.Guard Clock)} {L : List (Local Clock Var)}
    {Ns : List (MixedJ Clock Var)} {C : MixedJ Clock Var}
    (h : canonicalSyntax R G L Ns = some C) : currentLocalSet C = {l | l∈L} := by
  have hg : optionLocals (foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var)))) = ∅ := by
    ext a
    rw [fold_locals]
    simp only [List.mem_map]
    constructor
    · rintro ⟨J,⟨g,hg,rfl⟩,ha⟩; exact ha
    · exact False.elim
  have hb : optionLocals (foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next)) = {l | l∈L} := by
    ext a
    rw [fold_locals]
    simp only [List.mem_append,List.mem_map]
    constructor
    · rintro ⟨J,(⟨b,hb,rfl⟩ | ⟨K,hK,rfl⟩),ha⟩
      · cases b <;> simpa only [Local.toJudgement,currentLocalSet,Set.mem_singleton_iff] using ha ▸ hb
      · exact False.elim ha
    · intro ha
      refine ⟨a.toJudgement,Or.inl ⟨a,ha,rfl⟩,?_⟩
      cases a <;> exact Set.mem_singleton _
  have hr : optionLocals ((foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next)).map
      (Section3.Judgement.reset R)) = optionLocals (foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next)) := by
    cases foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next) <;> rfl
  have he := congrArg optionLocals h
  simp only [canonicalSyntax] at he
  rw [optional_locals,hg,hr,hb,Set.empty_union] at he
  exact he.symm

/-- The canonical list and actual state represent precisely the same locals,
including marker and terminal constructors. No list-order claim is required. -/
theorem OwnedPending.locals_eq_of_safe
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock} {N : Section3.StateForm Clock Var}
    (owned : OwnedPending J R W) (hSafe : SafeNormalization J (.ofState N)) :
    {l | l∈owned.locals} = N.locals :=
  (canonical_currentLocalSet owned.shape).symm.trans
    (owned.regroup.currentLocalSet_eq.symm.trans hSafe.current_locals_eq.symm)

theorem OwnedPending.local_mem_of_safe
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock} {N : Section3.StateForm Clock Var}
    (owned : OwnedPending J R W) (hSafe : SafeNormalization J (.ofState N)) (l : Local Clock Var) :
    l∈owned.locals ↔ l∈N.locals := by
  change l∈{l | l∈owned.locals} ↔ l∈N.locals
  rw [owned.locals_eq_of_safe hSafe]

end STLTableau.Section4.Finiteness
