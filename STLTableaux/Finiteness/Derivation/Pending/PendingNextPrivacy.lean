import STLTableaux.Finiteness.Derivation.CanonicalProjections

/-! Internal next-payload privacy through actual canonical pending assembly.
This is a separate syntactic invariant, not a new OwnedPending field or a
completed resolver. Current-local collection does not change literal nexts. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

namespace PendingNextPrivacy

private def optionalNextPrivate : Option (MixedJ Clock Var) → Prop
  | none => True
  | some J => NextPrivate J

private theorem optional_conj (J K : Option (MixedJ Clock Var)) :
    optionalNextPrivate (optionalConj J K) ↔ optionalNextPrivate J ∧ optionalNextPrivate K := by
  cases J <;> cases K <;> simp [optionalConj,optionalNextPrivate,NextPrivate]

private theorem optional_reset (R : ClockResetSet Clock) (J : Option (MixedJ Clock Var)) :
    optionalNextPrivate (J.map (Section3.Judgement.reset R)) ↔ optionalNextPrivate J := by
  cases J <;> rfl

private theorem fold_nextPrivate (Js : List (MixedJ Clock Var)) :
    optionalNextPrivate (foldCurrent Js) ↔ ∀ J ∈ Js, NextPrivate J := by
  induction Js with
  | nil => simp [foldCurrent,optionalNextPrivate]
  | cons J Js ih =>
    rw [foldCurrent,optional_conj,ih]
    simp [optionalNextPrivate]

@[simp] private theorem local_nextPrivate (l : Local Clock Var) : NextPrivate l.toJudgement := by
  cases l <;> trivial

private theorem canonical_optional (R : ClockResetSet Clock) (G : List (Guard Clock))
    (L : List (Local Clock Var)) (Ns : List (MixedJ Clock Var)) :
    optionalNextPrivate (canonicalSyntax R G L Ns) ↔
      ∀ K ∈ Ns, privateRawCurrent K ∧ NextPrivate K := by
  simp only [canonicalSyntax,optional_conj,optional_reset,fold_nextPrivate]
  simp only [List.forall_mem_append,List.forall_mem_map]
  simp [Guard.toJudgement,NextPrivate]

end PendingNextPrivacy

/-- The exact internal-next privacy content of an actual canonical spine.
Outside guards, current locals, and the common reset contribute no next layer. -/
theorem canonical_nextPrivate_iff
    {R : ClockResetSet Clock} {G : List (Guard Clock)} {L : List (Local Clock Var)}
    {Ns : List (MixedJ Clock Var)} {C : MixedJ Clock Var}
    (hshape : canonicalSyntax R G L Ns = some C) :
    NextPrivate C ↔ ∀ K ∈ Ns, privateRawCurrent K ∧ NextPrivate K := by
  have h := PendingNextPrivacy.canonical_optional R G L Ns
  rw [hshape] at h
  exact h

/-- Extract the future-payload invariant from the GIVEN original pending source
using its proved structural regrouping, not a successor privacy assumption. -/
theorem owned_payload_nextPrivate
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (hJ : NextPrivate J) :
    ∀ K ∈ owned.nextInputs, privateRawCurrent K ∧ NextPrivate K :=
  (canonical_nextPrivate_iff owned.shape).1 (owned.regroup.nextPrivate_iff.1 hJ)

/-- Appending the selected branch's next judgements preserves `NextPrivate`
for the assembled child. -/
theorem child_nextPrivate [DecidableEq Clock]
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (hJ : NextPrivate J)
    {p : Predicate Clock Var} {B Cb : MixedJ Clock Var} (raw : RawBranch p B)
    {Rb : ClockResetSet Clock} {Lb : List (Local Clock Var)} {Nb : List (MixedJ Clock Var)}
    (hbranch : canonicalSyntax Rb [] Lb Nb = some Cb) (hBC : StructuralEq B Cb)
    {Rc : ClockResetSet Clock} {Gc : List (Guard Clock)} {Lc : List (Local Clock Var)}
    {Cchild : MixedJ Clock Var}
    (hchild : canonicalSyntax Rc Gc Lc (Nb ++ owned.nextInputs) = some Cchild) :
    NextPrivate Cchild := by
  have hnew := (canonical_nextPrivate_iff hbranch).1 (hBC.nextPrivate_iff.1 raw.next_private)
  have hold := owned_payload_nextPrivate owned hJ
  apply (canonical_nextPrivate_iff hchild).2
  intro K hK
  rcases List.mem_append.mp hK with hK | hK
  · exact hnew K hK
  · exact hold K hK

end STLTableau.Section4.Finiteness
