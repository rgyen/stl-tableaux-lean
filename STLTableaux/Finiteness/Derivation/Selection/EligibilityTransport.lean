import STLTableaux.Finiteness.Derivation.Selection.SelectedPolicy
import STLTableaux.Finiteness.Derivation.Branches.RawBranchCurrentShape

/-! Eligibility of surviving current `↑↓` sources through the exact selected
children. Global boundedness and uniqueness stay fixed; current reset/marker and
semantic conditions are recovered from actual syntax and map agreement. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*}

private def rawLocals : MixedJ Clock Var → Set (Local Clock Var)
  | .terminal => {.terminal}
  | .marker m => {.marker m}
  | .predicate p => {.predicate p}
  | .conj J K => rawLocals J ∪ rawLocals K
  | .reset _ J => rawLocals J
  | _ => ∅

private theorem structural_locals {J K : MixedJ Clock Var} (h : StructuralEq J K) : rawLocals J = rawLocals K := by
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
  | some J => rawLocals J

private theorem optional_locals (J K : Option (MixedJ Clock Var)) :
    optionLocals (optionalConj J K) = optionLocals J ∪ optionLocals K := by
  cases J <;> cases K <;> simp [optionalConj,optionLocals,rawLocals]

private theorem fold_locals (Js : List (MixedJ Clock Var)) (l : Local Clock Var) :
    l ∈ optionLocals (foldCurrent Js) ↔ ∃ J ∈ Js, l ∈ rawLocals J := by
  induction Js with
  | nil => simp [foldCurrent,optionLocals]
  | cons J Js ih =>
      rw [foldCurrent,optional_locals]
      change (l ∈ rawLocals J ∨ l ∈ optionLocals (foldCurrent Js)) ↔ _
      simp only [ih,List.mem_cons,exists_eq_or_imp]

private theorem canonical_locals
    {R : ClockResetSet Clock} {G : List (Section3.Guard Clock)} {L : List (Local Clock Var)}
    {Ns : List (MixedJ Clock Var)} {C : MixedJ Clock Var}
    (h : canonicalSyntax R G L Ns = some C) (l : Local Clock Var) :
    l ∈ rawLocals C ↔ l ∈ L := by
  have hg : optionLocals (foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var)))) = ∅ := by
    ext a
    rw [fold_locals]
    simp only [List.mem_map]
    constructor
    · rintro ⟨J,⟨g,hg,rfl⟩,ha⟩; exact ha
    · exact False.elim
  have hb : optionLocals (foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next)) = {l | l ∈ L} := by
    ext a
    rw [fold_locals]
    simp only [List.mem_append,List.mem_map]
    constructor
    · rintro ⟨J,(⟨b,hb,rfl⟩ | ⟨K,hK,rfl⟩),ha⟩
      · cases b <;> simpa only [Local.toJudgement,rawLocals,Set.mem_singleton_iff] using ha ▸ hb
      · exact False.elim ha
    · intro ha
      refine ⟨a.toJudgement,Or.inl ⟨a,ha,rfl⟩,?_⟩
      cases a <;> exact Set.mem_singleton _
  have hreset : optionLocals ((foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next)).map
      (Section3.Judgement.reset R)) = optionLocals (foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next)) := by
    cases foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next) <;> rfl
  have he := congrArg optionLocals h
  simp only [canonicalSyntax] at he
  rw [optional_locals,hg,hreset,hb,Set.empty_union] at he
  change {l | l ∈ L} = rawLocals C at he
  rw [← he]
  rfl

private theorem owned_local_iff {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (l : Local Clock Var) : l ∈ owned.locals ↔ l ∈ rawLocals J := by
  rw [structural_locals owned.regroup]
  exact (canonical_locals owned.shape l).symm

private theorem predicate_local (J : MixedJ Clock Var) (p : Predicate Clock Var) :
    Local.predicate p ∈ rawLocals J ↔ p ∈ J.currentPredicates := by
  induction J with
  | terminal | marker | clock | next => simp [rawLocals,Section3.Judgement.currentPredicates]
  | predicate q => simp [rawLocals,Section3.Judgement.currentPredicates]
  | conj J K ih ik => exact or_congr ih ik
  | reset R J ih => exact ih

private theorem fold_local_mem {L : List (Local Clock Var)} {Ns : List (MixedJ Clock Var)}
    {Γ : MixedJ Clock Var} (hf : foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next) = some Γ)
    (l : Local Clock Var) : l ∈ rawLocals Γ ↔ l ∈ L := by
  have hs : canonicalSyntax ClockResetSet.empty [] L Ns = some (.reset ClockResetSet.empty Γ) := by
    simp only [canonicalSyntax,List.map_nil,foldCurrent,optionalConj,hf,Option.map_some]
  exact canonical_locals hs l

private theorem guard_locals (c : Clock) (b : Marker) (Γ : MixedJ Clock Var) :
    rawLocals (withBoundaryGuard c b Γ) = rawLocals Γ := by
  cases b <;> simp [withBoundaryGuard,rawLocals]

private theorem apply_agrees (R S : ClockResetSet Clock) (α : ClockValuation Clock) (c : Clock)
    (h : S.value c = R.value c) : S.apply (R.apply α) c = R.apply α c := by
  simp only [ClockResetSet.apply,h]
  cases R.value c <;> rfl

private theorem plain_transport (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α β : ClockValuation Clock) (k : STLTableau.Judgement.Position P) (φ : Formula Var) :
    Judgement.holds σ P α k (.predicate (.plain φ) : MixedJ Clock Var) ↔
      Judgement.holds σ P β k (.predicate (.plain φ) : MixedJ Clock Var) :=
  Judgement.holds_congr_of_agree (by intro c hc; exact False.elim hc) σ P k

private theorem ordinary_bounded_residual [DecidableEq Clock]
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} (choice : OrdinaryChoice E owned) (q : Predicate Clock Var)
    (hb : IsBoundedPredicate q) (hq : Local.predicate q ∈ choice.child.locals) :
    Local.predicate q ∈ choice.left ++ choice.right := by
  have hraw := (predicate_local _ q).1 ((owned_local_iff choice.child _).1 hq)
  cases q with
  | plain => cases hb
  | upper => cases hb
  | bounded c d m ell kind I φ =>
      cases hf : foldCurrent ((choice.left ++ choice.right).map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next) with
      | none =>
          have hB : Predicate.bounded c d m ell kind I φ ∈ choice.B.currentPredicates := by
            simpa only [ordinarySelectedInput,hf] using hraw
          exact False.elim (choice.branch.no_current_bounded c d m ell kind I φ hB)
      | some Γ =>
          change _ ∈ (ordinarySelectedInput _ _ _ _).currentPredicates at hraw
          simp only [ordinarySelectedInput,hf,Section3.Judgement.currentPredicates] at hraw
          rcases hraw with hB | hΓ
          · exact False.elim (choice.branch.no_current_bounded c d m ell kind I φ hB)
          · exact (fold_local_mem hf _).1 ((predicate_local Γ _).2 hΓ)

private theorem ordinary_marker [DecidableEq Clock]
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} (choice : OrdinaryChoice E owned) (ell : Marker)
    (hm : Local.marker ell ∈ owned.locals) : Local.marker ell ∈ choice.child.locals := by
  have hremaining : Local.marker ell ∈ choice.left ++ choice.right := by
    rw [choice.split] at hm
    simpa only [List.mem_append,List.mem_cons,reduceCtorEq,false_or] using hm
  apply (owned_local_iff choice.child _).2
  cases hf : foldCurrent ((choice.left ++ choice.right).map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next) with
  | none =>
      have he := (foldCurrent_none_iff _).1 hf
      have hempty : choice.left ++ choice.right = [] := List.map_eq_nil_iff.1 (List.append_eq_nil_iff.1 he).1
      rw [hempty] at hremaining
      cases hremaining
  | some Γ =>
      change Local.marker ell ∈ rawLocals (ordinarySelectedInput _ _ _ _)
      simp only [ordinarySelectedInput,rawLocals]
      exact Or.inr ((fold_local_mem hf _).2 hremaining)

/-- Ordinary selection transports the same global E to its exact chosen child. -/
theorem Eligibility.ordinary
    [DecidableEq Clock] {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var}
    {R : ClockResetSet Clock} {W : Set Clock} {owned : OwnedPending J R W} {U : Set Clock}
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain} {α : ClockValuation Clock}
    {k : STLTableau.Judgement.Position P} (h : Eligibility E owned U σ P α k)
    (choice : OrdinaryChoice E owned) : Eligibility E choice.child U σ P (R.apply α) k := by
  refine ⟨h.bounded,h.unique_formula,?_⟩
  intro q hqE hq
  have hremaining := ordinary_bounded_residual choice q (h.bounded q hqE) hq
  have hqOld : Local.predicate q ∈ owned.locals := by
    rw [choice.split]
    simp only [List.mem_append,List.mem_cons] at hremaining ⊢
    tauto
  obtain ⟨c,d,m,ell,kind,I,φ,hqdef,hf,hm,hd,hplain,hcomp,hU⟩ := h.current q hqE hqOld
  have hca : c ∈ activeSupport (choice.left ++ choice.right) :=
    ⟨q,hremaining,by rw [hqdef]; exact Or.inl rfl⟩
  have hda : d ∈ activeSupport (choice.left ++ choice.right) :=
    ⟨q,hremaining,by rw [hqdef]; exact Or.inr (Set.mem_singleton d)⟩
  have hc := choice.agreement c hca
  have hd' := choice.agreement d hda
  refine ⟨c,d,m,ell,kind,I,φ,hqdef,hf,ordinary_marker choice ell hm,hd'.trans hd,?_,?_,hU⟩
  · exact (plain_transport σ P _ _ k _).1 hplain
  · rw [apply_agrees R choice.childR α c hc]
    exact hcomp

private theorem boundary_residual_fold [DecidableEq Clock]
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {required : Bool} (choice : BoundaryChoice E owned required) :
    foldCurrent ((Local.marker choice.ell :: choice.rest).map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) = some choice.Gamma := by
  simp only [List.map_cons,List.cons_append,Local.toJudgement,foldCurrent_cons]
  rw [← choice.residual]

private theorem boundary_bounded_residual [DecidableEq Clock]
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {required : Bool} (choice : BoundaryChoice E owned required)
    (q : Predicate Clock Var) (hb : IsBoundedPredicate q) (hq : Local.predicate q ∈ choice.child.locals) :
    Local.predicate q ∈ choice.rest := by
  have hraw := (predicate_local _ q).1 ((owned_local_iff choice.child _).1 hq)
  rw [boundaryReplacement_child_predicates] at hraw
  cases q with
  | plain => cases hb
  | upper => cases hb
  | bounded c d m ell kind I φ =>
      rcases hraw with he | hΓ
      · cases he
      · have hm := (fold_local_mem (boundary_residual_fold choice) _).1
          ((predicate_local choice.Gamma _).2 hΓ)
        simpa only [List.mem_cons,reduceCtorEq,false_or] using hm

private theorem boundary_rest_old [DecidableEq Clock]
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {required : Bool} (choice : BoundaryChoice E owned required)
    (l : Local Clock Var) (hl : l ∈ choice.rest) : l ∈ choice.left ++ choice.right := by
  apply choice.selection.mem_iff.2
  cases required <;> simp [hl]

private theorem boundary_marker [DecidableEq Clock]
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {required : Bool} (choice : BoundaryChoice E owned required)
    (ell : Marker) (hm : Local.marker ell ∈ owned.locals) : Local.marker ell ∈ choice.child.locals := by
  have hremaining : Local.marker ell ∈ choice.left ++ choice.right := by
    rw [choice.split] at hm
    simpa only [List.mem_append,List.mem_cons,reduceCtorEq,false_or] using hm
  have hselected := choice.selection.mem_iff.1 hremaining
  have horigin : ell = choice.ell ∨ Local.marker ell ∈ choice.rest := by
    cases required <;>
      simpa only [Bool.false_eq_true,eq_self,ite_false,ite_true,List.mem_cons,
        reduceCtorEq,Local.marker.injEq,false_or] using hselected
  apply (owned_local_iff choice.child _).2
  simp only [boundaryReplacementChild,rawLocals,guard_locals]
  rcases horigin with rfl | hm
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ((fold_local_mem (boundary_residual_fold choice) _).2 (List.mem_cons_of_mem _ hm)))

private theorem copied_value (R : ClockResetSet Clock) (L : List (Local Clock Var)) (c : Clock)
    (hc : c ∈ activeSupport L) : (copyActiveResets R L).value c = R.value c := by
  classical
  change (if c ∈ activeSupport L then R.value c else none) = R.value c
  exact if_pos hc

/-- Required and optional boundary replacement retain eligibility exactly for
surviving current entries. The new upper is excluded by global boundedness. -/
theorem Eligibility.boundary
    [DecidableEq Clock] {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var}
    {R : ClockResetSet Clock} {W : Set Clock} {owned : OwnedPending J R W} {U : Set Clock}
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain} {α : ClockValuation Clock}
    {k : STLTableau.Judgement.Position P} (h : Eligibility E owned U σ P α k)
    {required : Bool} (choice : BoundaryChoice E owned required) :
    Eligibility E choice.child U σ P (R.apply α) k := by
  refine ⟨h.bounded,h.unique_formula,?_⟩
  intro q hqE hq
  have hrest := boundary_bounded_residual choice q (h.bounded q hqE) hq
  have hremaining := boundary_rest_old choice _ hrest
  have hqOld : Local.predicate q ∈ owned.locals := by
    rw [choice.split]
    simp only [List.mem_append,List.mem_cons] at hremaining ⊢
    tauto
  obtain ⟨c,d,m,ell,kind,I,φ,hqdef,hf,hm,hd,hplain,hcomp,hU⟩ := h.current q hqE hqOld
  have hca : c ∈ activeSupport (choice.left ++ choice.right) :=
    ⟨q,hremaining,by rw [hqdef]; exact Or.inl rfl⟩
  have hda : d ∈ activeSupport (choice.left ++ choice.right) :=
    ⟨q,hremaining,by rw [hqdef]; exact Or.inr (Set.mem_singleton d)⟩
  have hc := copied_value R (choice.left ++ choice.right) c hca
  have hd' := copied_value R (choice.left ++ choice.right) d hda
  refine ⟨c,d,m,ell,kind,I,φ,hqdef,hf,boundary_marker choice ell hm,hd'.trans hd,?_,?_,hU⟩
  · exact (plain_transport σ P _ _ k _).1 hplain
  · rw [apply_agrees R (copyActiveResets R (choice.left ++ choice.right)) α c hc]
    exact hcomp

end STLTableau.Section4.Finiteness
