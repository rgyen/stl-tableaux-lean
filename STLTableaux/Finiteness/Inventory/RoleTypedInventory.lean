import STLTableaux.Finiteness.ClockAllocation.SlotFrame
import STLTableaux.Finiteness.Derivation.NormalizationRenaming

/-! Syntactic typed-role membership in the actual sparse inventory. This
transports given actual role data; it asserts no allocation existence. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var Slot : Type*}
namespace SlotFrame

structure StateTyped (τ : Slot → FiniteInventory.Triple Clock Var)
    (role : ClockRoles Clock Slot) (S : Section3.StateForm Clock Var) : Prop where
  predicates : ∀p,Local.predicate p∈S.locals → PredicateTyped τ role p
  guards : ∀g∈S.guards,GuardTyped τ role g
  resets : ∀c a,S.resets.value c=some a → ResetTyped τ role c a

structure TransitionTyped (τ : Slot → FiniteInventory.Triple Clock Var)
    (role : ClockRoles Clock Slot) (F : Section3.TransitionForm Clock Var) : Prop where
  current : StateTyped τ role F.current
  next : ∀N,F.nextPart=some N → StateTyped τ role N

variable [Fintype Slot]

theorem stateTyped {τ : Slot → FiniteInventory.Triple Clock Var}
    {N : Section3.StateForm Clock Var} {e : Equiv.Perm Clock} (frame : SlotFrame τ N e) :
    StateTyped τ frame.role N := ⟨frame.predicates,frame.guards,frame.resets⟩

private theorem mark_surjective (m : Marker) : ∃b,FiniteInventory.mark b=m := by
  cases m
  · exact ⟨true,rfl⟩
  · exact ⟨false,rfl⟩

private theorem relation_surjective (r : ClockRelation) : ∃i : Fin 5,FiniteInventory.relationAt i=r := by
  cases r with
  | ge => exact ⟨0,rfl⟩
  | gt => exact ⟨1,rfl⟩
  | eq => exact ⟨2,rfl⟩
  | lt => exact ⟨3,rfl⟩
  | le => exact ⟨4,rfl⟩

/-- Each actual typed predicate lands in its own slot family's local inventory. -/
theorem predicate_rename_mem
    (P : Finset (Formula Var)) (τ : Slot → FiniteInventory.Triple Clock Var)
    (role : ClockRoles Clock Slot) (e : Equiv.Perm Clock)
    (he : ∀c s r,role c=some (s,r) → e c=FiniteInventory.clockAt (τ s) r)
    (p : Predicate Clock Var) (hp : PredicateTyped τ role p)
    (hplain : ∀φ,p=.plain φ → φ∈P) :
    Local.predicate (p.rename e)∈FiniteInventory.locals P τ := by
  classical
  unfold FiniteInventory.locals
  simp only [Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and]
  cases p with
  | plain φ => exact Or.inl (Or.inr ⟨φ,hplain φ rfl,rfl⟩)
  | upper c m kind I φ =>
      obtain ⟨s,hc,hkind,hI,hφ⟩ := hp
      obtain ⟨b,hb⟩ := mark_surjective m
      refine Or.inr ⟨(s,Sum.inl b),?_⟩
      have hh := he c s 0 hc
      simpa only [FiniteInventory.slotLocal,Predicate.rename,hb,hkind,hI,hφ,
        FiniteInventory.clockAt,ite_true] using congrArg
          (fun x=>Local.predicate (.upper x m (τ s).kind (τ s).interval (τ s).body)) hh.symm
  | bounded c d m q kind I φ =>
      obtain ⟨s,r,hr,hc,hd,hkind,hI,hφ⟩ := hp
      obtain ⟨bm,hm⟩ := mark_surjective m
      obtain ⟨bq,hq⟩ := mark_surjective q
      have hright : ∃br : Bool,(if br then (τ s).right₁ else (τ s).right₀)=FiniteInventory.clockAt (τ s) r := by
        rcases hr with hr | hr <;> subst r
        · exact ⟨false,rfl⟩
        · exact ⟨true,rfl⟩
      obtain ⟨br,hbr⟩ := hright
      refine Or.inr ⟨(s,Sum.inr (br,bm,bq)),?_⟩
      have hh := he c s 0 hc
      have hh' := he d s r hd
      simp only [FiniteInventory.clockAt,ite_true] at hh
      simp only [FiniteInventory.slotLocal,Predicate.rename,hm,hq,hkind,hI,hφ]
      rw [←hh,hbr,←hh']

/-- Full StateForm inventory membership, including guards and reset values. -/
theorem StateTyped.rename_within
    {τ : Slot → FiniteInventory.Triple Clock Var} {role : ClockRoles Clock Slot}
    {S : Section3.StateForm Clock Var} (typed : StateTyped τ role S)
    (P : Finset (Formula Var)) (e : Equiv.Perm Clock)
    (he : ∀c s r,role c=some (s,r) → e c=FiniteInventory.clockAt (τ s) r)
    (hplain : ∀φ,Local.predicate (.plain φ)∈S.locals → φ∈P) :
    FiniteInventory.Within (FiniteInventory.locals P τ) (FiniteInventory.guards τ)
      (FiniteInventory.resets τ) (S.rename e) := by
  classical
  constructor
  · rintro l ⟨a,ha,rfl⟩
    cases a with
    | terminal =>
        apply Finset.mem_union_left
        apply Finset.mem_union_left
        exact Finset.mem_image.2 ⟨none,Finset.mem_univ _,rfl⟩
    | marker m =>
        obtain ⟨b,hb⟩ := mark_surjective m
        apply Finset.mem_union_left
        apply Finset.mem_union_left
        exact Finset.mem_image.2 ⟨some b,Finset.mem_univ _,by simp only [hb,Local.rename]⟩
    | predicate p =>
        apply predicate_rename_mem P τ role e he p (typed.predicates p ha)
        intro φ hp
        subst p
        exact hplain φ ha
  · constructor
    · rintro g ⟨a,ha,rfl⟩
      obtain ⟨s,r,j,hr,hj⟩ := typed.guards a ha
      obtain ⟨i,hi⟩ := relation_surjective a.relation
      apply Finset.mem_image.2
      refine ⟨(s,r,i,j),Finset.mem_univ _,?_⟩
      cases a
      dsimp only at hr hj hi
      simp only [Guard.rename,he _ _ _ hr,hi,←hj]
    · intro c a hc
      change S.resets.value (e.symm c)=some a at hc
      obtain ⟨s,r,j,hr,hj⟩ := typed.resets (e.symm c) a hc
      have hh := he (e.symm c) s r hr
      simp only [Equiv.apply_symm_apply] at hh
      apply Finset.mem_image.2
      exact ⟨(s,r,j),Finset.mem_univ _,by simp only [←hh,hj]⟩

/-- Both actual current and next components are included, with no semantic
predicate replacing literal inventory membership. -/
theorem TransitionTyped.rename_within
    {τ : Slot → FiniteInventory.Triple Clock Var} {role : ClockRoles Clock Slot}
    {F : Section3.TransitionForm Clock Var} (typed : TransitionTyped τ role F)
    (P : Finset (Formula Var)) (e : Equiv.Perm Clock)
    (he : ∀c s r,role c=some (s,r) → e c=FiniteInventory.clockAt (τ s) r)
    (hplain : ∀φ,Local.predicate (.plain φ)∈F.current.locals → φ∈P)
    (hplainNext : ∀N,F.nextPart=some N → ∀φ,Local.predicate (.plain φ)∈N.locals → φ∈P) :
    FiniteInventory.TransitionWithin (FiniteInventory.locals P τ) (FiniteInventory.guards τ)
      (FiniteInventory.resets τ) (renameTransition e F) := by
  refine ⟨typed.current.rename_within P e he hplain,?_⟩
  intro N hn
  cases hnext : F.nextPart with
  | none => simp [renameTransition,hnext] at hn
  | some M =>
      have hN : N=M.rename e := by simpa [renameTransition,hnext] using hn.symm
      subst N
      exact (typed.next M hnext).rename_within P e he (hplainNext M hnext)
end SlotFrame
end STLTableau.Section4.Finiteness
