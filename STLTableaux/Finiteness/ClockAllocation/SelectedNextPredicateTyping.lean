import STLTableaux.Finiteness.ClockAllocation.SelectedSourceRoleTyping
import STLTableaux.Finiteness.ClockAllocation.SelectedClockedBodyRoles
import STLTableaux.Finiteness.ClockAllocation.SupportedClockPermutations

/-! Actual normalized next predicates acquire their family and left owner from
an actual raw continuation. Their right name is typed in that SAME owner. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var Slot : Type*} [DecidableEq Clock] [Fintype Slot]

omit [DecidableEq Clock] [Fintype Slot] in
private theorem current_predicate_support {K : MixedJ Clock Var} {p : Predicate Clock Var}
    (hp : p∈K.currentPredicates) : syntaxClocks (.predicate p)⊆syntaxClocks K := by
  induction K with
  | terminal | marker | clock | next => cases hp
  | predicate q => have he : p=q := hp;subst p;exact Set.Subset.rfl
  | conj J K ih ik =>
    rcases hp with hp | hp
    · exact (ih hp).trans Set.subset_union_left
    · exact (ik hp).trans Set.subset_union_right
  | reset R K ih => exact (ih hp).trans Set.subset_union_right

omit [DecidableEq Clock] [Fintype Slot] in
private theorem conjunct_clock_support {B K : MixedJ Clock Var} (h : Conjunct B K) :
    syntaxClocks K⊆syntaxClocks B := by
  induction h with
  | here => exact Set.Subset.rfl
  | left h ih => exact ih.trans Set.subset_union_left
  | right h ih => exact ih.trans Set.subset_union_right

variable {N : Section3.StateForm Clock Var} {J : MixedJ Clock Var} {W : Set Clock}
    {owned : OwnedPending J N.resets W} {H Er : MixedJ Clock Var}
    {τ : Slot→FiniteInventory.Triple Clock Var} {incoming : Equiv.Perm Clock}
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}

/-- The actual selected output's next predicate is typed without an assumed
next-state typing certificate. Initial literal-next payloads are absent in the
actual canonical state-input presentation. -/
theorem SelectedTree.retrospective_next_predicates_typed
    (O : InputOrigins σ P α k N)
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (root : Formula Var) (hBelow : ∀entry∈T.rawLedger,entry.source.formula≼root)
    (hInput : SafeNormalization J (.ofState N))
    (hLocal : ∀l,l∈owned.locals↔l∈N.locals) (hnil : owned.nextInputs=[])
    {F : Section3.TransitionForm Clock Var} (hFull : SafeNormalization H F)
    (frame : SlotFrame τ N incoming)
    (newSlot : ↥(Finiteness.rootTemporalSignatures root)→Slot)
    (hFamily : ∀sig,SlotFrame.slotFamily τ (newSlot sig)=sig.val)
    (hnew : Function.Injective newSlot)
    (hfree : ∀sig,newSlot sig∉SlotFrame.occupied frame.role)
    (M : Section3.StateForm Clock Var) (hn : F.nextPart=some M) :
    ∀p,Local.predicate p∈M.locals →
      SlotFrame.PredicateTyped τ (retrospectiveRoleMap root T frame newSlot) p := by
  intro p hp
  cases p with
  | plain => trivial
  | upper c m kind I φ =>
    rcases (T.normalized_next_provenance hFull hn _).1 hp with hold | ⟨entry,he,K,hK,hpK⟩
    · simp [hnil] at hold
    · exact False.elim (entry.actual.literal_next_no_upper hK c m kind I φ hpK)
  | bounded c d m q kind I φ =>
    obtain ⟨entry,he,K,hK,hpK⟩ : ∃entry∈T.rawLedger,∃K,Conjunct entry.body (.next K) ∧
        Predicate.bounded c d m q kind I φ∈K.currentPredicates := by
      rcases (T.normalized_next_provenance hFull hn _).1 hp with hold | h
      · simp [hnil] at hold
      · exact h
    have hsource := entry.actual.next_bounded_source hK c d m q kind I φ hpK
    have hc : ClockedLeft entry.source c kind I φ := by
      rcases hsource with ⟨b,hs,_⟩ | ⟨b,hs,_⟩
      · exact Or.inl ⟨b,hs⟩
      · exact Or.inr ⟨d,b,q,hs⟩
    have hcd : c≠d := by rcases hsource with ⟨_,_,h⟩ | ⟨_,_,h⟩ <;> exact h
    obtain ⟨s,left,hfamily⟩ := T.ledger_clocked_left_coverage O root hBelow hLocal frame newSlot hFamily
      entry he c kind I φ hc
    have hdBody : d∈syntaxClocks entry.body :=
      conjunct_clock_support hK (current_predicate_support hpK (by simp [syntaxClocks]))
    have hdF : d∈F.allClocks := by
      rw [transition_support_eq,hn]
      right
      left
      right
      exact ⟨.predicate (.bounded c d m q kind I φ),hp,by
        simp [Local.freeClocks,Local.toJudgement,Section3.Judgement.freeClocks]⟩
    have hdSupport := T.used_normalized_clock_support hFull hdF
    rw [input_clock_support_of_safe hInput] at hdSupport
    obtain ⟨t,r,role⟩ := (T.retrospective_domain O root hBelow hLocal frame newSlot hFamily d).1 hdSupport
    have howner : t=s := T.clocked_body_role_owner hInput hLocal entry he c kind I φ hc s left d hdBody t r role
    subst t
    have hr : r≠0 := by
      intro hr
      have heq := RetrospectiveRole.injective_of_eq hnew hfree role left.role_zero (by simp [hr])
      exact hcd heq.symm
    have hright : r=1 ∨r=2 := by fin_cases r <;> simp_all
    have hcl := (retrospectiveRoleMap_iff root T hInput frame newSlot c s 0).2 left.role_zero
    have hdr := (retrospectiveRoleMap_iff root T hInput frame newSlot d s r).2 role
    have hk : (τ s).kind=kind := congrArg Prod.fst hfamily
    have hI : (τ s).interval=I := congrArg (fun t=>t.2.1) hfamily
    have hφ : (τ s).body=φ := congrArg (fun t=>t.2.2) hfamily
    exact ⟨s,r,hright,hcl,hdr,hk.symm,hI.symm,hφ.symm⟩
end STLTableau.Section4.Finiteness
