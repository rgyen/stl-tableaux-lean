import STLTableaux.Finiteness.ClockAllocation.SelectedUsedNames
import STLTableaux.Finiteness.Derivation.Branches.RawBranchUpperShape

/-! For each fresh clock used in a selected derivation, records the source
predicate and the branch in which the clock occurs. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]
attribute [local instance] Classical.propDecidable

structure UsedNameEvent extends RawLedgerEntry (Clock := Clock) (Var := Var) where
  x : Clock
  reset_support : resetNames body⊆syntaxClocks (.predicate source) ∪ {x}
  not_source : x∉syntaxClocks (.predicate source)
  used : x∈syntaxClocks body

private def eventOfChoice
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} (choice : OrdinaryChoice E owned)
    (hx : choice.x∈syntaxClocks choice.B) : UsedNameEvent (Clock := Clock) (Var := Var) where
  source := choice.p
  body := choice.B
  actual := choice.branch
  x := choice.x
  reset_support := choice.reset_support
  not_source := by
    intro hc
    have hp : Local.predicate choice.p∈owned.locals := by rw [choice.split]; simp
    exact choice.fresh_name (owned.covers_input (Or.inl (Or.inl (owned.local_clock_support hp hc))))
  used := hx

noncomputable def SelectedTree.usedNameEvents
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) : List (UsedNameEvent (Clock := Clock) (Var := Var)) :=
  match T with
  | .zero _ _ => []
  | .ordinary _ choice tail =>
      if hx : choice.x∈syntaxClocks choice.B then eventOfChoice choice hx::tail.usedNameEvents else tail.usedNameEvents
  | .required _ _ tail => tail.usedNameEvents
  | .optional _ _ upper _ tail =>
      if hx : upper.x∈syntaxClocks upper.B then eventOfChoice upper hx::tail.usedNameEvents else tail.usedNameEvents

theorem SelectedTree.usedNameEvents_names
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) : T.usedNameEvents.map (fun e=>e.x)=T.usedFreshClocks := by
  induction T with
  | zero => rfl
  | ordinary owned choice tail ih =>
      by_cases hx : choice.x∈syntaxClocks choice.B <;>
        simp [SelectedTree.usedNameEvents,SelectedTree.usedFreshClocks,hx,eventOfChoice,ih]
  | required owned choice tail ih => exact ih
  | optional owned choice upper forced tail ih =>
      by_cases hx : upper.x∈syntaxClocks upper.B <;>
        simp [SelectedTree.usedNameEvents,SelectedTree.usedFreshClocks,hx,eventOfChoice,ih]

theorem SelectedTree.usedNameEvents_name_injective
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    {e f : UsedNameEvent (Clock := Clock) (Var := Var)}
    (he : e∈T.usedNameEvents) (hf : f∈T.usedNameEvents) (h : e.x=f.x) : e=f := by
  have hn : (T.usedNameEvents.map (fun e=>e.x)).Nodup := by
    rw [T.usedNameEvents_names]
    exact T.usedFreshClocks_nodup
  exact List.inj_on_of_nodup_map hn he hf h

theorem SelectedTree.usedNameEvents_ledger
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    {e : UsedNameEvent (Clock := Clock) (Var := Var)} (he : e∈T.usedNameEvents) :
    e.toRawLedgerEntry∈T.rawLedger := by
  induction T with
  | zero => cases he
  | ordinary owned choice tail ih =>
      by_cases hx : choice.x∈syntaxClocks choice.B
      · simp only [SelectedTree.usedNameEvents,dif_pos hx,List.mem_cons] at he
        rcases he with rfl | he
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih he)
      · simp only [SelectedTree.usedNameEvents,dif_neg hx] at he
        exact List.mem_cons_of_mem _ (ih he)
  | required owned choice tail ih => exact ih he
  | optional owned choice upper forced tail ih =>
      by_cases hx : upper.x∈syntaxClocks upper.B
      · simp only [SelectedTree.usedNameEvents,dif_pos hx,List.mem_cons] at he
        rcases he with rfl | he
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih he)
      · simp only [SelectedTree.usedNameEvents,dif_neg hx] at he
        exact List.mem_cons_of_mem _ (ih he)

private theorem opening_choice_name
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} (choice : OrdinaryChoice E owned)
    (c : Clock) (m : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hq : Predicate.upper c m kind I φ∈choice.B.currentPredicates) :
    choice.x=c ∧ choice.x∈syntaxClocks choice.B := by
  have hc : c=choice.x := choice.branch.current_child_subset_singleton choice.x choice.reset_support
    (.upper c m kind I φ) hq (by simp [syntaxClocks])
  obtain ⟨_,hbody⟩ := choice.branch.current_upper_opening c m kind I φ hq
  refine ⟨hc.symm,?_⟩
  rw [hbody,← hc]
  simp [syntaxClocks]

/-- Every actual opening left has its unique used-name producer in this same
 tree, retaining the source-bearing raw entry and the exact left name. -/
theorem SelectedTree.opening_name_producer
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    {entry : RawLedgerEntry (Clock := Clock) (Var := Var)} (he : entry∈T.rawLedger)
    (c : Clock) (m : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hq : Predicate.upper c m kind I φ∈entry.body.currentPredicates) :
    ∃e∈T.usedNameEvents,e.toRawLedgerEntry=entry ∧ e.x=c := by
  induction T generalizing entry with
  | zero => cases he
  | ordinary owned choice tail ih =>
      rcases List.mem_cons.1 he with he | he
      · subst entry
        obtain ⟨hc,hx⟩ := opening_choice_name choice c m kind I φ hq
        exact ⟨eventOfChoice choice hx,by simp [SelectedTree.usedNameEvents,hx],rfl,hc⟩
      · obtain ⟨e,he,heq,hc⟩ := ih he hq
        refine ⟨e,?_,heq,hc⟩
        by_cases hx : choice.x∈syntaxClocks choice.B <;>
          simp [SelectedTree.usedNameEvents,hx,he]
  | required owned choice tail ih => exact ih he hq
  | optional owned choice upper forced tail ih =>
      rcases List.mem_cons.1 he with he | he
      · subst entry
        obtain ⟨hc,hx⟩ := opening_choice_name upper c m kind I φ hq
        exact ⟨eventOfChoice upper hx,by simp [SelectedTree.usedNameEvents,hx],rfl,hc⟩
      · obtain ⟨e,he,heq,hc⟩ := ih he hq
        refine ⟨e,?_,heq,hc⟩
        by_cases hx : upper.x∈syntaxClocks upper.B <;>
          simp [SelectedTree.usedNameEvents,hx,he]

end STLTableau.Section4.Finiteness
