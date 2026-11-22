import STLTableaux.Finiteness.ClockAllocation.SelectedNameEvents

/-! A clock that occurs in a branch but is absent from its source predicate
comes from a fresh-clock introduction in the same derivation. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

private def choiceEvent
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
    have hp : Local.predicate choice.p∈owned.locals := by rw [choice.split];simp
    exact choice.fresh_name (owned.covers_input (Or.inl (Or.inl (owned.local_clock_support hp hc))))
  used := hx

private theorem body_new_name
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} (choice : OrdinaryChoice E owned)
    (a : Clock) (ha : a∈syntaxClocks choice.B)
    (hnew : a∉syntaxClocks (.predicate choice.p)) : a=choice.x := by
  exact (choice.branch.syntaxClocks_subset_source_union_singleton choice.x choice.reset_support ha).resolve_left hnew

/-- If a recorded branch uses a clock absent from its source predicate, the
same derivation records the introduction of that clock for this branch. -/
theorem SelectedTree.ledger_body_name_producer
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    {entry : RawLedgerEntry (Clock := Clock) (Var := Var)} (he : entry∈T.rawLedger)
    (a : Clock) (ha : a∈syntaxClocks entry.body)
    (hnew : a∉syntaxClocks (.predicate entry.source)) :
    ∃event∈T.usedNameEvents,event.toRawLedgerEntry=entry ∧ event.x=a := by
  classical
  induction T generalizing entry with
  | zero => cases he
  | ordinary owned choice tail ih =>
      rcases List.mem_cons.mp he with hhead | he
      · subst entry
        have hax := body_new_name choice a ha hnew
        have hx : choice.x∈syntaxClocks choice.B := hax ▸ ha
        refine ⟨choiceEvent choice hx,?_,rfl,hax.symm⟩
        simp only [SelectedTree.usedNameEvents,dif_pos hx]
        exact List.mem_cons_self
      · obtain ⟨event,he,heq,hx⟩ := ih he ha hnew
        refine ⟨event,?_,heq,hx⟩
        by_cases hc : choice.x∈syntaxClocks choice.B <;>
          simp [SelectedTree.usedNameEvents,hc,he]
  | required owned choice tail ih => exact ih he ha hnew
  | optional owned choice upper forced tail ih =>
      rcases List.mem_cons.mp he with hhead | he
      · subst entry
        have hax := body_new_name upper a ha hnew
        have hx : upper.x∈syntaxClocks upper.B := hax ▸ ha
        refine ⟨choiceEvent upper hx,?_,rfl,hax.symm⟩
        simp only [SelectedTree.usedNameEvents,dif_pos hx]
        exact List.mem_cons_self
      · obtain ⟨event,he,heq,hx⟩ := ih he ha hnew
        refine ⟨event,?_,heq,hx⟩
        by_cases hc : upper.x∈syntaxClocks upper.B <;>
          simp [SelectedTree.usedNameEvents,hc,he]
end STLTableau.Section4.Finiteness
