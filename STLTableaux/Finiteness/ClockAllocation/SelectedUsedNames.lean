import STLTableaux.Finiteness.ClockAllocation.SlotFrame
import STLTableaux.Finiteness.Derivation.Selection.SelectedClockSupport

/-! Lists the fresh clocks that occur in a selected derivation. A fresh name
chosen for a branch where it does not occur can be reused and consumes no
space in the fixed clock set. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]
attribute [local instance] Classical.propDecidable

noncomputable def SelectedTree.usedFreshClocks
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) : List Clock := by
  classical
  exact match T with
  | .zero _ _ => []
  | .ordinary _ choice tail =>
      if choice.x∈syntaxClocks choice.B then choice.x::tail.usedFreshClocks else tail.usedFreshClocks
  | .required _ _ tail => tail.usedFreshClocks
  | .optional _ _ upper _ tail =>
      if upper.x∈syntaxClocks upper.B then upper.x::tail.usedFreshClocks else tail.usedFreshClocks

private theorem used_in_child_budget
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} (choice : OrdinaryChoice E owned)
    (hx : choice.x∈syntaxClocks choice.B) : choice.x∈choice.childW := by
  have hs : choice.x∈syntaxClocks (ordinarySelectedInput R (choice.left++choice.right) choice.B
      (foldCurrent ((choice.left++choice.right).map Local.toJudgement ++
        owned.nextInputs.map Section3.Judgement.next))) := by
    cases hf : foldCurrent ((choice.left++choice.right).map Local.toJudgement ++
        owned.nextInputs.map Section3.Judgement.next) with
    | none => exact hx
    | some Γ => exact Or.inl hx
  exact choice.child.covers_input (Or.inl (Or.inl hs))

theorem SelectedTree.usedFreshClocks_outside
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) : ∀c∈T.usedFreshClocks,c∉W := by
  classical
  induction T with
  | zero => simp [SelectedTree.usedFreshClocks]
  | ordinary owned choice tail ih =>
      intro c hc
      by_cases hx : choice.x∈syntaxClocks choice.B
      · simp only [SelectedTree.usedFreshClocks,if_pos hx,List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact choice.fresh_name
        · exact fun hw => ih c hc (choice.grows hw)
      · simp only [SelectedTree.usedFreshClocks,if_neg hx] at hc
        exact fun hw => ih c hc (choice.grows hw)
  | required owned choice tail ih => exact ih
  | optional owned choice upper forced tail ih =>
      intro c hc
      by_cases hx : upper.x∈syntaxClocks upper.B
      · simp only [SelectedTree.usedFreshClocks,if_pos hx,List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact upper.fresh_name
        · exact fun hw => ih c hc (upper.grows hw)
      · simp only [SelectedTree.usedFreshClocks,if_neg hx] at hc
        exact fun hw => ih c hc (upper.grows hw)

theorem SelectedTree.usedFreshClocks_nodup
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) : T.usedFreshClocks.Nodup := by
  classical
  induction T with
  | zero => simp [SelectedTree.usedFreshClocks]
  | ordinary owned choice tail ih =>
      by_cases hx : choice.x∈syntaxClocks choice.B
      · simp only [SelectedTree.usedFreshClocks,if_pos hx,List.nodup_cons]
        exact ⟨fun h => tail.usedFreshClocks_outside choice.x h (used_in_child_budget choice hx),ih⟩
      · simpa only [SelectedTree.usedFreshClocks,if_neg hx] using ih
  | required owned choice tail ih => exact ih
  | optional owned choice upper forced tail ih =>
      by_cases hx : upper.x∈syntaxClocks upper.B
      · simp only [SelectedTree.usedFreshClocks,if_pos hx,List.nodup_cons]
        exact ⟨fun h => tail.usedFreshClocks_outside upper.x h (used_in_child_budget upper hx),ih⟩
      · simpa only [SelectedTree.usedFreshClocks,if_neg hx] using ih

private theorem ordinary_used_lift
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} (choice : OrdinaryChoice E owned) (xs : List Clock) :
    inputClockSupport (ordinarySelectedInput R (choice.left++choice.right) choice.B
      (foldCurrent ((choice.left++choice.right).map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next))) choice.childR ∪ {c|c∈xs} ⊆ inputClockSupport J R ∪
      {c|c∈if choice.x∈syntaxClocks choice.B then choice.x::xs else xs} := by
  classical
  have hp : Local.predicate choice.p∈owned.locals := by rw [choice.split]; simp
  have hs := owned.local_clock_support hp
  intro c hc
  rcases hc with hc | hc
  · rcases choice.input_clock_support_branch hc with hc | hc
    · exact Or.inl hc
    · by_cases hx : choice.x∈syntaxClocks choice.B
      · rcases choice.branch.syntaxClocks_subset_source_union_singleton choice.x choice.reset_support hc with hc | hc
        · exact Or.inl (Or.inl (hs hc))
        · have he : c=choice.x := hc
          exact Or.inr (by simp only [if_pos hx,List.mem_cons]; exact Or.inl he)
      · rcases choice.branch.syntaxClocks_subset_source_union_singleton choice.x choice.reset_support hc with hs' | he
        · exact Or.inl (Or.inl (hs hs'))
        · have he' : c=choice.x := he
          exact False.elim (hx (he' ▸ hc))
  · exact Or.inr (by split_ifs; exact List.mem_cons_of_mem _ hc; exact hc)

/-- The same full/erased outputs are covered by incoming names and ACTUALLY
 used generated names, not dummy freshness witnesses. -/
theorem SelectedTree.used_syntax_clock_support
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) :
    syntaxClocks H⊆inputClockSupport J R ∪ {c|c∈T.usedFreshClocks} ∧
      syntaxClocks Er⊆inputClockSupport J R ∪ {c|c∈T.usedFreshClocks} := by
  classical
  induction T with
  | zero owned hz =>
      simp only [SelectedTree.usedFreshClocks,List.not_mem_nil,Set.setOf_false,Set.union_empty]
      exact ⟨owned.canonical_clock_support,owned.canonical_clock_support⟩
  | ordinary owned choice tail ih =>
      simp only [SelectedTree.usedFreshClocks]
      have hLift := ordinary_used_lift choice tail.usedFreshClocks
      have hp : Local.predicate choice.p∈owned.locals := by rw [choice.split]; simp
      constructor
      · apply owned.outside_clock_support _ Set.subset_union_left
        exact Set.union_subset ((owned.local_clock_support hp).trans (fun c hc=>Or.inl (Or.inl hc))) (ih.1.trans hLift)
      · exact owned.outside_clock_support _ Set.subset_union_left (ih.2.trans hLift)
  | required owned choice tail ih =>
      simp only [SelectedTree.usedFreshClocks]
      have hLift := Set.union_subset_union choice.input_clock_support
        (Set.Subset.rfl (s:={c|c∈tail.usedFreshClocks}))
      exact ⟨owned.outside_clock_support _ Set.subset_union_left (ih.1.trans hLift),
        owned.outside_clock_support _ Set.subset_union_left (ih.2.trans hLift)⟩
  | optional owned choice upper forced tail ih =>
      simp only [SelectedTree.usedFreshClocks]
      have hb := choice.input_clock_support
      have hLift := (ordinary_used_lift upper tail.usedFreshClocks).trans
        (Set.union_subset_union hb Set.Subset.rfl)
      have hInput := hb.trans (Set.subset_union_left (t:={c|c∈if upper.x∈syntaxClocks upper.B then upper.x::tail.usedFreshClocks else tail.usedFreshClocks}))
      have hp : Local.predicate upper.p∈choice.child.locals := by rw [upper.split]; simp
      have hSource := (choice.child.local_clock_support hp).trans (Set.subset_union_left.trans hInput)
      constructor
      · apply owned.outside_clock_support _ Set.subset_union_left
        apply choice.child.outside_clock_support _ hInput
        exact Set.union_subset hSource (ih.1.trans hLift)
      · apply owned.outside_clock_support _ Set.subset_union_left
        exact choice.child.outside_clock_support _ hInput (ih.2.trans hLift)

theorem SelectedTree.used_normalized_clock_support
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) {F : Section3.TransitionForm Clock Var}
    (hSafe : SafeNormalization H F) :
    F.allClocks⊆inputClockSupport J R ∪ {c|c∈T.usedFreshClocks} :=
  hSafe.allClocks_subset_syntax.trans T.used_syntax_clock_support.1

end STLTableau.Section4.Finiteness
