import STLTableaux.Finiteness.Derivation.Selection.SelectedBranchHistory

/-! Exact clock-name support of actual raw expansion branches. Every name
outside the source is reset-bound, and every clocked current child uses only
introduced names. These are syntactic facts; next children remain frozen and
are not included in currentPredicates. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

set_option maxHeartbeats 2400000 in
set_option linter.unusedSimpArgs false in
private theorem finite_raw_support
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : STLTableau.ConcreteRule p R) {B : STLTableau.Judgement Clock Var} (hm : B ∈ R.branches) :
    syntaxClocks (Judgement.ofFinite B) ⊆
      syntaxClocks (.predicate (Predicate.ofFinite p)) ∪ resetNames (Judgement.ofFinite B) ∧
    ∀ q ∈ (Judgement.ofFinite B).currentPredicates,
      syntaxClocks (.predicate q) ⊆
        resetNames (Judgement.ofFinite B) \ syntaxClocks (.predicate (Predicate.ofFinite p)) := by
  classical
  (cases hr <;>
    simp only [ExpansionRule.plainAnd,ExpansionRule.plainOr,ExpansionRule.plainUntil,
      ExpansionRule.plainRelease,ExpansionRule.openEventually,ExpansionRule.openAlways,
      ExpansionRule.upperAlways,ExpansionRule.boundedAlways,ExpansionRule.upperEventually,
      ExpansionRule.boundedEventually,List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hm <;>
    (try split_ifs at hm) <;>
    (try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hm) <;>
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals simp_all [syntaxClocks,resetNames,Section3.Judgement.ofFinite,
    Section3.Judgement.currentPredicates,Predicate.ofFinite,
    ExpansionRule.upperAlways_defer,ExpansionRule.upperAlways_check,
    ExpansionRule.boundedAlways_defer,ExpansionRule.boundedAlways_check,ExpansionRule.boundedAlways_finish,
    ExpansionRule.upperEventually_defer,ExpansionRule.upperEventually_check,
    ExpansionRule.boundedEventually_defer,ExpansionRule.boundedEventually_check,ExpansionRule.boundedEventually_finish,
    STLTableau.Judgement.markedLT_eq_clock,STLTableau.Judgement.markedGT_eq_clock,
    ClockResetSet.clocks_union,Set.subset_def]

set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
private theorem infinite_raw_support
    {p : UnboundedClocked.Predicate Clock Var} {Bs : List (UnboundedClocked.Node Clock Var)}
    (hr : UnboundedClocked.ConcreteRule p Bs) {B : UnboundedClocked.Node Clock Var} (hm : B ∈ Bs) :
    syntaxClocks (Judgement.ofUnbounded B) ⊆
      syntaxClocks (.predicate (Predicate.ofUnbounded p)) ∪ resetNames (Judgement.ofUnbounded B) ∧
    ∀ q ∈ (Judgement.ofUnbounded B).currentPredicates,
      syntaxClocks (.predicate q) ⊆
        resetNames (Judgement.ofUnbounded B) \ syntaxClocks (.predicate (Predicate.ofUnbounded p)) := by
  classical
  (cases hr <;>
    simp only [UnboundedClocked.upperAlwaysBranches,UnboundedClocked.boundedAlwaysBranches,
      UnboundedClocked.upperEventuallyBranches,UnboundedClocked.boundedEventuallyBranches,
      List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hm <;>
    (try split_ifs at hm) <;>
    (try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hm) <;>
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals simp_all [syntaxClocks,resetNames,Section3.Judgement.ofUnbounded,
    Section3.Judgement.currentPredicates,Predicate.ofUnbounded,
    UnboundedClocked.upperAlwaysDefer,UnboundedClocked.upperAlwaysCheck,
    UnboundedClocked.boundedAlwaysDefer,UnboundedClocked.boundedAlwaysCheck,
    UnboundedClocked.upperEventuallyDefer,UnboundedClocked.upperEventuallyCheck,
    UnboundedClocked.boundedEventuallyDefer,UnboundedClocked.boundedEventuallyCheck,
    UnboundedClocked.boundedEventuallyFinish,UnboundedClocked.alwaysWait,UnboundedClocked.alwaysLast,
    UnboundedClocked.Node.lt,UnboundedClocked.Node.gt,ClockResetSet.clocks_union,Set.subset_def]

/-- Whole raw syntax uses only source names and names bound by actual resets.
This includes current/next guards and reset bindings, not merely free clocks. -/
theorem RawBranch.syntaxClocks_subset_source_union_resets
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B) :
    syntaxClocks B ⊆ syntaxClocks (.predicate p) ∪ resetNames B := by
  cases h with
  | finite hr hm => exact (finite_raw_support hr hm).1
  | infinite hr hm => exact (infinite_raw_support hr hm).1
  | opening c m kind a φ =>
    simp [syntaxClocks,resetNames,Judgement.ofUnbounded,UnboundedClocked.opening,Predicate.ofUnbounded]

/-- Current predicates are unclocked or in the `↑` form introduced by an opening
reset. Any clock of a current predicate is introduced by that branch. -/
theorem RawBranch.current_child_new
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B)
    (q : Predicate Clock Var) (hq : q ∈ B.currentPredicates) :
    syntaxClocks (.predicate q) ⊆ resetNames B \ syntaxClocks (.predicate p) := by
  cases h with
  | finite hr hm => exact (finite_raw_support hr hm).2 q hq
  | infinite hr hm => exact (infinite_raw_support hr hm).2 q hq
  | opening c m kind a φ =>
    have he : q = .upper c m kind (.unbounded a) φ := by
      simpa [UnboundedClocked.opening,Judgement.ofUnbounded,
        Section3.Judgement.currentPredicates,Predicate.ofUnbounded] using hq
    subst q
    simp [syntaxClocks,resetNames,Judgement.ofUnbounded,UnboundedClocked.opening]

/-- The selected history theorem's reset bound controls ALL branch names. -/
theorem RawBranch.syntaxClocks_subset_source_union_singleton
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B) (x : Clock)
    (hr : resetNames B ⊆ syntaxClocks (.predicate p) ∪ {x}) :
    syntaxClocks B ⊆ syntaxClocks (.predicate p) ∪ {x} := by
  intro d hd
  rcases h.syntaxClocks_subset_source_union_resets hd with hs | hb
  · exact Or.inl hs
  · exact hr hb

theorem RawBranch.current_child_subset_singleton
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B) (x : Clock)
    (hr : resetNames B ⊆ syntaxClocks (.predicate p) ∪ {x})
    (q : Predicate Clock Var) (hq : q ∈ B.currentPredicates) :
    syntaxClocks (.predicate q) ⊆ {x} := by
  intro d hd
  have hnew := h.current_child_new q hq hd
  rcases hr hnew.1 with hs | hx
  · exact False.elim (hnew.2 hs)
  · exact hx

/-- History exclusion for introduced resets therefore excludes every new
syntactic occurrence, including names occurring only in a future guard. -/
theorem RawBranch.new_support_disjoint_history
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B)
    (W : Set Clock) (hr : Disjoint (resetNames B \ syntaxClocks (.predicate p)) W) :
    Disjoint (syntaxClocks B \ syntaxClocks (.predicate p)) W := by
  apply Set.disjoint_left.2
  intro d hd hdW
  rcases h.syntaxClocks_subset_source_union_resets hd.1 with hs | hb
  · exact hd.2 hs
  · exact Set.disjoint_left.1 hr ⟨hb,hd.2⟩ hdW

theorem RawBranch.current_child_disjoint_history
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B)
    (W : Set Clock) (hr : Disjoint (resetNames B \ syntaxClocks (.predicate p)) W)
    (q : Predicate Clock Var) (hq : q ∈ B.currentPredicates) :
    Disjoint (syntaxClocks (.predicate q)) W :=
  hr.mono_left (h.current_child_new q hq)

/-- A selected branch uses only the source clocks and the selected fresh
clock. Its current children avoid the given history. -/
theorem exists_selected_branch_history_with_support [Infinite Clock]
    (p : Predicate Clock Var) (hp : p.Ready) (hn : ¬ p.IsAtomic) (Γ : MixedJ Clock Var)
    (W : Set Clock) (hW : W.Finite)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.val < P.size, p.Invariant σ P α k hk)
    (hst : σ.StablePartition p.formula P)
    (hs : Judgement.holds σ P α k (.predicate p)) :
    ∃ (x : Clock) (B : MixedJ Clock Var) (F : Section3.TransitionForm Clock Var),
      x ∉ W ∪ syntaxClocks Γ ∪ syntaxClocks (.predicate p) ∧
      RawBranch p B ∧ FreshFor p B Γ ∧
      resetNames B ⊆ syntaxClocks (.predicate p) ∪ {x} ∧
      syntaxClocks B ⊆ syntaxClocks (.predicate p) ∪ {x} ∧
      Disjoint (syntaxClocks B \ syntaxClocks (.predicate p)) W ∧
      (∀ q ∈ B.currentPredicates, Disjoint (syntaxClocks (.predicate q)) W) ∧
      (∀ q ∈ B.currentPredicates, syntaxClocks (.predicate q) ⊆ {x}) ∧
      SafeNormalization B F ∧ F.current.guards = ∅ ∧
      F.holds σ P α k ∧ F.EvaluatedInvariant σ P α k ∧ F.UnderlyingStable σ P := by
  obtain ⟨x,B,F,hx,hB,hfresh,hreset,hhistory,hsafe,hguards,htrue,hfull,hstable⟩ :=
    exists_selected_branch_history p hp hn Γ W hW σ P α k hi hst hs
  exact ⟨x,B,F,hx,hB,hfresh,hreset,hB.syntaxClocks_subset_source_union_singleton x hreset,
    hB.new_support_disjoint_history W hhistory,
    hB.current_child_disjoint_history W hhistory,hB.current_child_subset_singleton x hreset,
    hsafe,hguards,htrue,hfull,hstable⟩

end STLTableau.Section4.Finiteness
