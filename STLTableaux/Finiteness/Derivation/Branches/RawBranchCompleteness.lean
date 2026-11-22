import STLTableaux.Finiteness.Derivation.DerivationReady
import STLTableaux.Closure.Correctness.FaithfulClosureCompleteness

/-! Actual branch selection on the same signal and stable partition. This
module does not assume existence of a satisfied branch or a representative
path. The full evaluated invariant includes eventuality clauses for no past satisfaction. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

/-- Readiness is syntactic admission of an actual rule family; the arbitrary
branch obtained here carries no satisfaction hypothesis. -/
theorem RawBranch.exists_of_ready [DecidableEq Clock] [Nontrivial Clock]
    (p : Predicate Clock Var) (hp : p.Ready) (hn : ¬ p.IsAtomic) :
    ∃ B, RawBranch p B := by
  obtain ⟨B,hB⟩ := ConcreteMixed.catalogue.branch_exists p hp.admitted hn ClockResetSet.empty
  rcases hB with h | h | h
  · obtain ⟨p₀,R,raw,F,rfl,hr,hm,_,_⟩ := h
    exact ⟨_,.finite hr hm⟩
  · obtain ⟨p₀,Bs,raw,F,rfl,hr,hm,_,_⟩ := h
    exact ⟨_,.infinite hr hm⟩
  · obtain ⟨c,m,kind,a,φ,F,rfl,_,_⟩ := h
    exact ⟨_,.opening c m kind a φ⟩

/-- From an actual syntactic rule family, select one branch satisfying both
its real judgement and every scoped full invariant. The supplied arbitrary
branch is not assumed satisfied and may be replaced. -/
theorem RawBranch.select_preserving [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, p.Invariant σ P α k hk)
    (hst : σ.StablePartition p.formula P)
    (hs : Judgement.holds σ P α k (.predicate p)) :
    ∃ C, RawBranch p C ∧ Judgement.holds σ P α k C ∧
      C.EvaluatedInvariant σ P α k ∧ C.UnderlyingStable σ P := by
  cases h with
  | @finite p₀ R rule B₀ _ =>
      have hi₀ : ∀ hk : k.1 < P.size, STLTableau.Invariant σ P α k hk p₀ := by
        intro hk
        cases p₀ <;> exact hi hk
      have hst₀ : σ.StablePartition p₀.formula P := by simpa using hst
      obtain ⟨C,hm,hC,hI⟩ := STLTableau.rule_complete_preserving rule σ P α k hi₀ hst₀
        ((Judgement.holds_ofFinite σ P α k (.predicate p₀)).1 hs)
      exact ⟨_,.finite rule hm,(Judgement.holds_ofFinite σ P α k C).2 hC,
        (Judgement.evaluatedInvariant_ofFinite σ P α k C).2 hI,
        GeneratorStability.finite_branch_stable rule hm σ P hst₀⟩
  | @infinite p₀ Bs rule B₀ _ =>
      have hi₀ : ∀ hk : k.1 < P.size, UnboundedClocked.Invariant σ P α k hk p₀ := by
        intro hk
        cases p₀ <;> exact hi hk
      have hst₀ : σ.StablePartition p₀.formula P := by simpa using hst
      obtain ⟨C,hm,hC,hI⟩ := UnboundedClocked.rule_complete_preserving rule σ P α k hi₀ hst₀
        ((Judgement.holds_ofUnbounded σ P α k (.predicate p₀)).1 hs)
      exact ⟨_,.infinite rule hm,(Judgement.holds_ofUnbounded σ P α k C).2 hC,
        (Judgement.evaluatedInvariant_ofUnbounded σ P α k C).2 hI,
        GeneratorStability.infinite_branch_stable rule hm σ P hst₀⟩
  | opening c m kind a φ =>
      obtain ⟨m',hm⟩ := (UnboundedClocked.opening_correct σ P α k c kind a φ).1
        ((Judgement.holds_ofUnbounded σ P α k (.plain _)).1 hs)
      exact ⟨_,.opening c m' kind a φ,(Judgement.holds_ofUnbounded σ P α k _).2 hm,
        (Judgement.evaluatedInvariant_ofUnbounded σ P α k _).2
          (UnboundedClocked.opening_preserves σ P α k c m' kind a φ hm),
        GeneratorStability.opening_branch_stable c m' kind a φ σ P hst⟩

/-- For a satisfied non-atomic input predicate with its invariant on a fully
stable partition, an expansion branch preserves satisfaction, the predicate
invariants, and stability of the underlying formulas. -/
theorem RawBranch.exists_preserving [DecidableEq Clock] [Nontrivial Clock]
    (p : Predicate Clock Var) (hp : p.Ready) (hn : ¬ p.IsAtomic)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, p.Invariant σ P α k hk)
    (hst : σ.StablePartition p.formula P)
    (hs : Judgement.holds σ P α k (.predicate p)) :
    ∃ B, RawBranch p B ∧ Judgement.holds σ P α k B ∧
      B.EvaluatedInvariant σ P α k ∧ B.UnderlyingStable σ P := by
  obtain ⟨B,hB⟩ := RawBranch.exists_of_ready p hp hn
  exact hB.select_preserving σ P α k hi hst hs

/-- The raw context includes only finitely many clock names, even in reset
bindings and future guards. -/
theorem syntaxClocks_finite (J : MixedJ Clock Var) : (syntaxClocks J).Finite := by
  induction J with
  | terminal => exact Set.finite_empty
  | marker => exact Set.finite_empty
  | clock => exact Set.finite_singleton _
  | predicate p => cases p with
    | plain => exact Set.finite_empty
    | upper => exact Set.finite_singleton _
    | bounded => exact (Set.finite_singleton _).insert _
  | next J ih => exact ih
  | reset R J ih => exact R.finite_domain.union ih
  | conj J K ih ig => exact ih.union ig

@[simp] theorem resetNames_finiteLT (c : Clock) (m : Marker) (a : NNReal) :
    resetNames (Judgement.ofFinite (STLTableau.Judgement.markedLT c m a) : MixedJ Clock Var) = ∅ := by
  cases m <;> rfl
@[simp] theorem resetNames_finiteGT (c : Clock) (m : Marker) (a : NNReal) :
    resetNames (Judgement.ofFinite (STLTableau.Judgement.markedGT c m a) : MixedJ Clock Var) = ∅ := by
  cases m <;> rfl
@[simp] theorem resetNames_infiniteLT (c : Clock) (m : Marker) (a : NNReal) :
    resetNames (Judgement.ofUnbounded (UnboundedClocked.Node.lt c m a) : MixedJ Clock Var) = ∅ := by
  cases m <;> rfl
@[simp] theorem resetNames_infiniteGT (c : Clock) (m : Marker) (a : NNReal) :
    resetNames (Judgement.ofUnbounded (UnboundedClocked.Node.gt c m a) : MixedJ Clock Var) = ∅ := by
  cases m <;> rfl

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1200000 in
/-- Reselect only fresh rule parameters; keep the actual source predicate.
Every branch of the chosen finite rule satisfies whole-context freshness. -/
theorem finite_fresh_rule_at [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : STLTableau.ConcreteRule p R) (Γ : MixedJ Clock Var) (x : Clock)
    (hx : x ∉ syntaxClocks Γ ∪ syntaxClocks (.predicate (Predicate.ofFinite p))) :
    ∃ R', STLTableau.ConcreteRule p R' ∧ ∀ B ∈ R'.branches,
      FreshFor (Predicate.ofFinite p) (Judgement.ofFinite B) Γ ∧
      resetNames (Judgement.ofFinite B) ⊆ syntaxClocks (.predicate (Predicate.ofFinite p)) ∪ {x} := by
  classical
  have hxΓ : x ∉ syntaxClocks Γ := fun h => hx (Or.inl h)
  have hxp : x ∉ syntaxClocks (.predicate (Predicate.ofFinite p)) := fun h => hx (Or.inr h)
  cases hr <;> first
    | refine ⟨_,.plainAnd _ _,?_⟩
    | refine ⟨_,.plainOr _ _,?_⟩
    | refine ⟨_,.plainUntil _ _,?_⟩
    | refine ⟨_,.plainRelease _ _,?_⟩
    | refine ⟨_,.openEventually x _ _,?_⟩
    | refine ⟨_,.openAlways x _ _,?_⟩
    | refine ⟨_,.upperAlways _ x _ _ _ (by
        intro he; apply hxp; simp [Predicate.ofFinite,syntaxClocks,he]),?_⟩
    | refine ⟨_,.boundedAlways _ _ _ _ _ _ (by assumption),?_⟩
    | refine ⟨_,.upperEventually _ x _ _ _ (by
        intro he; apply hxp; simp [Predicate.ofFinite,syntaxClocks,he]),?_⟩
    | refine ⟨_,.boundedEventually _ _ _ _ _ _ (by assumption),?_⟩
  all_goals
    intro B hB
    simp only [ExpansionRule.plainAnd,ExpansionRule.plainOr,ExpansionRule.plainUntil,
      ExpansionRule.plainRelease,ExpansionRule.openEventually,ExpansionRule.openAlways,
      ExpansionRule.upperAlways,ExpansionRule.boundedAlways,ExpansionRule.upperEventually,
      ExpansionRule.boundedEventually,List.mem_cons,List.not_mem_nil,or_false,
      List.mem_append] at hB
    try split_ifs at hB
    all_goals
      try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hB
      rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        simp_all [FreshFor,resetNames,syntaxClocks,Judgement.ofFinite,Predicate.ofFinite,
          ExpansionRule.upperAlways_defer,ExpansionRule.upperAlways_check,
          ExpansionRule.boundedAlways_defer,ExpansionRule.boundedAlways_check,
          ExpansionRule.boundedAlways_finish,ExpansionRule.upperEventually_defer,
          ExpansionRule.upperEventually_check,ExpansionRule.boundedEventually_defer,
          ExpansionRule.boundedEventually_check,ExpansionRule.boundedEventually_finish,
          ClockResetSet.clocks_union,Set.disjoint_left]

/-- Infinite-clock corollary of the chosen-name finite-family theorem. -/
theorem finite_fresh_rule [DecidableEq Clock] [Infinite Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : STLTableau.ConcreteRule p R) (Γ : MixedJ Clock Var) :
    ∃ R', STLTableau.ConcreteRule p R' ∧ ∀ B ∈ R'.branches,
      FreshFor (Predicate.ofFinite p) (Judgement.ofFinite B) Γ := by
  obtain ⟨x,hx⟩ := ((syntaxClocks_finite Γ).union
    (syntaxClocks_finite (.predicate (Predicate.ofFinite p)))).exists_notMem
  obtain ⟨R',hr',hf⟩ := finite_fresh_rule_at hr Γ x hx
  exact ⟨R',hr',fun B hm => (hf B hm).1⟩

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 800000 in
/-- Infinite timing uses the same fresh-parameter discipline and actual raw
families; no finite semantic cap or fresh branch-existence assumption is used. -/
theorem infinite_fresh_rule_at [DecidableEq Clock]
    {p : UnboundedClocked.Predicate Clock Var} {Bs : List (UnboundedClocked.Node Clock Var)}
    (hr : UnboundedClocked.ConcreteRule p Bs) (Γ : MixedJ Clock Var) (x : Clock)
    (hx : x ∉ syntaxClocks Γ ∪ syntaxClocks (.predicate (Predicate.ofUnbounded p))) :
    ∃ Bs', UnboundedClocked.ConcreteRule p Bs' ∧ ∀ B ∈ Bs',
      FreshFor (Predicate.ofUnbounded p) (Judgement.ofUnbounded B) Γ ∧
      resetNames (Judgement.ofUnbounded B) ⊆ syntaxClocks (.predicate (Predicate.ofUnbounded p)) ∪ {x} := by
  classical
  have hxΓ : x ∉ syntaxClocks Γ := fun h => hx (Or.inl h)
  have hxp : x ∉ syntaxClocks (.predicate (Predicate.ofUnbounded p)) := fun h => hx (Or.inr h)
  cases hr <;> first
    | refine ⟨_,.upperAlways _ x _ _ _ (by
        intro he; apply hxp; simp [Predicate.ofUnbounded,syntaxClocks,he]),?_⟩
    | refine ⟨_,.boundedAlways _ _ _ _ _ _ (by assumption),?_⟩
    | refine ⟨_,.upperEventually _ x _ _ _ (by
        intro he; apply hxp; simp [Predicate.ofUnbounded,syntaxClocks,he]),?_⟩
    | refine ⟨_,.boundedEventually _ _ _ _ _ _ (by assumption),?_⟩
  all_goals
    intro B hB
    simp only [UnboundedClocked.upperAlwaysBranches,UnboundedClocked.boundedAlwaysBranches,
      UnboundedClocked.upperEventuallyBranches,UnboundedClocked.boundedEventuallyBranches,
      List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hB
    try split_ifs at hB
    all_goals
      try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hB
      rcases hB with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        simp_all [FreshFor,resetNames,syntaxClocks,Judgement.ofUnbounded,Predicate.ofUnbounded,
          UnboundedClocked.upperAlwaysDefer,UnboundedClocked.upperAlwaysCheck,
          UnboundedClocked.boundedAlwaysDefer,UnboundedClocked.boundedAlwaysCheck,
          UnboundedClocked.upperEventuallyDefer,UnboundedClocked.upperEventuallyCheck,
          UnboundedClocked.boundedEventuallyDefer,UnboundedClocked.boundedEventuallyCheck,
          UnboundedClocked.boundedEventuallyFinish,UnboundedClocked.alwaysWait,
          UnboundedClocked.alwaysLast,
          ClockResetSet.clocks_union,Set.disjoint_left]

/-- Infinite-clock corollary of the chosen-name infinite-timing family theorem. -/
theorem infinite_fresh_rule [DecidableEq Clock] [Infinite Clock]
    {p : UnboundedClocked.Predicate Clock Var} {Bs : List (UnboundedClocked.Node Clock Var)}
    (hr : UnboundedClocked.ConcreteRule p Bs) (Γ : MixedJ Clock Var) :
    ∃ Bs', UnboundedClocked.ConcreteRule p Bs' ∧ ∀ B ∈ Bs',
      FreshFor (Predicate.ofUnbounded p) (Judgement.ofUnbounded B) Γ := by
  obtain ⟨x,hx⟩ := ((syntaxClocks_finite Γ).union
    (syntaxClocks_finite (.predicate (Predicate.ofUnbounded p)))).exists_notMem
  obtain ⟨Bs',hr',hf⟩ := infinite_fresh_rule_at hr Γ x hx
  exact ⟨Bs',hr',fun B hm => (hf B hm).1⟩

/-- Choose fresh RULE parameters before selecting a branch. The result is
an actual raw branch, fresh against all context names (including future guards
and reset bindings), satisfied on the same signal/partition, with the FULL
scoped invariant. Neither branch choice nor freshness is assumed. -/
theorem RawBranch.exists_preserving_fresh [DecidableEq Clock] [Infinite Clock]
    (p : Predicate Clock Var) (hp : p.Ready) (hn : ¬ p.IsAtomic) (Γ : MixedJ Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, p.Invariant σ P α k hk)
    (hst : σ.StablePartition p.formula P)
    (hs : Judgement.holds σ P α k (.predicate p)) :
    ∃ B, RawBranch p B ∧ FreshFor p B Γ ∧ Judgement.holds σ P α k B ∧
      B.EvaluatedInvariant σ P α k ∧ B.UnderlyingStable σ P := by
  obtain ⟨B,hB⟩ := RawBranch.exists_of_ready p hp hn
  cases hB with
  | @finite p₀ R rule B₀ _ =>
      obtain ⟨R',hr,hfresh⟩ := finite_fresh_rule rule Γ
      have hi₀ : ∀ hk : k.1 < P.size, STLTableau.Invariant σ P α k hk p₀ := by
        intro hk
        cases p₀ <;> exact hi hk
      have hst₀ : σ.StablePartition p₀.formula P := by simpa using hst
      obtain ⟨C,hm,hC,hI⟩ := STLTableau.rule_complete_preserving hr σ P α k hi₀ hst₀
        ((Judgement.holds_ofFinite σ P α k (.predicate p₀)).1 hs)
      exact ⟨_,.finite hr hm,hfresh C hm,(Judgement.holds_ofFinite σ P α k C).2 hC,
        (Judgement.evaluatedInvariant_ofFinite σ P α k C).2 hI,
        GeneratorStability.finite_branch_stable hr hm σ P hst₀⟩
  | @infinite p₀ Bs rule B₀ _ =>
      obtain ⟨Bs',hr,hfresh⟩ := infinite_fresh_rule rule Γ
      have hi₀ : ∀ hk : k.1 < P.size, UnboundedClocked.Invariant σ P α k hk p₀ := by
        intro hk
        cases p₀ <;> exact hi hk
      have hst₀ : σ.StablePartition p₀.formula P := by simpa using hst
      obtain ⟨C,hm,hC,hI⟩ := UnboundedClocked.rule_complete_preserving hr σ P α k hi₀ hst₀
        ((Judgement.holds_ofUnbounded σ P α k (.predicate p₀)).1 hs)
      exact ⟨_,.infinite hr hm,hfresh C hm,(Judgement.holds_ofUnbounded σ P α k C).2 hC,
        (Judgement.evaluatedInvariant_ofUnbounded σ P α k C).2 hI,
        GeneratorStability.infinite_branch_stable hr hm σ P hst₀⟩
  | opening c m kind a φ =>
      obtain ⟨x,hx⟩ := (syntaxClocks_finite Γ).exists_notMem
      obtain ⟨m',hm⟩ := (UnboundedClocked.opening_correct σ P α k x kind a φ).1
        ((Judgement.holds_ofUnbounded σ P α k (.plain _)).1 hs)
      have hfresh : FreshFor (.plain (UnboundedClocked.formula kind a φ))
          (Judgement.ofUnbounded (UnboundedClocked.opening x m' kind a φ)) Γ := by
        simpa [FreshFor,resetNames,syntaxClocks,Judgement.ofUnbounded,
          UnboundedClocked.opening,Set.disjoint_left] using hx
      exact ⟨_,.opening x m' kind a φ,hfresh,(Judgement.holds_ofUnbounded σ P α k _).2 hm,
        (Judgement.evaluatedInvariant_ofUnbounded σ P α k _).2
          (UnboundedClocked.opening_preserves σ P α k x m' kind a φ hm),
        GeneratorStability.opening_branch_stable x m' kind a φ σ P hst⟩

end STLTableau.Section4.Finiteness
