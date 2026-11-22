import STLTableaux.Closure.Catalogue.FaithfulContextualCatalogue
import STLTableaux.Examples.ClosureAlphaFacts

namespace STLTableau.Section3.UpperAlwaysClosure
variable {Clock Var : Type*} [DecidableEq Clock]

def HasNextPredicate (F : TransitionForm Clock Var) : Prop :=
  ∃ N, F.nextPart = some N ∧ ∃ p, Local.predicate p ∈ N.locals
def HasNextGuard (F : TransitionForm Clock Var) (g : Guard Clock) : Prop :=
  ∃ N, F.nextPart = some N ∧ g ∈ N.guards
def HasNextTerminal (F : TransitionForm Clock Var) : Prop :=
  ∃ N, F.nextPart = some N ∧ Local.terminal ∈ N.locals
def Checked (F : TransitionForm Clock Var) (c : Clock) (I : BoundedTimeInterval)
    (a : AtomicProposition Var) : Prop :=
  Local.predicate (.plain (.atom a)) ∈ F.current.locals ∧
    HasNextGuard F ⟨c,.gt,⟨I.lower,I.lower_nonnegative⟩⟩ ∧ HasNextTerminal F

set_option maxHeartbeats 1000000 in
-- Normalize the six branches of the expansion rule for always in the `↑` form.
private theorem finite_branch_facts
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    {raw : STLTableau.Judgement Clock Var} {F : TransitionForm Clock Var}
    (c : Clock) (I : BoundedTimeInterval) (a : AtomicProposition Var)
    (hr : STLTableau.ConcreteRule p R)
    (he : Predicate.ofFinite p = .upper c .closed .always (.bounded I) (.atom a))
    (hm : raw ∈ R.branches)
    (hn : TransitionForm.normalize? (Judgement.ofFinite raw) = some F) :
    F.current.resets.clocks = ∅ ∧
      (HasNextPredicate F ∨
        HasNextGuard F ⟨c, .le, ⟨I.lower, I.lower_nonnegative⟩⟩ ∨ Checked F c I a) := by
  cases hr <;> simp only [Predicate.ofFinite, Predicate.upper.injEq, reduceCtorEq,
    TimeInterval.bounded.injEq, true_and, false_and, and_false] at he
  rename_i c' d b I' φ hcd
  obtain ⟨rfl,rfl,rfl,rfl⟩ := he
  have hempty : (ClockResetSet.empty : ClockResetSet Clock).clocks = ∅ := by
    ext clock
    constructor
    · rintro ⟨x,hx⟩
      change none = some x at hx
      cases hx
    · intro h
      cases h
  simp only [ExpansionRule.upperAlways, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [ExpansionRule.upperAlways_defer, ExpansionRule.upperAlways_check,
      STLTableau.Judgement.markedLT_eq_clock, STLTableau.Judgement.markedGT_eq_clock,
      Judgement.ofFinite, TransitionForm.normalize?, TransitionForm.union,
      TransitionForm.unionNext, TransitionForm.ofState, TransitionForm.ofNextState,
      TransitionForm.underReset] at hn <;> cases hn <;>
    norm_num [HasNextPredicate, HasNextGuard, HasNextTerminal, Checked,
      StateForm.ofGuard, StateForm.ofLocal, StateForm.union, ClockResetSet.clocks,
      ClockResetSet.empty, StateForm.empty, ClockResetSet.union, Predicate.ofFinite] <;>
    exact hempty

private theorem mixed_branch_facts (c : Clock) (I : BoundedTimeInterval)
    (a : AtomicProposition Var) {R : TransitionForm Clock Var}
    (hR : ConcreteMixed.catalogue.Branch
      (.upper c .closed .always (.bounded I) (.atom a)) ClockResetSet.empty R) :
    R.current.resets.clocks = ∅ ∧
      (HasNextPredicate R ∨
        HasNextGuard R ⟨c,.le,⟨I.lower,I.lower_nonnegative⟩⟩ ∨ Checked R c I a) := by
  rcases hR with h | h | h
  · obtain ⟨p,E,raw,F,he,hr,hm,hn,rfl⟩ := h
    obtain ⟨hem,hf⟩ := finite_branch_facts c I a hr he.symm hm hn
    constructor
    · have he : (ClockResetSet.empty : ClockResetSet Clock).clocks = ∅ := by
        ext c; constructor
        · rintro ⟨v,hv⟩; change none = some v at hv; cases hv
        · intro h; cases h
      simpa [TransitionForm.underReset, ClockResetSet.clocks_union, he] using hem
    · simpa [HasNextPredicate, HasNextGuard, HasNextTerminal, Checked,
        TransitionForm.underReset] using hf
  · obtain ⟨p,E,raw,F,he,hr,hm,hn,rfl⟩ := h
    cases p <;> simp [Predicate.ofUnbounded] at he
  · obtain ⟨c,m,k,t,φ,F,he,hn,rfl⟩ := h
    cases he

omit [DecidableEq Clock] in
private theorem alpha_branch_facts (c : Clock) (I : BoundedTimeInterval)
    (a : AtomicProposition Var) {A R : TransitionForm Clock Var}
    (ha : A.AlphaEquivalent R)
    (hf : R.current.resets.clocks = ∅ ∧
      (HasNextPredicate R ∨
        HasNextGuard R ⟨c, .le, ⟨I.lower, I.lower_nonnegative⟩⟩ ∨ Checked R c I a)) :
    HasNextPredicate A ∨
      HasNextGuard A ⟨c,.le,⟨I.lower,I.lower_nonnegative⟩⟩ ∨ Checked A c I a := by
  have hem := ha.current_reset_empty.mpr hf.1
  rcases hf.2 with hp | hg | ⟨hp,hg,ht⟩
  · exact Or.inl (ha.next_predicate.mpr hp)
  · exact Or.inr (Or.inl ((ha.next_guards_of_current_reset_empty hem _).mpr hg))
  · exact Or.inr (Or.inr ⟨(ha.current_plain _).mpr hp,
      (ha.next_guards_of_current_reset_empty hem _).mpr hg, ha.next_terminal.mpr ht⟩)

theorem branch_forced (c : Clock) (I : BoundedTimeInterval) (a : AtomicProposition Var)
    {Θ C B : TransitionForm Clock Var} {N : StateForm Clock Var}
    (hC : C.nextPart = some N)
    (hg : N.guards = {⟨c,.gt,⟨I.lower,I.lower_nonnegative⟩⟩})
    (hl : N.locals = {Local.terminal})
    (hΘ : SyntacticallySubsumed Θ C)
    (hb : ConcreteContextual.catalogue.Branch
      (.upper c .closed .always (.bounded I) (.atom a)) Θ.current.resets B)
    (hB : SyntacticallySubsumed B Θ) : Checked Θ c I a := by
  obtain ⟨R,A,hR,ha,rfl⟩ := hb
  have hf := alpha_branch_facts c I a ha (mixed_branch_facts c I a hR)
  have hninc : ∀ M, A.nextPart = some M →
      ∃ T, Θ.nextPart = some T ∧ ComponentsIncluded M T ∧ ComponentsIncluded T N := by
    intro M hM
    obtain ⟨T,hT,hMT,_⟩ := hB.next M hM
    obtain ⟨U,hU,hTU,_⟩ := hΘ.next T hT
    have : U = N := Option.some.inj (hU.symm.trans hC)
    subst U
    exact ⟨T,hT,hMT,hTU⟩
  rcases hf with ⟨M,hM,p,hp⟩ | ⟨M,hM,hguard⟩ | ⟨hplain,⟨M,hM,hguard⟩,⟨T,hT,hterminal⟩⟩
  · obtain ⟨T,hT,hMT,hTN⟩ := hninc M hM
    have hh := hTN.locals (hMT.locals hp)
    rw [hl] at hh
    cases hh
  · obtain ⟨T,hT,hMT,hTN⟩ := hninc M hM
    have hh := hTN.guards (hMT.guards hguard)
    rw [hg] at hh
    have heq := Set.mem_singleton_iff.mp hh
    have := congrArg Guard.relation heq
    cases this
  · obtain ⟨U,hU,hMU,hUN⟩ := hninc M hM
    have eqMT : M = T := Option.some.inj (hM.symm.trans hT)
    subst T
    exact ⟨hB.current.locals hplain, ⟨U,hU,hMU.guards hguard⟩,
      ⟨U,hU,hMU.locals hterminal⟩⟩

theorem ruleClosed_forced (c d : Clock) (hcd : c ≠ d)
    (I : BoundedTimeInterval) (a : AtomicProposition Var)
    {Θ C : TransitionForm Clock Var} {N : StateForm Clock Var}
    (hC : C.nextPart = some N)
    (hg : N.guards = {⟨c,.gt,⟨I.lower,I.lower_nonnegative⟩⟩})
    (hl : N.locals = {Local.terminal})
    (hΘ : SyntacticallySubsumed Θ C)
    (hc : ConcreteContextual.catalogue.RuleClosedFor Θ
      (.upper c .closed .always (.bounded I) (.atom a))) : Checked Θ c I a := by
  rcases hc with hno | ⟨B,hb,hB⟩
  · apply False.elim
    apply hno
    apply ConcreteContextual.catalogue.branch_exists
    · exact Or.inl (Or.inr ⟨.upper c .closed .always I (.atom a),
        ExpansionRule.upperAlways c d .closed I (.atom a), rfl,
        .upperAlways c d .closed I (.atom a) hcd⟩)
    · simp [Predicate.IsAtomic]
  · exact branch_forced c I a hC hg hl hΘ hb hB

end STLTableau.Section3.UpperAlwaysClosure

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``STLTableau.Section3.UpperAlwaysClosure.branch_forced,
      ``STLTableau.Section3.UpperAlwaysClosure.ruleClosed_forced] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
