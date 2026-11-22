import STLTableaux.Closure.Expansion.FixedExpansionOrder

open STLTableau (Formula AtomicProposition ClockResetSet)
open STLTableau.Section3

namespace FixedExpansionOrderChecks

/-- Enumerate the current predicates in reverse order. -/
noncomputable def reverseOrder {Clock Var : Type*} (F : TransitionForm Clock Var) :
    List (Predicate Clock Var) :=
  (FaithfulClosure.statePredicates F.current).toList.reverse

theorem reverseOrder_enumerates {Clock Var : Type*} (F : TransitionForm Clock Var) :
    ExpansionFamily.EnumeratesCurrent (reverseOrder F) F := by
  classical
  constructor
  · simpa only [reverseOrder, List.nodup_reverse] using
      (Finset.nodup_toList (FaithfulClosure.statePredicates F.current))
  · intro p
    simp [reverseOrder, FaithfulClosure.mem_statePredicates]

def emptyState : StateForm Unit Unit where
  guards := ∅
  guards_finite := Set.finite_empty
  resets := ClockResetSet.empty
  locals := ∅
  locals_finite := Set.finite_empty

def emptyForm : TransitionForm Unit Unit := .ofState emptyState

def zeroAtom : AtomicProposition Unit := ⟨0, Fin.elim0, fun _ => 0, .ge⟩
def oneAtom : AtomicProposition Unit := ⟨0, Fin.elim0, fun _ => 1, .ge⟩

def twoAtomicState : StateForm Unit Unit where
  guards := ∅
  guards_finite := Set.finite_empty
  resets := ClockResetSet.empty
  locals := {Local.predicate (.plain (.atom zeroAtom)), Local.predicate (.plain (.atom oneAtom))}
  locals_finite := (Set.finite_singleton _).insert _

def twoAtomicForm : TransitionForm Unit Unit := .ofState twoAtomicState

theorem twoAtomic_closed : ConcreteContextual.catalogue.IsClosed twoAtomicForm := by
  intro p hp
  have hp' : Local.predicate p = Local.predicate (.plain (.atom zeroAtom)) ∨
      Local.predicate p = Local.predicate (.plain (.atom oneAtom)) := hp
  rcases hp' with hp | hp
  all_goals
    cases hp
    apply ConcreteContextual.zero_complexity_ruleClosed
    rfl

/-- Both distinct current predicates occur exactly once even in reverse order. -/
theorem reverseOrder_twoAtomic :
    (reverseOrder twoAtomicForm).Nodup ∧
    Predicate.plain (.atom zeroAtom) ∈ reverseOrder twoAtomicForm ∧
    Predicate.plain (.atom oneAtom) ∈ reverseOrder twoAtomicForm ∧
    (Predicate.plain (.atom zeroAtom) : Predicate Unit Unit) ≠ .plain (.atom oneAtom) := by
  refine ⟨(reverseOrder_enumerates twoAtomicForm).1, ?_, ?_, ?_⟩
  · apply ((reverseOrder_enumerates twoAtomicForm).2 _).2
    exact Or.inl rfl
  · apply ((reverseOrder_enumerates twoAtomicForm).2 _).2
    exact Or.inr rfl
  · intro h
    have ha : zeroAtom = oneAtom := Formula.atom.inj (Predicate.plain.inj h)
    have hn := congrArg (fun a : AtomicProposition Unit => a.function (fun _ => 0)) ha
    have bad : (0 : ℝ) = 1 := hn
    exact zero_ne_one bad

theorem emptyForm_closed : ConcreteContextual.catalogue.IsClosed emptyForm := by
  intro p hp
  exact False.elim hp

theorem emptyForm_own_closure :
    ConcreteContextual.catalogue.IsClosure emptyForm emptyForm :=
  ClosureCatalogue.IsClosure.self emptyForm_closed

theorem empty_literal_rank_zero : ConcreteContextual.literalLevelRank emptyForm 0 = 0 := by
  apply ExpansionFamily.familyRank_eq_zero_of_all_closed
  intro F hF
  have hEq : F = emptyForm := hF
  subst F
  exact emptyForm_closed

theorem empty_alpha_rank_zero : ConcreteContextual.alphaLevelRank emptyForm 0 = 0 := by
  apply ExpansionFamily.familyRank_eq_zero_of_all_closed
  intro F hF
  have hEq : F = emptyForm := hF
  subst F
  exact emptyForm_closed

/-- Check fixed-order reachability for every minimal closure over a one-clock type. -/
theorem all_minimal_literal (F : TransitionForm Unit Unit) (k : ℕ)
    (hz : ConcreteContextual.literalLevelRank F k = 0) :
    ∀ U, ConcreteContextual.catalogue.IsClosure F U →
      U ∈ ConcreteContextual.catalogue.fixedExpansionLevel reverseOrder F k ∧
      U ∈ ConcreteContextual.catalogue.expansionLevel F k :=
  (ConcreteContextual.fixed_expansion_order_correct
    reverseOrder reverseOrder_enumerates F k hz).2

theorem all_minimal_alpha (F : TransitionForm Unit Unit) (k : ℕ)
    (hz : ConcreteContextual.alphaLevelRank F k = 0) :
    ∀ U, ConcreteContextual.catalogue.IsClosure F U →
      U ∈ ConcreteContextual.fixedAlphaExpansionLevel reverseOrder F k ∧
      U ∈ ConcreteContextual.alphaExpansionLevel F k :=
  (ConcreteContextual.fixed_alpha_expansion_order_correct
    reverseOrder reverseOrder_enumerates F k hz).2

theorem empty_zero_level :
    emptyForm ∈ ConcreteContextual.catalogue.fixedExpansionLevel reverseOrder emptyForm 0 ∧
    emptyForm ∈ ConcreteContextual.fixedAlphaExpansionLevel reverseOrder emptyForm 0 := by
  exact ⟨(all_minimal_literal emptyForm 0 empty_literal_rank_zero
    emptyForm emptyForm_own_closure).1,
    (all_minimal_alpha emptyForm 0 empty_alpha_rank_zero
      emptyForm emptyForm_own_closure).1⟩

/-- Empty current input remains exactly itself after arbitrarily many rounds,
even for a completely unconstrained step relation. -/
theorem empty_fixed_level (Step : Predicate Unit Unit → TransitionForm Unit Unit →
    TransitionForm Unit Unit → Prop) (i : ℕ) :
    ExpansionFamily.fixedLevel Step reverseOrder emptyForm i = {emptyForm} := by
  have horder : reverseOrder emptyForm = [] := by
    classical
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro p hp
    exact ((reverseOrder_enumerates emptyForm).2 p).mp hp
  induction i with
  | zero => rfl
  | succ i ih =>
    ext G
    constructor
    · rintro ⟨H, hH, hr⟩
      rw [ih] at hH
      have hH' : H = emptyForm := hH
      subst H
      change ExpansionFamily.Sequence Step (reverseOrder emptyForm) emptyForm G at hr
      rw [horder] at hr
      cases hr
      rfl
    · intro hG
      have hG' : G = emptyForm := hG
      subst G
      refine ⟨emptyForm, ?_, ?_⟩
      · rw [ih]; rfl
      · change ExpansionFamily.Sequence Step (reverseOrder emptyForm) emptyForm emptyForm
        rw [horder]
        exact .nil _

theorem empty_seventh_level :
    emptyForm ∈ ConcreteContextual.catalogue.fixedExpansionLevel reverseOrder emptyForm 7 ∧
    emptyForm ∈ ConcreteContextual.fixedAlphaExpansionLevel reverseOrder emptyForm 7 := by
  constructor <;> change emptyForm ∈ ExpansionFamily.fixedLevel _ reverseOrder emptyForm 7
  all_goals rw [empty_fixed_level]; rfl

/-- Existing rank termination supplies a later positive-index level containing
every given minimal closure, still over the finite clock type. -/
theorem positive_rank_eventually_all_minimal (F : TransitionForm Unit Unit)
    (hpos : 0 < ConcreteContextual.literalLevelRank F 0) :
    ∃ k, 0 < k ∧ ConcreteContextual.literalLevelRank F k = 0 ∧
      ∀ U, ConcreteContextual.catalogue.IsClosure F U →
        U ∈ ConcreteContextual.catalogue.fixedExpansionLevel reverseOrder F k := by
  obtain ⟨k, hz⟩ := ConcreteContextual.literal_level_rank_eventually_zero F
  have hzero := hz k le_rfl
  have hk : 0 < k := by
    by_contra h
    have he : k = 0 := by omega
    subst k
    omega
  refine ⟨k, hk, hzero, ?_⟩
  intro U hc
  exact (all_minimal_literal F k hzero U hc).1

/-- Fixing the processing list does not fix expansion branch choices. This
small relation isolates the generic API, without claiming concrete rulehood. -/
theorem fixed_round_retains_two_choices :
    ∃ G H : TransitionForm Unit Unit, G ≠ H ∧
      ExpansionFamily.fixedRound (fun _ _ _ => True)
        (fun _ => [Predicate.plain Formula.truth]) emptyForm G ∧
      ExpansionFamily.fixedRound (fun _ _ _ => True)
        (fun _ => [Predicate.plain Formula.truth]) emptyForm H := by
  refine ⟨emptyForm, ⟨emptyState, some emptyState⟩, ?_, ?_, ?_⟩
  · intro h
    have hn := congrArg TransitionForm.nextPart h
    cases hn
  · exact .cons trivial (.nil _)
  · exact .cons trivial (.nil _)

run_elab do
  for name in #[``reverseOrder_enumerates, ``emptyForm_own_closure,
      ``twoAtomic_closed, ``reverseOrder_twoAtomic,
      ``empty_literal_rank_zero, ``empty_alpha_rank_zero,
      ``all_minimal_literal, ``all_minimal_alpha, ``empty_zero_level,
      ``empty_fixed_level, ``empty_seventh_level, ``positive_rank_eventually_all_minimal,
      ``fixed_round_retains_two_choices] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end FixedExpansionOrderChecks
