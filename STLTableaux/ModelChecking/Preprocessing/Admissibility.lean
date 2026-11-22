/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Closure.Residual.BranchTransitionForm

/-! # Normalized inputs of the concrete tableau rules

Negation normalization preserves satisfaction on finite signals. The
admissibility predicate checks the temporal grammar of `ConcreteRule`.
`Formula.normalizeForTableau` in
`STLTableaux.ModelChecking.Preprocessing.NormalizedInput` handles normalization
for the finite tableau.
-/
namespace STLTableau
open scoped STL

namespace AtomicProposition

/-- Negate a real comparison without introducing a negated atomic formula.
Disequality is the disjunction of the two strict comparisons. -/
def complementFormula {Var : Type*} (a : AtomicProposition Var) : Formula Var :=
  match a.relation with
  | .ge => .atom { a with relation := .lt }
  | .gt => .atom { a with relation := .le }
  | .lt => .atom { a with relation := .ge }
  | .le => .atom { a with relation := .gt }
  | .eq => Formula.or (.atom { a with relation := .lt }) (.atom { a with relation := .gt })

theorem satisfies_complementFormula {Var : Type*} (a : AtomicProposition Var)
    (σ : FiniteSignal Var) (t : σ.Time) :
    σ.Satisfies a.complementFormula t ↔ ¬ a.Holds (σ.value t) := by
  cases h : a.relation <;>
    simp [complementFormula, h, FiniteSignal.satisfies_or,
      FiniteSignal.satisfies_atom, Holds, RealRelation.Holds]

end AtomicProposition

namespace Formula
variable {Var : Type*}

/-- Push negation to comparisons and Boolean constants. For bounded `I`,
the negation of `◇[I] φ` uses the `□` form for the opening rule. -/
def normalizeNegation (negative : Bool) : Formula Var → Formula Var
  | .truth => if negative then falsity else .truth
  | .atom a => if negative then a.complementFormula else .atom a
  | .neg φ => normalizeNegation (!negative) φ
  | .and φ ψ => if negative then
      Formula.or (normalizeNegation true φ) (normalizeNegation true ψ)
    else .and (normalizeNegation false φ) (normalizeNegation false ψ)
  | .until I φ ψ => if negative then
      match I, φ with
      | .bounded J, .truth => Formula.always J (normalizeNegation true ψ)
      | _, _ => Formula.release I (normalizeNegation true φ) (normalizeNegation true ψ)
    else .until I (normalizeNegation false φ) (normalizeNegation false ψ)

theorem satisfies_normalizeNegation (φ : Formula Var) (negative : Bool)
    (σ : FiniteSignal Var) (t : σ.Time) :
    σ.Satisfies (φ.normalizeNegation negative) t ↔
      if negative then ¬ σ.Satisfies φ t else σ.Satisfies φ t := by
  induction φ generalizing negative t with
  | truth => cases negative <;> simp [normalizeNegation, falsity, FiniteSignal.Satisfies]
  | atom a => cases negative <;>
      simp [normalizeNegation, AtomicProposition.satisfies_complementFormula,
        FiniteSignal.Satisfies]
  | neg φ ih => cases negative <;> simp [normalizeNegation, FiniteSignal.Satisfies, ih]
  | and φ ψ ihφ ihψ =>
      cases negative
      · simp [normalizeNegation, FiniteSignal.Satisfies, ihφ, ihψ]
      · simp [normalizeNegation, FiniteSignal.satisfies_or, FiniteSignal.Satisfies,
          ihφ, ihψ]
        tauto
  | «until» I φ ψ ihφ ihψ =>
      cases negative
      · simp [normalizeNegation, FiniteSignal.Satisfies, ihφ, ihψ]
      · have hrelease :
            σ.Satisfies (Formula.release I (normalizeNegation true φ)
              (normalizeNegation true ψ)) t ↔ ¬ σ.Satisfies (.until I φ ψ) t := by
          simp [Formula.release, FiniteSignal.Satisfies, ihφ, ihψ]
        cases I <;> cases φ <;> first
          | exact hrelease
          | simp only [normalizeNegation, ↓reduceIte]
            simp [Formula.always, Formula.eventually, FiniteSignal.Satisfies, ihψ]

/-- The normalized input grammar as implemented by the concrete rule catalog.
General timed until/release must be eliminated separately before admission. -/
inductive TableauReady : Formula Var → Prop
  | truth : TableauReady .truth
  | falsity : TableauReady falsity
  | atom (a : AtomicProposition Var) : TableauReady (.atom a)
  | and {φ ψ} : TableauReady φ → TableauReady ψ → TableauReady (.and φ ψ)
  | or {φ ψ} : TableauReady φ → TableauReady ψ → TableauReady (Formula.or φ ψ)
  | until {φ ψ} : TableauReady φ → TableauReady ψ → TableauReady (untimedUntil φ ψ)
  | release {φ ψ} : TableauReady φ → TableauReady ψ →
      TableauReady (Formula.release (.unbounded 0) φ ψ)
  | eventually (I : BoundedTimeInterval) {φ} : TableauReady φ → TableauReady (eventually I φ)
  | always (I : BoundedTimeInterval) {φ} : TableauReady φ → TableauReady (always I φ)

theorem TableauReady.normalizeNegation {φ : Formula Var} (h : φ.TableauReady)
    (negative : Bool) : (φ.normalizeNegation negative).TableauReady := by
  induction h generalizing negative with
  | truth => cases negative <;> first | exact .truth | exact .falsity
  | falsity => cases negative <;> first | exact .truth | exact .falsity
  | atom a =>
      cases negative
      · exact .atom a
      · cases hr : a.relation <;>
          simp only [Formula.normalizeNegation, ↓reduceIte,
            AtomicProposition.complementFormula, hr] <;>
          first | exact .atom _ | exact .or (.atom _) (.atom _)
  | and hφ hψ ihφ ihψ =>
      cases negative
      · exact .and (ihφ false) (ihψ false)
      · exact .or (ihφ true) (ihψ true)
  | or hφ hψ ihφ ihψ =>
      cases negative
      · exact .or (ihφ false) (ihψ false)
      · exact .and (ihφ true) (ihψ true)
  | «until» hφ hψ ihφ ihψ =>
      cases negative
      · exact .until (ihφ false) (ihψ false)
      · exact .release (ihφ true) (ihψ true)
  | release hφ hψ ihφ ihψ =>
      cases negative
      · exact .release (ihφ false) (ihψ false)
      · exact .until (ihφ true) (ihψ true)
  | eventually I hφ ih =>
      cases negative
      · exact .eventually I (ih false)
      · exact .always I (ih true)
  | always I hφ ih =>
      cases negative
      · exact .always I (ih false)
      · exact .eventually I (ih true)

/-- A formula satisfying the tableau input grammar. -/
abbrev TableauInput (Var : Type*) := {φ : Formula Var // φ.TableauReady}

/-- Normalize Boolean negations and return the result when it satisfies
`TableauReady`. The grammar check uses classical decidability. -/
noncomputable def prepare? (φ : Formula Var) : Option (TableauInput Var) := by
  classical
  exact if h : (φ.normalizeNegation false).TableauReady then
    some ⟨φ.normalizeNegation false, h⟩ else none

theorem prepare?_sound {φ : Formula Var} {input : TableauInput Var}
    (h : φ.prepare? = some input) (σ : FiniteSignal Var) (t : σ.Time) :
    σ.Satisfies input.1 t ↔ σ.Satisfies φ t := by
  classical
  unfold prepare? at h
  split_ifs at h with hr
  · cases h
    simpa using satisfies_normalizeNegation φ false σ t
theorem prepare?_exists_iff (φ : Formula Var) :
    (∃ input, φ.prepare? = some input) ↔ (φ.normalizeNegation false).TableauReady := by
  classical
  simp only [prepare?]
  split_ifs <;> simp_all

theorem TableauReady.prepare?_exists {φ : Formula Var} (h : φ.TableauReady) :
    ∃ input, φ.prepare? = some input :=
  (prepare?_exists_iff φ).2 (h.normalizeNegation false)

@[simp] theorem normalizeNegation_triple_truth :
    (Formula.neg (.neg (.neg .truth)) : Formula Var).normalizeNegation false = falsity := rfl

theorem prepare?_triple_truth :
    ∃ input : TableauInput Var,
      (Formula.neg (.neg (.neg .truth))).prepare? = some input ∧ input.1 = falsity := by
  classical
  simp [prepare?, normalizeNegation, TableauReady.falsity]

theorem TableauReady.complexity_zero_iff {Clock : Type*}
    {φ : Formula Var} (h : φ.TableauReady) :
    φ.complexity = 0 ↔
      (IntervalPredicate.plain φ : IntervalPredicate Clock Var).IsAtomic := by
  cases h <;>
    simp [Formula.complexity, Formula.falsity, Formula.or, Formula.untimedUntil,
      Formula.release, Formula.eventually, Formula.always, IntervalPredicate.IsAtomic]

theorem TableauReady.and_operands {φ ψ : Formula Var} (h : (Formula.and φ ψ).TableauReady) :
    φ.TableauReady ∧ ψ.TableauReady := by cases h; constructor <;> assumption

theorem TableauReady.or_operands {φ ψ : Formula Var} (h : (Formula.or φ ψ).TableauReady) :
    φ.TableauReady ∧ ψ.TableauReady := by cases h; constructor <;> assumption

theorem TableauReady.until_operands {φ ψ : Formula Var}
    (h : (untimedUntil φ ψ).TableauReady) :
    φ.TableauReady ∧ ψ.TableauReady := by cases h; constructor <;> assumption

theorem TableauReady.release_operands {φ ψ : Formula Var}
    (h : (Formula.release (.unbounded 0) φ ψ).TableauReady) :
    φ.TableauReady ∧ ψ.TableauReady := by cases h; constructor <;> assumption

theorem TableauReady.eventually_operand {φ : Formula Var} {I : BoundedTimeInterval}
    (h : (Formula.eventually I φ).TableauReady) : φ.TableauReady := by cases h; assumption

theorem TableauReady.always_operand {φ : Formula Var} {I : BoundedTimeInterval}
    (h : (Formula.always I φ).TableauReady) : φ.TableauReady := by cases h; assumption

@[simp] theorem tableauReady_and {φ ψ : Formula Var} :
    (Formula.and φ ψ).TableauReady ↔ φ.TableauReady ∧ ψ.TableauReady :=
  ⟨TableauReady.and_operands, fun h => .and h.1 h.2⟩

@[simp] theorem tableauReady_or {φ ψ : Formula Var} :
    (Formula.or φ ψ).TableauReady ↔ φ.TableauReady ∧ ψ.TableauReady :=
  ⟨TableauReady.or_operands, fun h => .or h.1 h.2⟩

@[simp] theorem tableauReady_until {φ ψ : Formula Var} :
    (untimedUntil φ ψ).TableauReady ↔ φ.TableauReady ∧ ψ.TableauReady :=
  ⟨TableauReady.until_operands, fun h => .until h.1 h.2⟩

@[simp] theorem tableauReady_release {φ ψ : Formula Var} :
    (Formula.release (.unbounded 0) φ ψ).TableauReady ↔ φ.TableauReady ∧ ψ.TableauReady :=
  ⟨TableauReady.release_operands, fun h => .release h.1 h.2⟩

@[simp] theorem tableauReady_eventually {φ : Formula Var} {I : BoundedTimeInterval} :
    (Formula.eventually I φ).TableauReady ↔ φ.TableauReady :=
  ⟨TableauReady.eventually_operand, .eventually I⟩

@[simp] theorem tableauReady_always {φ : Formula Var} {I : BoundedTimeInterval} :
    (Formula.always I φ).TableauReady ↔ φ.TableauReady :=
  ⟨TableauReady.always_operand, .always I⟩

end Formula

namespace IntervalPredicate

/-- Supported operands, and distinct clocks in a two-clock predicate. -/
def TableauReady {Clock Var : Type*} : IntervalPredicate Clock Var → Prop
  | .plain φ => φ.TableauReady
  | .upper _ _ _ _ φ => φ.TableauReady
  | .bounded c d _ _ _ _ φ => c ≠ d ∧ φ.TableauReady

theorem TableauReady.complexity_zero_iff {Clock Var : Type*}
    {p : IntervalPredicate Clock Var} (h : p.TableauReady) :
    p.complexity = 0 ↔ p.IsAtomic := by
  cases p with
  | plain φ => exact Formula.TableauReady.complexity_zero_iff h
  | upper => simp [complexity, IsAtomic]
  | bounded => simp [complexity, IsAtomic]

end IntervalPredicate

namespace Judgement

/-- Supported predicates at every nesting depth, including resets and next. -/
def TableauReady {Clock Var : Type*} : Judgement Clock Var → Prop
  | .predicate p => p.TableauReady
  | .conj Φ Ψ => Φ.TableauReady ∧ Ψ.TableauReady
  | .reset _ Ψ | .next Ψ => Ψ.TableauReady
  | _ => True

theorem TableauReady.currentPredicates {Clock Var : Type*} {Ψ : Judgement Clock Var}
    (h : Ψ.TableauReady) {p : IntervalPredicate Clock Var}
    (hp : p ∈ Ψ.currentPredicates) : p.TableauReady := by
  induction Ψ with
  | predicate q =>
      have heq : p = q := hp
      exact heq ▸ h
  | conj Φ Ψ ihΦ ihΨ =>
      rcases hp with hp | hp
      · exact ihΦ h.1 hp
      · exact ihΨ h.2 hp
  | reset Λ Ψ ih => exact ih h hp
  | _ => simp [Judgement.currentPredicates] at hp

@[simp] theorem tableauReady_markedLT {Clock Var : Type*} (c : Clock) (m : Marker)
    (a : NNReal) : (markedLT c m a : Judgement Clock Var).TableauReady := by
  cases m <;> trivial

@[simp] theorem tableauReady_markedGT {Clock Var : Type*} (c : Clock) (m : Marker)
    (a : NNReal) : (markedGT c m a : Judgement Clock Var).TableauReady := by
  cases m <;> trivial

end Judgement

namespace ConcreteRule
variable {Clock Var : Type*} [DecidableEq Clock]

theorem not_atomic {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (h : ConcreteRule p R) : ¬ p.IsAtomic := by
  cases h <;> simp [IntervalPredicate.IsAtomic, Formula.or, Formula.untimedUntil,
    Formula.release, Formula.eventually, Formula.always]

/-- All predicates produced by an actual rule remain in the supported grammar.
This includes predicates below resets and at the next interval. -/
theorem branch_tableauReady {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hrule : ConcreteRule p R) (hready : p.TableauReady)
    {B : Judgement Clock Var} (hB : B ∈ R.branches) : B.TableauReady := by
  classical
  cases hrule <;>
    simp only [ExpansionRule.plainAnd, ExpansionRule.plainOr,
      ExpansionRule.plainUntil, ExpansionRule.plainRelease,
      ExpansionRule.openEventually, ExpansionRule.openAlways,
      ExpansionRule.upperAlways, ExpansionRule.boundedAlways,
      ExpansionRule.upperEventually, ExpansionRule.boundedEventually,
      List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at hB <;>
    (try split_ifs at hB) <;>
    (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hB) <;>
    rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [Judgement.TableauReady, IntervalPredicate.TableauReady,
      ExpansionRule.upperAlways_defer, ExpansionRule.upperAlways_check,
      ExpansionRule.boundedAlways_defer, ExpansionRule.boundedAlways_check,
      ExpansionRule.boundedAlways_finish, ExpansionRule.upperEventually_defer,
      ExpansionRule.upperEventually_check, ExpansionRule.boundedEventually_defer,
      ExpansionRule.boundedEventually_check, ExpansionRule.boundedEventually_finish]

/-- Opening an unclocked temporal predicate `[φ]` uses one clock. Expanding the `↑` form
uses a second clock distinct from its left clock. -/
theorem exists_of_ready_not_atomic [Nontrivial Clock]
    {p : IntervalPredicate Clock Var} (h : p.TableauReady) (hna : ¬ p.IsAtomic) :
    ∃ R, ConcreteRule p R := by
  obtain ⟨c, d, hcd⟩ := exists_pair_ne Clock
  cases p with
  | plain φ =>
      cases h with
      | truth => exact (hna trivial).elim
      | falsity => exact (hna trivial).elim
      | atom => exact (hna trivial).elim
      | and hφ hψ => exact ⟨_, .plainAnd _ _⟩
      | or hφ hψ => exact ⟨_, .plainOr _ _⟩
      | «until» hφ hψ => exact ⟨_, .plainUntil _ _⟩
      | release hφ hψ => exact ⟨_, .plainRelease _ _⟩
      | eventually I hφ => exact ⟨_, .openEventually c I _⟩
      | always I hφ => exact ⟨_, .openAlways c I _⟩
  | upper e m kind I φ =>
      obtain ⟨f, hef⟩ := exists_ne e
      cases kind
      · exact ⟨_, .upperAlways e f m I φ (Ne.symm hef)⟩
      · exact ⟨_, .upperEventually e f m I φ (Ne.symm hef)⟩
  | bounded e f m q kind I φ =>
      cases kind
      · exact ⟨_, .boundedAlways e f m q I φ h.1⟩
      · exact ⟨_, .boundedEventually e f m q I φ h.1⟩

end ConcreteRule

namespace BranchTransitionForms
variable {Clock Var : Type*} [DecidableEq Clock] [Nontrivial Clock]

theorem not_hasRule_iff_atomic (A : BranchTransitionForms Clock Var)
    {p : IntervalPredicate Clock Var} (h : p.TableauReady) :
    ¬ A.expansionRules.HasRule p ↔ p.IsAtomic := by
  constructor
  · intro hn
    by_contra hna
    exact hn (ConcreteRule.exists_of_ready_not_atomic h hna)
  · rintro ha ⟨R, hR⟩
    exact ConcreteRule.not_atomic hR ha

/-- In the supported grammar a non-atomic closed predicate has a real rule
branch witness; the no-rule alternative cannot silently discharge it. -/
theorem ruleClosedFor_nonatomic (A : BranchTransitionForms Clock Var)
    {Φ : TransitionForm Clock Var} {p : IntervalPredicate Clock Var}
    (hr : p.TableauReady) (hna : ¬ p.IsAtomic)
    (hc : A.expansionRules.RuleClosedFor Φ p) :
    ∃ R, ConcreteRule p R ∧ ∃ Ψ ∈ R.branches, ∃ B,
      A.relation Φ.current.resets Ψ B ∧ B ⊑ Φ := by
  rcases hc.2 with hn | hb
  · exact (hna ((A.not_hasRule_iff_atomic hr).1 hn)).elim
  · exact hb

omit [Nontrivial Clock] in
/-- The current-part admissibility boundary is preserved by the existing
minimal-extension expansion relation. -/
theorem expansion_preservesCurrentTableauReady (A : BranchTransitionForms Clock Var)
    {Φ Φ' : TransitionForm Clock Var} {p : IntervalPredicate Clock Var}
    (hexp : A.expansionRules.PExpansion p Φ Φ')
    (hΦ : ExpansionRules.AllCurrentPredicates Φ IntervalPredicate.TableauReady) :
    ExpansionRules.AllCurrentPredicates Φ' IntervalPredicate.TableauReady := by
  apply hexp.preservesAllCurrentPredicates hΦ
  intro R Ψ B hR hΨ hB _ q hq
  exact (ConcreteRule.branch_tableauReady hR (hΦ p hexp.1) hΨ).currentPredicates
    (A.currentPredicate_mem hB hq)

omit [Nontrivial Clock] in
/-- Any existing closure of a supported current form retains that boundary. -/
theorem closure_preservesCurrentTableauReady (A : BranchTransitionForms Clock Var)
    {Φ Φc : TransitionForm Clock Var}
    (hc : A.expansionRules.IsClosure Φ Φc)
    (hΦ : ExpansionRules.AllCurrentPredicates Φ IntervalPredicate.TableauReady) :
    ExpansionRules.AllCurrentPredicates Φc IntervalPredicate.TableauReady :=
  hc.expansionPath.preserve (fun _ hexp => A.expansion_preservesCurrentTableauReady hexp) hΦ

end BranchTransitionForms

namespace Formula.TableauInput

/-- Enter the tableau layer with the certified formula, never the raw input. -/
def initialForm {Clock Var : Type*} (input : Formula.TableauInput Var) :
    TransitionForm Clock Var :=
  TransitionForm.ofState (StateForm.ofLocal (.predicate (.plain input.1)) trivial)

theorem initialForm_ready {Clock Var : Type*} (input : Formula.TableauInput Var) :
    ExpansionRules.AllCurrentPredicates (input.initialForm : TransitionForm Clock Var)
      IntervalPredicate.TableauReady := by
  intro p hp
  have heq : p = .plain input.1 := by
    simpa [initialForm, TransitionForm.ofState, StateForm.ofLocal] using hp
  subst p
  exact input.2

theorem initialForm_satisfies {Clock Var : Type*} (input : Formula.TableauInput Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    input.initialForm.Satisfies σ P α k ↔
      Judgement.Satisfies σ P α k (.predicate (.plain input.1)) := by
  simp [initialForm]

/-- Preparing a raw formula and entering its certified initial form preserves
the original interval judgement, including the terminal position. -/
theorem initialForm_of_prepare?_satisfies {Clock Var : Type*}
    {φ : Formula Var} {input : Formula.TableauInput Var} (h : φ.prepare? = some input)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    input.initialForm.Satisfies σ P α k ↔
      Judgement.Satisfies σ P α k (.predicate (.plain φ)) := by
  rw [initialForm_satisfies]
  simp only [Judgement.Satisfies]
  split
  · simp only [IntervalPredicate.Satisfies, Formula.prepare?_sound h]
  · rfl

/-- Every non-atomic current predicate of a closure reached from a certified
input has an actual expansion witness. -/
theorem closure_nonatomic_has_branch {Clock Var : Type*}
    [DecidableEq Clock] [Nontrivial Clock]
    (input : Formula.TableauInput Var) (A : BranchTransitionForms Clock Var)
    {Φc : TransitionForm Clock Var} (hc : A.expansionRules.IsClosure input.initialForm Φc)
    {p : IntervalPredicate Clock Var} (hp : Judgement.predicate p ∈ Φc.current.locals)
    (hna : ¬ p.IsAtomic) :
    ∃ R, ConcreteRule p R ∧ ∃ Ψ ∈ R.branches, ∃ B,
      A.relation Φc.current.resets Ψ B ∧ B ⊑ Φc :=
  A.ruleClosedFor_nonatomic
    (A.closure_preservesCurrentTableauReady hc input.initialForm_ready p hp)
    hna (hc.closed p hp)

end Formula.TableauInput
end STLTableau
