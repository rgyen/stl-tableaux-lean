import STLTableaux.Syntax.InputSyntax
import STLTableaux.Finiteness.Derivation.Derivation

/-! Formula-level normalized input preservation for the actual raw expansion rules.
This is separate from reset freshness, clock bounds and trace satisfaction. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

def predicateNormalizedReady : Predicate Clock Var → Prop
  | .plain φ | .upper _ _ _ _ φ | .bounded _ _ _ _ _ _ φ => φ.NormalizedReady

def judgementNormalizedReady : MixedJ Clock Var → Prop
  | .predicate p => predicateNormalizedReady p
  | .conj J K => judgementNormalizedReady J ∧ judgementNormalizedReady K
  | .reset _ J | .next J => judgementNormalizedReady J
  | _ => True

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem finite_branch_normalizedReady [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : STLTableau.ConcreteRule p R) (hp : predicateNormalizedReady (Predicate.ofFinite p))
    {B : STLTableau.Judgement Clock Var} (hB : B ∈ R.branches) :
    judgementNormalizedReady (Judgement.ofFinite B) := by
  classical
  cases hr <;>
    simp only [ExpansionRule.plainAnd, ExpansionRule.plainOr,
      ExpansionRule.plainUntil, ExpansionRule.plainRelease,
      ExpansionRule.openEventually, ExpansionRule.openAlways,
      ExpansionRule.upperAlways, ExpansionRule.boundedAlways,
      ExpansionRule.upperEventually, ExpansionRule.boundedEventually,
      List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at hB <;>
    (try split_ifs at hB) <;>
    (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hB) <;>
    rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [judgementNormalizedReady, Judgement.ofFinite,
      predicateNormalizedReady, Predicate.ofFinite,
      ExpansionRule.upperAlways_defer, ExpansionRule.upperAlways_check,
      ExpansionRule.boundedAlways_defer, ExpansionRule.boundedAlways_check,
      ExpansionRule.boundedAlways_finish, ExpansionRule.upperEventually_defer,
      ExpansionRule.upperEventually_check, ExpansionRule.boundedEventually_defer,
      ExpansionRule.boundedEventually_check, ExpansionRule.boundedEventually_finish,
      STLTableau.Judgement.markedLT_eq_clock, STLTableau.Judgement.markedGT_eq_clock]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem infinite_branch_normalizedReady [DecidableEq Clock]
    {p : UnboundedClocked.Predicate Clock Var} {Bs : List (UnboundedClocked.Node Clock Var)}
    (hr : UnboundedClocked.ConcreteRule p Bs)
    (hp : predicateNormalizedReady (Predicate.ofUnbounded p))
    {B : UnboundedClocked.Node Clock Var} (hB : B ∈ Bs) :
    judgementNormalizedReady (Judgement.ofUnbounded B) := by
  classical
  open UnboundedClocked in
    cases hr <;>
      simp only [upperAlwaysBranches, boundedAlwaysBranches, upperEventuallyBranches,
        boundedEventuallyBranches, List.mem_cons, List.not_mem_nil, or_false,
        List.mem_append] at hB <;>
      (try split_ifs at hB) <;>
      (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hB) <;>
      rcases hB with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [judgementNormalizedReady, Judgement.ofUnbounded, predicateNormalizedReady,
        Predicate.ofUnbounded, upperAlwaysDefer, upperAlwaysCheck, boundedAlwaysDefer,
        boundedAlwaysCheck, alwaysWait, alwaysLast, upperEventuallyDefer,
        upperEventuallyCheck, boundedEventuallyDefer, boundedEventuallyCheck,
        boundedEventuallyFinish, Node.lt, Node.gt]

theorem RawBranch.normalizedReady [DecidableEq Clock] {p : Predicate Clock Var}
    {B : MixedJ Clock Var} (hb : RawBranch p B) (hp : predicateNormalizedReady p) :
    judgementNormalizedReady B := by
  cases hb with
  | finite hr hm => exact finite_branch_normalizedReady hr hp hm
  | infinite hr hm => exact infinite_branch_normalizedReady hr hp hm
  | opening c m kind a φ =>
    cases kind <;>
      simpa [predicateNormalizedReady, judgementNormalizedReady, UnboundedClocked.formula,
        UnboundedClocked.opening, Judgement.ofUnbounded, Predicate.ofUnbounded] using hp

theorem ACIdem.normalizedReady_iff {J K : MixedJ Clock Var} (h : ACIdem J K) :
    judgementNormalizedReady J ↔ judgementNormalizedReady K := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ig => exact ih.trans ig
  | assoc => exact and_assoc
  | comm => exact and_comm
  | idem => exact and_self_iff
  | conj _ _ ih ig => exact and_congr ih ig
  | reset _ _ ih => exact ih
  | resetDistrib => rfl
  | resetUnused => rfl
  | resetNested => rfl

theorem withBoundaryGuard_normalizedReady (c : Clock) (b : Marker) (J : MixedJ Clock Var) :
    judgementNormalizedReady (withBoundaryGuard c b J) ↔ judgementNormalizedReady J := by
  cases b <;> simp [withBoundaryGuard, judgementNormalizedReady]

/-- All finite resolution constructors preserve the normalized input grammar in
both outputs. This does not yet address arbitrary minimal closures or graph
reachability through normalized states. -/
theorem Resolve.normalizedReady [DecidableEq Clock] {J H A : MixedJ Clock Var}
    (hd : Resolve J H A) (hi : judgementNormalizedReady J) :
    judgementNormalizedReady H ∧ judgementNormalizedReady A := by
  induction hd with
  | leaf => exact ⟨hi, hi⟩
  | conj _ _ ih ig =>
    obtain ⟨hH, hA⟩ := ih hi.1
    obtain ⟨hG, hB⟩ := ig hi.2
    exact ⟨⟨hH, hG⟩, ⟨hA, hB⟩⟩
  | reset _ _ ih => exact ih hi
  | structural he _ ih => exact ih (he.normalizedReady_iff.mp hi)
  | expandCtx hb _ _ _ ih =>
    obtain ⟨hH, hA⟩ := ih ⟨hb.normalizedReady hi.1, hi.2⟩
    exact ⟨⟨hi.1, hH⟩, hA⟩
  | expandSolo hb _ _ _ ih =>
    obtain ⟨hH, hA⟩ := ih (hb.normalizedReady hi)
    exact ⟨⟨hi, hH⟩, hA⟩
  | boundaryRequired _ _ _ ih =>
    exact ih ⟨hi.1.1, trivial, (withBoundaryGuard_normalizedReady _ _ _).mpr hi.2.2⟩
  | boundaryOptional _ _ _ ih =>
    exact ih ⟨hi.1, trivial, (withBoundaryGuard_normalizedReady _ _ _).mpr hi.2.2⟩
  | unusedReset _ _ _ _ _ ih => exact ih hi

theorem normalizedReady_plain_not_false {φ : Formula Var}
    (h : predicateNormalizedReady (Predicate.plain φ : Predicate Clock Var)) :
    φ ≠ Formula.falsity := by
  intro he
  subst φ
  exact Formula.not_normalizedReady_falsity h

end STLTableau.Section4.Finiteness
