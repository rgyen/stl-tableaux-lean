import STLTableaux.Finiteness.Inventory.SignatureNumericProvenance
import STLTableaux.Finiteness.Derivation.Branches.RawBranchNormalization

/-! Immediate-source constants of actual raw branches. Plain expansions only
 introduce zero; clocked expansions use their own interval endpoints. Numeric
 provenance does not assert that shared clock names have a consistent owner. -/
namespace STLTableau.Section4.Finiteness
open Section3
open STLTableau.ExpansionRule
open Finiteness
open scoped STL
variable {Clock Var : Type*}

noncomputable def branchConstants : Predicate Clock Var → Finset NNReal
  | .plain _ => {0}
  | .upper _ _ _ I _ | .bounded _ _ _ _ _ I _ => intervalClockConstants I

set_option maxHeartbeats 12000000 in
set_option linter.unusedSimpArgs false in
theorem finite_raw_constants [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : STLTableau.ConcreteRule p R) {Ψ : STLTableau.Judgement Clock Var}
    (hΨ : Ψ ∈ R.branches) {F : Section3.TransitionForm Clock Var}
    (hnorm : TransitionForm.normalize? (Judgement.ofFinite Ψ) = some F) :
    FormConstantsWithin (branchConstants (Predicate.ofFinite p)) F := by
  (cases hr <;>
    simp only [plainAnd,plainOr,plainUntil,plainRelease,openEventually,openAlways,
      upperAlways,boundedAlways,upperEventually,boundedEventually,
      List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hΨ <;>
    (try split_ifs at hΨ) <;>
    (try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hΨ) <;>
    rcases hΨ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    (try simp only [upperAlways_defer,upperAlways_check,boundedAlways_defer,boundedAlways_check,
      boundedAlways_finish,upperEventually_defer,upperEventually_check,
      boundedEventually_defer,boundedEventually_check,boundedEventually_finish,
      STLTableau.Judgement.markedLT_eq_clock,STLTableau.Judgement.markedGT_eq_clock] at hnorm) <;>
    simp [Judgement.ofFinite,TransitionForm.normalize?,Option.bind_some,Option.map_some,
      Section3.TransitionForm.ofState,Section3.TransitionForm.ofNextState,
      Section3.TransitionForm.union,Section3.TransitionForm.unionNext,
      Section3.TransitionForm.underReset,Section3.StateForm.union,Section3.StateForm.empty,
      Section3.StateForm.ofGuard,Section3.StateForm.ofLocal,Option.some.injEq] at hnorm <;>
    subst F <;>
    simp [FormConstantsWithin,StateConstantsWithin,branchConstants,rootClockConstants,intervalClockConstants,
      Section3.Predicate.formula,Section3.Predicate.ofFinite,IntervalPredicate.formula,Formula.eventually,Formula.always,
      Section3.StateForm.union,Section3.StateForm.empty,Section3.StateForm.ofLocal,
      Section3.StateForm.ofGuard]
  all_goals repeat' first | apply And.intro | apply reset_union | apply reset_empty
  all_goals (apply reset_singleton; simp [branchConstants,rootClockConstants,intervalClockConstants,
    Section3.Predicate.formula,Section3.Predicate.ofFinite,IntervalPredicate.formula,Formula.eventually,Formula.always])

set_option maxHeartbeats 12000000 in
set_option linter.unusedSimpArgs false in
/-- Infinite clocked raw branches have the same direct label support. -/
theorem infinite_raw_constants [DecidableEq Clock]
    {p : UnboundedClocked.Predicate Clock Var} {Bs : List (UnboundedClocked.Node Clock Var)}
    (hr : UnboundedClocked.ConcreteRule p Bs) {Ψ : UnboundedClocked.Node Clock Var}
    (hΨ : Ψ ∈ Bs) {F : Section3.TransitionForm Clock Var}
    (hnorm : TransitionForm.normalize? (Judgement.ofUnbounded Ψ) = some F) :
    FormConstantsWithin (branchConstants (Predicate.ofUnbounded p)) F := by
  open UnboundedClocked in
    (cases hr <;>
      simp only [upperAlwaysBranches, boundedAlwaysBranches, upperEventuallyBranches,
        boundedEventuallyBranches, List.mem_cons, List.not_mem_nil, or_false,
        List.mem_append] at hΨ <;>
      (try split_ifs at hΨ) <;>
      (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hΨ) <;>
      rcases hΨ with rfl | rfl | rfl | rfl | rfl | rfl) <;>
      (try simp only [upperAlwaysDefer, upperAlwaysCheck, boundedAlwaysDefer, boundedAlwaysCheck,
        alwaysWait, alwaysLast, upperEventuallyDefer, upperEventuallyCheck,
        boundedEventuallyDefer, boundedEventuallyCheck, boundedEventuallyFinish,
        UnboundedClocked.Node.lt, UnboundedClocked.Node.gt] at hnorm) <;>
    simp [Judgement.ofUnbounded,TransitionForm.normalize?,Option.bind_some,Option.map_some,
      Section3.TransitionForm.ofState,Section3.TransitionForm.ofNextState,
      Section3.TransitionForm.union,Section3.TransitionForm.unionNext,
      Section3.TransitionForm.underReset,Section3.StateForm.union,Section3.StateForm.empty,
      Section3.StateForm.ofGuard,Section3.StateForm.ofLocal,Option.some.injEq] at hnorm <;>
    subst F <;>
    simp [FormConstantsWithin,StateConstantsWithin,branchConstants,rootClockConstants,intervalClockConstants,
      Section3.Predicate.formula,Section3.Predicate.ofUnbounded,UnboundedClocked.formula,Formula.eventually,Formula.always,
      Section3.StateForm.union,Section3.StateForm.empty,Section3.StateForm.ofLocal,
      Section3.StateForm.ofGuard]
  all_goals repeat' first | apply And.intro | apply reset_union | apply reset_empty
  all_goals (apply reset_singleton; simp [branchConstants,rootClockConstants,intervalClockConstants,
    Section3.Predicate.formula,Section3.Predicate.ofUnbounded,UnboundedClocked.formula,Formula.eventually,Formula.always])



set_option linter.unusedSimpArgs false in
theorem opening_zero_constants [DecidableEq Clock]
    (c : Clock) (m : Marker) (kind : TemporalKind) (a : NNReal) (φ : Formula Var)
    {F : Section3.TransitionForm Clock Var}
    (hnorm : TransitionForm.normalize?
      (Judgement.ofUnbounded (UnboundedClocked.opening c m kind a φ)) = some F) :
    FormConstantsWithin ({0} : Finset NNReal) F := by
  cases kind <;>
    simp only [UnboundedClocked.opening] at hnorm <;>
    simp [Judgement.ofUnbounded,TransitionForm.normalize?,Option.bind_some,Option.map_some,
      Section3.TransitionForm.ofState,Section3.TransitionForm.ofNextState,
      Section3.TransitionForm.union,Section3.TransitionForm.unionNext,
      Section3.TransitionForm.underReset,Section3.StateForm.union,Section3.StateForm.empty,
      Section3.StateForm.ofGuard,Section3.StateForm.ofLocal,Option.some.injEq] at hnorm <;>
    subst F <;>
    simp [FormConstantsWithin,StateConstantsWithin,rootClockConstants,intervalClockConstants,
      Formula.eventually,Section3.StateForm.union,Section3.StateForm.empty,
      Section3.StateForm.ofLocal,Section3.StateForm.ofGuard]
  all_goals repeat' first | apply And.intro | apply reset_union | apply reset_empty
  all_goals (apply reset_singleton; simp [rootClockConstants,intervalClockConstants,Formula.eventually])


/-- All literal numeric annotations, retaining their clock names and including
 next payloads and reset binders even when a later union overwrites them. -/
def RawConstantsWithin (C : Finset NNReal) : MixedJ Clock Var → Prop
  | .clock _ _ a => a ∈ C
  | .conj J K => RawConstantsWithin C J ∧ RawConstantsWithin C K
  | .reset R J => ResetConstantsWithin C R ∧ RawConstantsWithin C J
  | .next J => RawConstantsWithin C J
  | _ => True

set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
private theorem finite_literal_constants [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : STLTableau.ConcreteRule p R) {Ψ : STLTableau.Judgement Clock Var}
    (hΨ : Ψ ∈ R.branches) :
    RawConstantsWithin (branchConstants (Predicate.ofFinite p)) (Judgement.ofFinite Ψ) := by
  (cases hr <;>
    simp only [plainAnd,plainOr,plainUntil,plainRelease,openEventually,openAlways,
      upperAlways,boundedAlways,upperEventually,boundedEventually,
      List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hΨ <;>
    (try split_ifs at hΨ) <;>
    (try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hΨ) <;>
    rcases hΨ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    (try simp only [upperAlways_defer,upperAlways_check,boundedAlways_defer,boundedAlways_check,
      boundedAlways_finish,upperEventually_defer,upperEventually_check,
      boundedEventually_defer,boundedEventually_check,boundedEventually_finish,
      STLTableau.Judgement.markedLT_eq_clock,STLTableau.Judgement.markedGT_eq_clock] )
  all_goals simp [RawConstantsWithin,Judgement.ofFinite,Judgement.ofUnbounded,
    branchConstants,Predicate.ofFinite,Predicate.ofUnbounded,intervalClockConstants]
  all_goals repeat' first | apply And.intro | exact reset_empty _ | refine reset_singleton _ _ _ ?_ | refine reset_union _ _ _ ?_ ?_
  all_goals try simp [branchConstants,intervalClockConstants]

set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
private theorem infinite_literal_constants [DecidableEq Clock]
    {p : UnboundedClocked.Predicate Clock Var} {Bs : List (UnboundedClocked.Node Clock Var)}
    (hr : UnboundedClocked.ConcreteRule p Bs) {Ψ : UnboundedClocked.Node Clock Var}
    (hΨ : Ψ ∈ Bs) :
    RawConstantsWithin (branchConstants (Predicate.ofUnbounded p)) (Judgement.ofUnbounded Ψ) := by
  open UnboundedClocked in
    (cases hr <;>
      simp only [upperAlwaysBranches, boundedAlwaysBranches, upperEventuallyBranches,
        boundedEventuallyBranches, List.mem_cons, List.not_mem_nil, or_false,
        List.mem_append] at hΨ <;>
      (try split_ifs at hΨ) <;>
      (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hΨ) <;>
      rcases hΨ with rfl | rfl | rfl | rfl | rfl | rfl) <;>
      (try simp only [upperAlwaysDefer, upperAlwaysCheck, boundedAlwaysDefer, boundedAlwaysCheck,
        alwaysWait, alwaysLast, upperEventuallyDefer, upperEventuallyCheck,
        boundedEventuallyDefer, boundedEventuallyCheck, boundedEventuallyFinish,
        UnboundedClocked.Node.lt, UnboundedClocked.Node.gt] )
  all_goals simp [RawConstantsWithin,Judgement.ofFinite,Judgement.ofUnbounded,
    branchConstants,Predicate.ofFinite,Predicate.ofUnbounded,intervalClockConstants]
  all_goals repeat' first | apply And.intro | exact reset_empty _ | refine reset_singleton _ _ _ ?_ | refine reset_union _ _ _ ?_ ?_
  all_goals try simp [branchConstants,intervalClockConstants]

theorem RawBranch.raw_constants [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B) :
    RawConstantsWithin (branchConstants p) B := by
  cases h with
  | finite hr hm => exact finite_literal_constants hr hm
  | infinite hr hm => exact infinite_literal_constants hr hm
  | opening c m kind a φ =>
      cases kind <;> simp [UnboundedClocked.opening,Judgement.ofUnbounded,
        RawConstantsWithin,branchConstants]
      all_goals apply reset_singleton; simp

theorem RawBranch.normalized_constants [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B)
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization B F) :
    FormConstantsWithin (branchConstants p) F := by
  cases h with
  | finite hr hm => exact finite_raw_constants hr hm hSafe.normalizes
  | infinite hr hm => exact infinite_raw_constants hr hm hSafe.normalizes
  | opening c m kind a φ => exact opening_zero_constants c m kind a φ hSafe.normalizes

end STLTableau.Section4.Finiteness
