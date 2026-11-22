import STLTableaux.Closure.Catalogue.FaithfulContextualCatalogue

/-! Actual guard thresholds and reset values are interval endpoints or zero.
No elapsed value, difference of endpoints, or expansion count is included. -/
namespace STLTableau.Section4.Finiteness
open Section3
open STLTableau.ExpansionRule
open scoped STL
variable {Clock Var : Type*}

noncomputable def intervalClockConstants : TimeInterval → Finset NNReal
  | .bounded I => by
    classical
    exact {0,⟨I.lower,I.lower_nonnegative⟩,⟨I.upper,I.lower_nonnegative.trans I.nonSingular.le⟩}
  | .unbounded a => by
    classical
    exact {0,a}

noncomputable def rootClockConstants : Formula Var → Finset NNReal
  | .truth | .atom _ => {0}
  | .neg φ => rootClockConstants φ
  | .and φ ψ => by
    classical
    exact rootClockConstants φ ∪ rootClockConstants ψ
  | .until I φ ψ => by
    classical
    exact intervalClockConstants I ∪ rootClockConstants φ ∪ rootClockConstants ψ

def ResetConstantsWithin (C : Finset NNReal) (Λ : ClockResetSet Clock) : Prop :=
  ∀ c a, Λ.value c = some a → a ∈ C

theorem reset_empty (C : Finset NNReal) :
    ResetConstantsWithin C (ClockResetSet.empty : ClockResetSet Clock) := by
  intro c a h
  change (Option.none : Option NNReal) = some a at h
  cases h

theorem reset_singleton [DecidableEq Clock] (C : Finset NNReal)
    (c : Clock) (a : NNReal) (ha : a ∈ C) : ResetConstantsWithin C (ClockResetSet.singleton c a) := by
  intro d b h
  by_cases hd : d = c
  · have he : a = b := by simpa only [ClockResetSet.singleton,if_pos hd,Option.some.injEq] using h
    exact he ▸ ha
  · simp only [ClockResetSet.singleton,if_neg hd] at h
    cases h

theorem reset_union (C : Finset NNReal) (Λ Γ : ClockResetSet Clock)
    (hΛ : ResetConstantsWithin C Λ) (hΓ : ResetConstantsWithin C Γ) :
    ResetConstantsWithin C (Λ.union Γ) := by
  intro c a h
  cases he : Λ.value c with
  | none => exact hΓ c a (by simpa only [ClockResetSet.union,he] using h)
  | some b =>
    have hb : b = a := by simpa only [ClockResetSet.union,he,Option.some.injEq] using h
    exact hb ▸ hΛ c b he

def StateConstantsWithin (C : Finset NNReal) (S : Section3.StateForm Clock Var) : Prop :=
  (∀ g ∈ S.guards, g.bound ∈ C) ∧ ResetConstantsWithin C S.resets

def FormConstantsWithin (C : Finset NNReal) (F : Section3.TransitionForm Clock Var) : Prop :=
  StateConstantsWithin C F.current ∧ ∀ N,F.nextPart = some N → StateConstantsWithin C N

set_option maxHeartbeats 12000000 in
set_option linter.unusedSimpArgs false in
theorem finite_raw_branch_numeric_constants [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : STLTableau.ConcreteRule p R) {Ψ : STLTableau.Judgement Clock Var}
    (hΨ : Ψ ∈ R.branches) {F : Section3.TransitionForm Clock Var}
    (hnorm : TransitionForm.normalize? (Judgement.ofFinite Ψ) = some F) :
    FormConstantsWithin (rootClockConstants (Predicate.ofFinite p).formula) F := by
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
    simp [FormConstantsWithin,StateConstantsWithin,rootClockConstants,intervalClockConstants,
      Section3.Predicate.formula,Section3.Predicate.ofFinite,IntervalPredicate.formula,Formula.eventually,Formula.always,
      Section3.StateForm.union,Section3.StateForm.empty,Section3.StateForm.ofLocal,
      Section3.StateForm.ofGuard]
  all_goals repeat' first | apply And.intro | apply reset_union | apply reset_empty
  all_goals (apply reset_singleton; simp [rootClockConstants,intervalClockConstants,
    Section3.Predicate.formula,Section3.Predicate.ofFinite,IntervalPredicate.formula,Formula.eventually,Formula.always])

set_option maxHeartbeats 12000000 in
set_option linter.unusedSimpArgs false in
/-- Infinite clocked raw branches have the same direct label support. -/
theorem infinite_raw_branch_numeric_constants [DecidableEq Clock]
    {p : UnboundedClocked.Predicate Clock Var} {Bs : List (UnboundedClocked.Node Clock Var)}
    (hr : UnboundedClocked.ConcreteRule p Bs) {Ψ : UnboundedClocked.Node Clock Var}
    (hΨ : Ψ ∈ Bs) {F : Section3.TransitionForm Clock Var}
    (hnorm : TransitionForm.normalize? (Judgement.ofUnbounded Ψ) = some F) :
    FormConstantsWithin (rootClockConstants (Predicate.ofUnbounded p).formula) F := by
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
    simp [FormConstantsWithin,StateConstantsWithin,rootClockConstants,intervalClockConstants,
      Section3.Predicate.formula,Section3.Predicate.ofUnbounded,UnboundedClocked.formula,Formula.eventually,Formula.always,
      Section3.StateForm.union,Section3.StateForm.empty,Section3.StateForm.ofLocal,
      Section3.StateForm.ofGuard]
  all_goals repeat' first | apply And.intro | apply reset_union | apply reset_empty
  all_goals (apply reset_singleton; simp [rootClockConstants,intervalClockConstants,
    Section3.Predicate.formula,Section3.Predicate.ofUnbounded,UnboundedClocked.formula,Formula.eventually,Formula.always])

set_option linter.unusedSimpArgs false in
/-- Opening clocks occur in the emitted current upper label. -/
theorem opening_raw_branch_numeric_constants [DecidableEq Clock]
    (c : Clock) (m : Marker) (kind : TemporalKind) (a : NNReal) (φ : Formula Var)
    {F : Section3.TransitionForm Clock Var}
    (hnorm : TransitionForm.normalize?
      (Judgement.ofUnbounded (UnboundedClocked.opening c m kind a φ)) = some F) :
    FormConstantsWithin (rootClockConstants (Formula.eventually (.unbounded a) φ)) F := by
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

theorem reset_rename_iff (C : Finset NNReal) (Λ : ClockResetSet Clock)
    (e : Equiv.Perm Clock) : ResetConstantsWithin C (Λ.rename e) ↔ ResetConstantsWithin C Λ := by
  constructor
  · intro h c a ha
    apply h (e c) a
    simpa only [ClockResetSet.rename,Equiv.symm_apply_apply] using ha
  · intro h c a ha
    exact h (e.symm c) a ha

theorem state_rename_iff (C : Finset NNReal) (S : Section3.StateForm Clock Var)
    (e : Equiv.Perm Clock) : StateConstantsWithin C (S.rename e) ↔ StateConstantsWithin C S := by
  constructor
  · intro h
    refine ⟨fun g hg => h.1 (Guard.rename e g) ⟨g,hg,rfl⟩,
      (reset_rename_iff C S.resets e).mp h.2⟩
  · intro h
    refine ⟨?_,(reset_rename_iff C S.resets e).mpr h.2⟩
    rintro g ⟨g,hg,rfl⟩
    exact h.1 g hg

private theorem state_alphaReset_iff (C : Finset NNReal) (S : Section3.StateForm Clock Var)
    (e : Equiv.Perm Clock) : StateConstantsWithin C (S.alphaReset e) ↔ StateConstantsWithin C S := by
  exact and_congr Iff.rfl (reset_rename_iff C S.resets e)

/-- Scoped alpha conversion changes names, never numeric thresholds or resets. -/
theorem alpha_numeric_constants_iff (C : Finset NNReal)
    {F G : Section3.TransitionForm Clock Var} (h : Section3.TransitionForm.AlphaEquivalent F G) :
    FormConstantsWithin C F ↔ FormConstantsWithin C G := by
  induction h with
  | refl => rfl
  | outer F e hf =>
    apply and_congr (state_alphaReset_iff C F.current e)
    cases hn : F.nextPart with
    | none => simp [Section3.TransitionForm.alphaOuter,hn]
    | some N =>
      simpa only [Section3.TransitionForm.alphaOuter,hn,Option.map_some,
        Option.some.injEq,forall_eq'] using state_rename_iff C N e
  | next F e hf =>
    apply and_congr Iff.rfl
    cases hn : F.nextPart with
    | none => simp [Section3.TransitionForm.alphaNext,hn]
    | some N =>
      simpa only [Section3.TransitionForm.alphaNext,hn,Option.map_some,
        Option.some.injEq,forall_eq'] using state_alphaReset_iff C N e
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig

/-- Enclosing assignments must themselves be confined; they are not silently
classified as raw rule constants. -/
theorem underReset_numeric_constants (C : Finset NNReal)
    (F : Section3.TransitionForm Clock Var) (Γ : ClockResetSet Clock)
    (hF : FormConstantsWithin C F) (hΓ : ResetConstantsWithin C Γ) :
    FormConstantsWithin C (F.underReset Γ) :=
  ⟨⟨hF.1.1,reset_union C F.current.resets Γ hF.1.2 hΓ⟩,hF.2⟩

/-- Every root inventory contains zero. -/
theorem zero_mem_rootClockConstants (root : Formula Var) : 0 ∈ rootClockConstants root := by
  classical
  induction root with
  | truth | atom => simp [rootClockConstants]
  | neg φ ih => exact ih
  | and φ ψ ihφ ihψ => exact Finset.mem_union_left _ ihφ
  | «until» I φ ψ ihφ ihψ => exact Finset.mem_union_right _ ihψ

/-- Literal syntactic subformula confinement entails numeric confinement. -/
theorem rootClockConstants_mono {φ root : Formula Var} (h : φ ≼ root) :
    rootClockConstants φ ⊆ rootClockConstants root := by
  classical
  induction h with
  | refl => exact Finset.Subset.refl _
  | neg h ih => exact ih
  | and_left h ih => exact fun a ha => Finset.mem_union_left _ (ih ha)
  | and_right h ih => exact fun a ha => Finset.mem_union_right _ (ih ha)
  | until_left h ih => exact fun a ha => Finset.mem_union_left _ (Finset.mem_union_right _ (ih ha))
  | until_right h ih => exact fun a ha => Finset.mem_union_right _ (ih ha)

theorem numeric_mono {C D : Finset NNReal} (hCD : C ⊆ D)
    {F : Section3.TransitionForm Clock Var} (h : FormConstantsWithin C F) :
    FormConstantsWithin D F :=
  ⟨⟨fun g hg => hCD (h.1.1 g hg),fun c a ha => hCD (h.1.2 c a ha)⟩,
    fun N hN => ⟨fun g hg => hCD ((h.2 N hN).1 g hg),
      fun c a ha => hCD ((h.2 N hN).2 c a ha)⟩⟩

/-- Every actual raw mixed branch is confined to its source formula's constants. -/
theorem mixed_branch_numeric_constants [DecidableEq Clock]
    {p : Predicate Clock Var} {R : Section3.TransitionForm Clock Var}
    (h : ConcreteMixed.catalogue.Branch p ClockResetSet.empty R) :
    FormConstantsWithin (rootClockConstants p.formula) R := by
  rcases h with h | h | h
  · obtain ⟨p,E,Ψ,F,rfl,hr,hm,hn,rfl⟩ := h
    exact underReset_numeric_constants _ F _ (finite_raw_branch_numeric_constants hr hm hn)
      (reset_empty _)
  · obtain ⟨p,E,Ψ,F,rfl,hr,hm,hn,rfl⟩ := h
    exact underReset_numeric_constants _ F _ (infinite_raw_branch_numeric_constants hr hm hn)
      (reset_empty _)
  · obtain ⟨c,m,kind,a,φ,F,rfl,hn,rfl⟩ := h
    apply underReset_numeric_constants _ F _ _ (reset_empty _)
    have hh := opening_raw_branch_numeric_constants c m kind a φ hn
    cases kind <;> exact hh

/-- Actual scoped branches introduce only root constants; inherited assignments
are required to be confined explicitly and may otherwise contain arbitrary values. -/
theorem contextual_branch_numeric_constants [DecidableEq Clock]
    (root : Formula Var) {p : Predicate Clock Var} {Γ : ClockResetSet Clock}
    {B : Section3.TransitionForm Clock Var}
    (hb : ConcreteContextual.catalogue.Branch p Γ B) (hp : p.formula ≼ root)
    (hΓ : ResetConstantsWithin (rootClockConstants root) Γ) :
    FormConstantsWithin (rootClockConstants root) B := by
  obtain ⟨R,A,hR,ha,rfl⟩ := hb
  apply underReset_numeric_constants _ A Γ _ hΓ
  apply numeric_mono (rootClockConstants_mono hp)
  exact (alpha_numeric_constants_iff _ ha).mpr (mixed_branch_numeric_constants hR)

end STLTableau.Section4.Finiteness
