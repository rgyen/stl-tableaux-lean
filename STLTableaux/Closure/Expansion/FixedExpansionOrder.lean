import STLTableaux.Closure.Expansion.MinimalClosureReachability

/-! Fixed predicate enumeration for complete expansion rounds. Every branch
remains available, and every minimal closure is reached at a zero-rank level. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}

namespace ExpansionFamily

/-- Process the prescribed current-predicate list, retaining all step choices. -/
def fixedRound (Step : Predicate Clock Var → TransitionForm Clock Var →
    TransitionForm Clock Var → Prop)
    (order : TransitionForm Clock Var → List (Predicate Clock Var))
    (F G : TransitionForm Clock Var) : Prop :=
  Sequence Step (order F) F G

/-- Complete-round expansion levels with a fixed enumeration at each judgement. -/
def fixedLevel (Step : Predicate Clock Var → TransitionForm Clock Var →
    TransitionForm Clock Var → Prop)
    (order : TransitionForm Clock Var → List (Predicate Clock Var))
    (F : TransitionForm Clock Var) : ℕ → Set (TransitionForm Clock Var)
  | 0 => {F}
  | i + 1 => {G | ∃ H ∈ fixedLevel Step order F i, fixedRound Step order H G}

theorem fixedLevel_subset
    {Step : Predicate Clock Var → TransitionForm Clock Var → TransitionForm Clock Var → Prop}
    (order : TransitionForm Clock Var → List (Predicate Clock Var))
    (enumerates : ∀ F, EnumeratesCurrent (order F) F)
    (F : TransitionForm Clock Var) (i : ℕ) :
    fixedLevel Step order F i ⊆ level Step F i := by
  induction i with
  | zero => exact Set.Subset.refl _
  | succ i ih =>
    rintro G ⟨H, hH, sequence⟩
    exact ⟨H, ih hH, order H, enumerates H, sequence⟩

theorem fixedLevel_mono
    {Step Step' : Predicate Clock Var → TransitionForm Clock Var →
      TransitionForm Clock Var → Prop}
    (includeStep : ∀ {p F G}, Step p F G → Step' p F G)
    (order : TransitionForm Clock Var → List (Predicate Clock Var))
    (F : TransitionForm Clock Var) (i : ℕ) :
    fixedLevel Step order F i ⊆ fixedLevel Step' order F i := by
  induction i with
  | zero => exact Set.Subset.refl _
  | succ i ih =>
    rintro G ⟨H, hH, sequence⟩
    exact ⟨H, ih hH, sequence.mono includeStep⟩

end ExpansionFamily

namespace ClosureCatalogue

abbrev FixedExpansionRound (E : ClosureCatalogue Clock Var) :=
  ExpansionFamily.fixedRound E.PExpansion

abbrev fixedExpansionLevel (E : ClosureCatalogue Clock Var) :=
  ExpansionFamily.fixedLevel E.PExpansion

end ClosureCatalogue

namespace ConcreteContextual
variable [DecidableEq Clock]

abbrev fixedAlphaExpansionLevel :=
  ExpansionFamily.fixedLevel (AlphaPExpansion (Clock := Clock) (Var := Var))

/-- The bounded-upper-closure induction, using the given order
rather than choosing a new enumeration at each round. -/
theorem literal_fixed_level_below
    (order : TransitionForm Clock Var → List (Predicate Clock Var))
    (enumerates : ∀ F, ExpansionFamily.EnumeratesCurrent (order F) F)
    (F U : TransitionForm Clock Var) (extension : SyntacticallySubsumed F U)
    (closed : catalogue.IsClosed U) (i : ℕ) :
    ∃ G ∈ catalogue.fixedExpansionLevel order F i,
      SyntacticallySubsumed F G ∧ SyntacticallySubsumed G U := by
  induction i with
  | zero => exact ⟨F, rfl, .refl F, extension⟩
  | succ i ih =>
    obtain ⟨H, member, source, upper⟩ := ih
    obtain ⟨G, sequence, step, target⟩ := literal_sequence_below (order H) H U
      (fun p hp => ((enumerates H).2 p).1 hp) upper closed
    exact ⟨G, ⟨H, member, sequence⟩, source.trans step, target⟩

/-- Every given minimal closure occurs at the specified zero-rank level,
not merely at some later level depending on that closure. -/
theorem minimal_closure_mem_fixed_expansion_level_at_rank_zero
    (order : TransitionForm Clock Var → List (Predicate Clock Var))
    (enumerates : ∀ F, ExpansionFamily.EnumeratesCurrent (order F) F)
    {F U : TransitionForm Clock Var} (closure : catalogue.IsClosure F U)
    (k : ℕ) (zero : literalLevelRank F k = 0) :
    U ∈ catalogue.fixedExpansionLevel order F k := by
  obtain ⟨G, member, source, upper⟩ :=
    literal_fixed_level_below order enumerates F U closure.extension closure.closed k
  have allClosed := (ExpansionFamily.familyRank_zero_iff_closed
    (literal_expansionLevel_bounded F k)).1 zero
  have closed : catalogue.IsClosed G :=
    allClosed G (ExpansionFamily.fixedLevel_subset order enumerates F k member)
  have reverse := closure.minimal G source closed upper
  exact (upper.antisymm reverse) ▸ member

/-- The same exact-level statement for the appendix's explicit alpha family.
Literal choices are admitted alpha choices; no converse family equality is used. -/
theorem minimal_closure_mem_fixed_alpha_expansion_level_at_rank_zero
    (order : TransitionForm Clock Var → List (Predicate Clock Var))
    (enumerates : ∀ F, ExpansionFamily.EnumeratesCurrent (order F) F)
    {F U : TransitionForm Clock Var} (closure : catalogue.IsClosure F U)
    (k : ℕ) (zero : alphaLevelRank F k = 0) :
    U ∈ fixedAlphaExpansionLevel order F k := by
  obtain ⟨G, literal, source, upper⟩ :=
    literal_fixed_level_below order enumerates F U closure.extension closure.closed k
  have member : G ∈ fixedAlphaExpansionLevel order F k :=
    ExpansionFamily.fixedLevel_mono
      (fun {p H K} step => ⟨H, NextAlphaPath.refl H, step⟩) order F k literal
  have allClosed := (ExpansionFamily.familyRank_zero_iff_closed
    (alpha_expansionLevel_bounded F k)).1 zero
  have closed : catalogue.IsClosed G :=
    allClosed G (ExpansionFamily.fixedLevel_subset order enumerates F k member)
  have reverse := closure.minimal G source closed upper
  exact (upper.antisymm reverse) ▸ member

/-- Every minimal closure is reached at a zero-rank level using its fixed
bound-clock representatives. -/
theorem fixed_expansion_order_correct
    (order : TransitionForm Clock Var → List (Predicate Clock Var))
    (enumerates : ∀ F, ExpansionFamily.EnumeratesCurrent (order F) F)
    (F : TransitionForm Clock Var) (k : ℕ) (zero : literalLevelRank F k = 0) :
    catalogue.fixedExpansionLevel order F k ⊆ catalogue.expansionLevel F k ∧
      ∀ U, catalogue.IsClosure F U →
        U ∈ catalogue.fixedExpansionLevel order F k ∧ U ∈ catalogue.expansionLevel F k := by
  have subset := ExpansionFamily.fixedLevel_subset order enumerates F k
    (Step := catalogue.PExpansion)
  refine ⟨subset, ?_⟩
  intro U closure
  have member := minimal_closure_mem_fixed_expansion_level_at_rank_zero
    order enumerates closure k zero
  exact ⟨member, subset member⟩

/-- Explicit-alpha counterpart, retaining every permitted alpha expansion
branch while fixing only the current-predicate enumeration. -/
theorem fixed_alpha_expansion_order_correct
    (order : TransitionForm Clock Var → List (Predicate Clock Var))
    (enumerates : ∀ F, ExpansionFamily.EnumeratesCurrent (order F) F)
    (F : TransitionForm Clock Var) (k : ℕ) (zero : alphaLevelRank F k = 0) :
    fixedAlphaExpansionLevel order F k ⊆ alphaExpansionLevel F k ∧
      ∀ U, catalogue.IsClosure F U →
        U ∈ fixedAlphaExpansionLevel order F k ∧ U ∈ alphaExpansionLevel F k := by
  have subset := ExpansionFamily.fixedLevel_subset order enumerates F k
    (Step := AlphaPExpansion)
  refine ⟨subset, ?_⟩
  intro U closure
  have member := minimal_closure_mem_fixed_alpha_expansion_level_at_rank_zero
    order enumerates closure k zero
  exact ⟨member, subset member⟩

end ConcreteContextual

run_elab do
  for name in #[``ExpansionFamily.fixedLevel_subset, ``ExpansionFamily.fixedLevel_mono,
      ``ConcreteContextual.literal_fixed_level_below,
      ``ConcreteContextual.minimal_closure_mem_fixed_expansion_level_at_rank_zero,
      ``ConcreteContextual.minimal_closure_mem_fixed_alpha_expansion_level_at_rank_zero,
      ``ConcreteContextual.fixed_expansion_order_correct,
      ``ConcreteContextual.fixed_alpha_expansion_order_correct] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end STLTableau.Section3
