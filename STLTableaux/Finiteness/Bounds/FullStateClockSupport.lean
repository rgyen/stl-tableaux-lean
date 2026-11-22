import STLTableaux.Tableau.Construction.TableauState
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Clock accounting for the full generator/current/next state.
Temporal labels are retained. Reset clocks and guard clocks are counted even
when bound or absent from free-clock support. These are structural bounds;
a root-formula bound on the component sizes is a separate proof obligation. -/
namespace STLTableau.Section4.Finiteness
variable {Clock Var : Type*} [DecidableEq Clock]

/-- All clocks of a local, including temporal interval endpoints. -/
def localClockNames : Section3.Local Clock Var → Finset Clock
  | .terminal | .marker _ | .predicate (.plain _) => ∅
  | .predicate (.upper c _ _ _ _) => {c}
  | .predicate (.bounded c d _ _ _ _ _) => {c, d}

theorem localClockNames_card_le (l : Section3.Local Clock Var) :
    (localClockNames l).card ≤ 2 := by
  cases l with
  | terminal => simp [localClockNames]
  | marker m => simp [localClockNames]
  | predicate p =>
    cases p with
    | plain φ => simp [localClockNames]
    | upper c b kind I φ => simp [localClockNames]
    | bounded c d b q kind I φ =>
      exact (Finset.card_insert_le _ _).trans (by simp)

theorem mem_localClockNames (l : Section3.Local Clock Var) (c : Clock) :
    c ∈ localClockNames l ↔ c ∈ l.freeClocks := by
  cases l with
  | terminal => simp [localClockNames, Section3.Local.freeClocks,
      Section3.Local.toJudgement, Section3.Judgement.freeClocks]
  | marker m => simp [localClockNames, Section3.Local.freeClocks,
      Section3.Local.toJudgement, Section3.Judgement.freeClocks]
  | predicate p =>
    cases p <;> simp [localClockNames, Section3.Local.freeClocks,
      Section3.Local.toJudgement, Section3.Judgement.freeClocks]

noncomputable def stateLocalClockNames (S : Section3.StateForm Clock Var) : Finset Clock := by
  classical
  exact S.locals_finite.toFinset.biUnion localClockNames

noncomputable def stateClockNames (S : Section3.StateForm Clock Var) : Finset Clock := by
  classical
  exact S.guards_finite.toFinset.image Section3.Guard.clock ∪
    S.resets.finite_domain.toFinset ∪ stateLocalClockNames S

/-- The two-clock factor applies to every local, not only atomic labels. -/
theorem stateLocalClockNames_card_le (S : Section3.StateForm Clock Var) :
    (stateLocalClockNames S).card ≤ 2 * S.locals.ncard := by
  classical
  calc
    (stateLocalClockNames S).card ≤
        ∑ l ∈ S.locals_finite.toFinset, (localClockNames l).card := Finset.card_biUnion_le
    _ ≤ ∑ _l ∈ S.locals_finite.toFinset, 2 :=
      Finset.sum_le_sum (fun l _ => localClockNames_card_le l)
    _ = 2 * S.locals.ncard := by
      simp [Set.ncard_eq_toFinset_card S.locals S.locals_finite, Nat.mul_comm]

/-- Every guard, reset and local occurrence is included in the support. -/
theorem mem_stateClockNames (S : Section3.StateForm Clock Var) (c : Clock) :
    c ∈ stateClockNames S ↔
      c ∈ S.guardClocks ∨ c ∈ S.resets.clocks ∨ c ∈ S.localClocks := by
  classical
  simp only [stateClockNames, stateLocalClockNames, Finset.mem_union, Finset.mem_image,
    Set.Finite.mem_toFinset, Finset.mem_biUnion, mem_localClockNames]
  change ((∃ g, g ∈ S.guards ∧ g.clock = c) ∨ c ∈ S.resets.clocks) ∨
    (∃ l, l ∈ S.locals ∧ c ∈ l.freeClocks) ↔ _
  exact or_assoc

/-- Guards and resets must be bounded as well as temporal locals. -/
noncomputable def stateClockBudget (S : Section3.StateForm Clock Var) : ℕ :=
  S.guards.ncard + S.resets.clocks.ncard + 2 * S.locals.ncard

theorem stateClockNames_card_le (S : Section3.StateForm Clock Var) :
    (stateClockNames S).card ≤ stateClockBudget S := by
  classical
  calc
    (stateClockNames S).card ≤
        (S.guards_finite.toFinset.image Section3.Guard.clock ∪
          S.resets.finite_domain.toFinset).card + (stateLocalClockNames S).card :=
      Finset.card_union_le _ _
    _ ≤ (S.guards_finite.toFinset.image Section3.Guard.clock).card +
        S.resets.finite_domain.toFinset.card + (stateLocalClockNames S).card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ S.guards_finite.toFinset.card + S.resets.finite_domain.toFinset.card +
        2 * S.locals.ncard := by
      exact Nat.add_le_add (Nat.add_le_add_right Finset.card_image_le _)
        (stateLocalClockNames_card_le S)
    _ = stateClockBudget S := by
      unfold stateClockBudget
      rw [Set.ncard_eq_toFinset_card S.guards S.guards_finite,
        Set.ncard_eq_toFinset_card S.resets.clocks S.resets.finite_domain]
      congr 2

/-- Complete clock support of the three components of a representative state. -/
noncomputable def wholeClockNames (s : ClosureState Clock Var) : Finset Clock :=
  stateClockNames s.generator ∪ stateClockNames s.form.current ∪
    match s.form.nextPart with
    | none => ∅
    | some N => stateClockNames N

noncomputable def wholeClockBudget (s : ClosureState Clock Var) : ℕ :=
  stateClockBudget s.generator + stateClockBudget s.form.current +
    match s.form.nextPart with
    | none => 0
    | some N => stateClockBudget N

theorem wholeClockNames_card_le (s : ClosureState Clock Var) :
    (wholeClockNames s).card ≤ wholeClockBudget s := by
  have hg := stateClockNames_card_le s.generator
  have hc := stateClockNames_card_le s.form.current
  have h₁ := Finset.card_union_le (stateClockNames s.generator) (stateClockNames s.form.current)
  cases hn : s.form.nextPart with
  | none =>
    simp only [wholeClockNames, wholeClockBudget, hn, Finset.union_empty, Nat.add_zero]
    omega
  | some N =>
    have hncard := stateClockNames_card_le N
    have h₂ := Finset.card_union_le
      (stateClockNames s.generator ∪ stateClockNames s.form.current) (stateClockNames N)
    simp only [wholeClockNames, wholeClockBudget, hn]
    omega

end STLTableau.Section4.Finiteness
