/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Closure.Expansion.FaithfulLevelRankBounds
import STLTableaux.Examples.UpperAlwaysClosure

/-! Transition form (Example 4.2), syntactic subsumption (Example 4.4),
rule-closure (Example 4.7), and a minimal closure (Example 4.9). -/

namespace STLTableau.Examples.TransitionForms
open STLTableau
open STLTableau.Section3

inductive Clock where
  | c | d
  deriving DecidableEq
inductive Variable where
  | x | u
  deriving DecidableEq

def ge (v : Variable) (a : ℝ) : STLTableau.Formula Variable :=
  .atom ⟨1, fun _ => v, fun z => a - z 0, .le⟩

def interval23 : STLTableau.BoundedTimeInterval := ⟨2, 3, by norm_num, by norm_num⟩
def interval612 : STLTableau.BoundedTimeInterval := ⟨6, 12, by norm_num, by norm_num⟩
def upper23 : Predicate Clock Variable :=
  .upper .c .closed .always (.bounded interval23) (ge .x 0)
def upper612 : Predicate Clock Variable :=
  .upper .c .closed .always (.bounded interval612) (ge .u 4)

def resetC : STLTableau.ClockResetSet Clock := .singleton .c 0
def resetD : STLTableau.ClockResetSet Clock := .singleton .d 0

/-- Local judgements are terminal judgements, interval type judgements,
interval predicates, and their conjunctions. -/
def LocalSyntax : Section3.Judgement Clock Variable → Prop
  | .terminal | .marker _ | .predicate _ => True
  | .conj F G => LocalSyntax F ∧ LocalSyntax G
  | _ => False

/-- In state form, clock constraints occur outside the scope of clock resets. -/
def StateSyntax : Section3.Judgement Clock Variable → Prop
  | .terminal | .marker _ | .predicate _ | .clock _ _ _ => True
  | .reset _ F => LocalSyntax F
  | .conj F G => StateSyntax F ∧ StateSyntax G
  | .next _ => False

/-- Under the reset of a transition-form judgement, the body contains local
judgements and an optional next state-form judgement. -/
def TransitionBodySyntax : Section3.Judgement Clock Variable → Prop
  | .terminal | .marker _ | .predicate _ => True
  | .next F => StateSyntax F
  | .conj F G => TransitionBodySyntax F ∧ TransitionBodySyntax G
  | _ => False

def TransitionSyntax : Section3.Judgement Clock Variable → Prop
  | .terminal | .marker _ | .predicate _ | .clock _ _ _ => True
  | .next F => StateSyntax F
  | .reset _ F => TransitionBodySyntax F
  | .conj F G => TransitionSyntax F ∧ TransitionSyntax G

/-- Example 4.2. A transition form with an empty reset part. -/
def firstJudgement : Section3.Judgement Clock Variable :=
  .conj (.clock .c .ge 5) (.conj (.predicate upper23) (.next (.clock .c .le 3)))
def firstForm : Section3.TransitionForm Clock Variable :=
  (Section3.TransitionForm.ofState (.ofGuard ⟨.c, .ge, 5⟩)).union
    ((Section3.TransitionForm.ofState (.ofLocal (.predicate upper23))).union
      (Section3.TransitionForm.ofNextState (.ofGuard ⟨.c, .le, 3⟩)))
theorem first_normalizes :
    Section3.TransitionForm.normalize? firstJudgement = some firstForm := rfl
theorem first_empty_reset : firstForm.current.resets = STLTableau.ClockResetSet.empty := by
  congr 1

def secondJudgement : Section3.Judgement Clock Variable := .reset resetC (.predicate upper23)
def secondForm : Section3.TransitionForm Clock Variable :=
  (Section3.TransitionForm.ofState (.ofLocal (.predicate upper23))).underReset resetC
theorem second_normalizes :
    Section3.TransitionForm.normalize? secondJudgement = some secondForm := rfl
theorem second_no_next : secondForm.nextPart = none := rfl
theorem first_transition_syntax : TransitionSyntax firstJudgement := ⟨trivial, trivial, trivial⟩
theorem second_transition_syntax : TransitionSyntax secondJudgement := trivial
theorem nested_next_not_transition_syntax :
    ¬ TransitionSyntax (.next (.next (.clock .c .ge 5))) := id
theorem reset_guard_not_transition_syntax :
    ¬ TransitionSyntax (.reset (.singleton .c 2) (.clock .c .ge 5)) := id
theorem nested_next_rejected :
    Section3.TransitionForm.normalize? (Section3.Judgement.next (.next (.clock Clock.c .ge 5)) :
      Section3.Judgement Clock Variable) = none := rfl

def positiveSource : Section3.TransitionForm Clock Variable := .ofState (.ofGuard ⟨.c, .gt, 2⟩)
def positiveTarget : Section3.TransitionForm Clock Variable :=
  ⟨{ (Section3.StateForm.ofGuard ⟨.c, .gt, 2⟩) with resets := resetC },
    some { (Section3.StateForm.ofLocal (.predicate (.plain (ge .x 4)))) with resets := resetD }⟩

/-- Example 4.4. The constraint `c > 2` is outside the scope of the reset of
`c`, and `d` is fresh. -/
theorem positive_subsumption : Section3.SyntacticallySubsumed positiveSource positiveTarget := by
  refine ⟨⟨fun _ h => h, ?_, fun _ h => h⟩, ?_, ?_⟩
  · intro clock a h; cases h
  · simp [positiveSource, Section3.TransitionForm.bodyFreeClocks, Section3.TransitionForm.ofState,
      Section3.StateForm.localClocks, Section3.StateForm.ofGuard]
  · intro N h; cases h

def captureSource : Section3.TransitionForm Clock Variable :=
  (Section3.TransitionForm.ofNextState (.ofGuard ⟨.d, .gt, 4⟩)).underReset resetC
def captureTarget : Section3.TransitionForm Clock Variable :=
  (Section3.TransitionForm.ofNextState (.ofGuard ⟨.d, .gt, 4⟩)).underReset (resetC.union resetD)

theorem reset_capture_not_subsumed :
    ¬ Section3.SyntacticallySubsumed captureSource captureTarget := by
  intro h
  have hf := Set.disjoint_left.mp h.outerFresh
  apply hf (a := Clock.d)
  · exact ⟨0, rfl⟩
  · constructor
    · exact Or.inr (Or.inl ⟨⟨.d, .gt, 4⟩, rfl, rfl⟩)
    · rintro ⟨a, ha⟩; cases ha

def atomicForm : Section3.TransitionForm Clock Variable :=
  (Section3.TransitionForm.ofState (.ofGuard ⟨.c, .le, 3⟩)).union
    (Section3.TransitionForm.ofState (.ofLocal (.predicate (.plain (ge .x 0)))))
/-- Example 4.7. The atomic predicate has no expansion rule. -/
theorem atom_rule_closed : ConcreteContextual.catalogue.RuleClosedFor atomicForm
    (.plain (ge .x 0)) := by
  apply ConcreteContextual.zero_complexity_ruleClosed
  rfl

def closureInput : Section3.TransitionForm Clock Variable :=
  (Section3.TransitionForm.ofState (.ofLocal (.predicate upper612))).underReset resetC
def printedClosure : Section3.TransitionForm Clock Variable :=
  ((Section3.TransitionForm.ofState (.ofLocal (.predicate upper612))).union
    ((Section3.TransitionForm.ofState (.ofLocal (.predicate (.plain (ge .u 4))))).union
      (Section3.TransitionForm.ofNextState ((Section3.StateForm.ofGuard ⟨.c, .gt, 6⟩).union
        (.ofLocal .terminal))))).underReset resetC

theorem printedClosure_same_resets :
    printedClosure.current.resets = closureInput.current.resets := by
  rfl

def terminalCheckRaw : STLTableau.Judgement Clock Variable :=
  .conj (.predicate (.plain (ge .u 4)))
    (.next (.conj (.clock .c .gt 6) .terminal))
def terminalCheck : Section3.TransitionForm Clock Variable :=
  (Section3.TransitionForm.ofState (.ofLocal (.predicate (.plain (ge .u 4))))).union
    (.ofNextState ((Section3.StateForm.ofGuard ⟨.c, .gt, 6⟩).union (.ofLocal .terminal)))

theorem terminalCheck_normalizes :
    Section3.TransitionForm.normalize?
      (Section3.Judgement.ofFinite terminalCheckRaw) = some terminalCheck := rfl

theorem terminalCheck_actual_branch :
    ConcreteContextual.catalogue.Branch upper612 resetC (terminalCheck.underReset resetC) := by
  refine ⟨terminalCheck, terminalCheck, Or.inl ?_, .refl _, rfl⟩
  refine ⟨.upper .c .closed .always interval612 (ge .u 4),
    STLTableau.ExpansionRule.upperAlways .c .d .closed interval612 (ge .u 4),
    terminalCheckRaw, terminalCheck, rfl, ?_, ?_, terminalCheck_normalizes, ?_⟩
  · exact .upperAlways Clock.c Clock.d .closed interval612 (ge .u 4) (by decide)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self)))
  · rfl

theorem terminalCheck_subsumed :
    Section3.SyntacticallySubsumed
      (terminalCheck.underReset resetC) printedClosure := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg; exact Or.inr hg
  · intro clock a h; exact h
  · intro l hl; exact Or.inr hl
  · apply Set.disjoint_left.mpr
    intro clock hc hd
    exact hd.2 hc
  · intro N hn
    cases hn
    refine ⟨_, rfl, ⟨fun _ h => h, fun _ _ h => h, fun _ h => h⟩, ?_⟩
    apply Set.disjoint_left.mpr
    intro clock hc hd
    exact hd.2 hc

theorem printedClosure_upper_rule_closed :
    ConcreteContextual.catalogue.RuleClosedFor printedClosure upper612 :=
  Or.inr ⟨terminalCheck.underReset resetC, terminalCheck_actual_branch,
    terminalCheck_subsumed⟩

theorem printedClosure_closed : ConcreteContextual.catalogue.IsClosed printedClosure := by
  intro p hp
  have h : p = upper612 ∨ p = .plain (ge .u 4) := by
    simpa [printedClosure, Section3.TransitionForm.underReset,
      Section3.TransitionForm.union, Section3.StateForm.union,
      Section3.TransitionForm.ofState, Section3.TransitionForm.ofNextState,
      Section3.StateForm.ofLocal, Section3.StateForm.empty,
      or_comm] using hp
  rcases h with rfl | rfl
  · exact printedClosure_upper_rule_closed
  · apply ConcreteContextual.zero_complexity_ruleClosed; rfl

theorem closureInput_subsumed :
    Section3.SyntacticallySubsumed closureInput printedClosure := by
  refine ⟨⟨?_, fun _ _ h => h, ?_⟩, ?_, ?_⟩
  · intro g hg; exact Or.inl hg
  · intro l hl; exact Or.inl hl
  · apply Set.disjoint_left.mpr
    intro clock hc hd
    exact hd.2 hc
  · intro N hn; cases hn

private theorem printedClosure_no_unbound :
    printedClosure.bodyFreeClocks \ printedClosure.current.resets.clocks = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro clock hc
  cases clock with
  | c => exact hc.2 ⟨0, rfl⟩
  | d =>
    simpa [printedClosure, upper612, Section3.TransitionForm.bodyFreeClocks,
      Section3.TransitionForm.underReset, Section3.TransitionForm.union,
      Section3.TransitionForm.unionNext, Section3.TransitionForm.ofState,
      Section3.TransitionForm.ofNextState, Section3.StateForm.empty,
      Section3.StateForm.union, Section3.StateForm.ofGuard, Section3.StateForm.ofLocal,
      Section3.StateForm.localClocks, Section3.StateForm.guardClocks,
      Section3.StateForm.freeClocks, Local.freeClocks, Local.toJudgement,
      Section3.Judgement.freeClocks, resetC, STLTableau.ClockResetSet.clocks,
      STLTableau.ClockResetSet.empty, STLTableau.ClockResetSet.union,
      STLTableau.ClockResetSet.singleton] using hc.1

theorem printedClosure_subsumed_of_forced
    {U : Section3.TransitionForm Clock Variable}
    (hext : Section3.SyntacticallySubsumed closureInput U)
    (hatom : Local.predicate (.plain (ge .u 4)) ∈ U.current.locals)
    (hguard : ∃ N, U.nextPart = some N ∧ (⟨Clock.c, .gt, 6⟩ : Guard Clock) ∈ N.guards)
    (hterminal : ∃ N, U.nextPart = some N ∧ Local.terminal ∈ N.locals) :
    Section3.SyntacticallySubsumed printedClosure U := by
  obtain ⟨N, hn, hg⟩ := hguard
  obtain ⟨M, hm, ht⟩ := hterminal
  have heq : M = N := Option.some.inj (hm.symm.trans hn)
  subst M
  refine ⟨⟨?_, hext.current.resets, ?_⟩, ?_, ?_⟩
  · intro g hg
    rcases hg with hg | hg
    · exact (Set.notMem_empty _ hg).elim
    · rcases hg with hg | hg <;> exact (Set.notMem_empty _ hg).elim
  · intro l hl
    rcases hl with hl | hl
    · exact hext.current.locals hl
    · rcases hl with hl | hl
      · have he : l = Local.predicate (.plain (ge .u 4)) := hl
        exact he ▸ hatom
      · exact (Set.notMem_empty _ hl).elim
  · rw [printedClosure_no_unbound]
    exact Set.disjoint_empty _
  · intro K hk
    cases hk
    refine ⟨N, hn, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro g hg'
      rcases hg' with hg' | hg'
      · exact hg' ▸ hg
      · exact (Set.notMem_empty _ hg').elim
    · intro clock a ha; cases ha
    · intro l hl
      rcases hl with hl | hl
      · exact (Set.notMem_empty _ hl).elim
      · exact hl ▸ ht
    · apply Set.disjoint_left.mpr
      intro clock hc hd
      rcases hd.1 with ⟨l, hl, hfree⟩
      rcases hl with hl | hl
      · exact (Set.notMem_empty _ hl).elim
      · cases hl
        exact hfree

/-- Example 4.9. The displayed closure is minimal among rule-closed extensions
of the input. -/
theorem printedClosure_isClosure :
    ConcreteContextual.catalogue.IsClosure closureInput printedClosure := by
  refine ⟨closureInput_subsumed, printedClosure_closed, ?_⟩
  intro U hext hclosed hbelow
  have hcurrent : Local.predicate upper612 ∈ U.current.locals :=
    hext.current.locals (Set.mem_singleton _)
  have hc := hclosed upper612 hcurrent
  have hforced := UpperAlwaysClosure.ruleClosed_forced
    Clock.c Clock.d (by decide) interval612
    (⟨1, fun _ => Variable.u, fun z => 4 - z 0, .le⟩ : AtomicProposition Variable)
    (C := printedClosure) rfl (Set.union_empty _) (Set.empty_union _)
    hbelow hc
  exact printedClosure_subsumed_of_forced hext hforced.1 hforced.2.1 hforced.2.2

set_option maxHeartbeats 1000000 in
-- Check the transition forms of all six branches of the rule for always in the `↑` form.
private theorem finite_upper_branch_next
    {p : STLTableau.IntervalPredicate Clock Variable}
    {R : STLTableau.ExpansionRule Clock Variable}
    {raw : STLTableau.Judgement Clock Variable} {F : Section3.TransitionForm Clock Variable}
    (hr : STLTableau.ConcreteRule p R) (he : Predicate.ofFinite p = upper23)
    (hm : raw ∈ R.branches)
    (hn : Section3.TransitionForm.normalize?
      (Section3.Judgement.ofFinite raw) = some F) : F.nextPart ≠ none := by
  cases hr <;> simp only [Predicate.ofFinite, upper23, Predicate.upper.injEq,
    reduceCtorEq, and_false, false_and, true_and,
    TimeInterval.bounded.injEq] at he
  rename_i clock other b I φ hcd
  obtain ⟨rfl, rfl, rfl, rfl⟩ := he
  simp only [STLTableau.ExpansionRule.upperAlways, List.mem_cons,
    List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [STLTableau.ExpansionRule.upperAlways_defer,
      STLTableau.ExpansionRule.upperAlways_check,
      STLTableau.Judgement.markedLT_eq_clock, STLTableau.Judgement.markedGT_eq_clock,
      Section3.Judgement.ofFinite,
      Section3.TransitionForm.normalize?,
      Section3.TransitionForm.union,
      Section3.TransitionForm.unionNext,
      Section3.TransitionForm.ofState,
      Section3.TransitionForm.ofNextState] at hn <;>
    cases hn <;> simp

private theorem upper23_branch_next {Λ : STLTableau.ClockResetSet Clock}
    {B : Section3.TransitionForm Clock Variable}
    (hb : ConcreteContextual.catalogue.Branch upper23 Λ B) : B.nextPart ≠ none := by
  obtain ⟨R, A, hR, ha, rfl⟩ := hb
  change A.nextPart ≠ none
  intro hnone
  have hnoneR := ha.next_none.mp hnone
  rcases hR with h | h | h
  · obtain ⟨p, E, raw, F, he, hr, hm, hn, rfl⟩ := h
    exact finite_upper_branch_next hr he.symm hm hn hnoneR
  · obtain ⟨p, E, raw, F, he, hr, hm, hn, rfl⟩ := h
    cases p <;> simp [Predicate.ofUnbounded, upper23] at he
  · obtain ⟨clock, m, kind, a, φ, F, he, hn, rfl⟩ := h
    simp [upper23] at he

def nonclosedUpperForm : Section3.TransitionForm Clock Variable :=
  (Section3.TransitionForm.ofState (.ofGuard ⟨.c, .le, 3⟩)).union
    (.ofState (.ofLocal (.predicate upper23)))

theorem upper_not_rule_closed :
    ¬ ConcreteContextual.catalogue.RuleClosedFor nonclosedUpperForm upper23 := by
  intro h
  rcases h with h | ⟨B, hb, hs⟩
  · apply h
    apply ConcreteContextual.catalogue.branch_exists
    · exact Or.inl (Or.inr ⟨.upper .c .closed .always interval23 (ge .x 0),
        STLTableau.ExpansionRule.upperAlways Clock.c Clock.d .closed interval23 (ge .x 0),
        rfl, .upperAlways Clock.c Clock.d .closed interval23 (ge .x 0) (by decide)⟩)
    · simp [upper23, Predicate.IsAtomic]
  · have hn := upper23_branch_next hb
    cases he : B.nextPart with
    | none => exact hn he
    | some N =>
      obtain ⟨M, hm, _⟩ := hs.next N he
      cases hm

end STLTableau.Examples.TransitionForms
