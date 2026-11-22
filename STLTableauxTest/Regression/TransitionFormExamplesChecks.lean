/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Examples.TransitionForms

open STLTableau.Examples.TransitionForms
open STLTableau.Section3

example : TransitionForm.normalize? firstJudgement = some firstForm := first_normalizes
example : TransitionSyntax firstJudgement := first_transition_syntax
example : TransitionSyntax secondJudgement := second_transition_syntax
example : ¬ TransitionSyntax (.next (.next (.clock .c .ge 5))) :=
  nested_next_not_transition_syntax
example : ¬ TransitionSyntax (.reset (.singleton .c 2) (.clock .c .ge 5)) :=
  reset_guard_not_transition_syntax
example : SyntacticallySubsumed positiveSource positiveTarget := positive_subsumption
example : ¬ SyntacticallySubsumed captureSource captureTarget := reset_capture_not_subsumed
example : ConcreteContextual.catalogue.RuleClosedFor atomicForm (.plain (ge .x 0)) :=
  atom_rule_closed
example : ¬ ConcreteContextual.catalogue.RuleClosedFor nonclosedUpperForm upper23 :=
  upper_not_rule_closed
example : ConcreteContextual.catalogue.IsClosed printedClosure := printedClosure_closed
example : SyntacticallySubsumed closureInput printedClosure := closureInput_subsumed
example : printedClosure.current.resets = closureInput.current.resets := printedClosure_same_resets
example : ConcreteContextual.catalogue.IsClosure closureInput printedClosure :=
  printedClosure_isClosure
example (U : TransitionForm Clock Variable)
    (hext : SyntacticallySubsumed closureInput U)
    (hc : ConcreteContextual.catalogue.IsClosed U)
    (hbelow : SyntacticallySubsumed U printedClosure) :
    SyntacticallySubsumed printedClosure U :=
  printedClosure_isClosure.minimal U hext hc hbelow

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``first_normalizes, ``first_empty_reset, ``second_normalizes,
      ``second_no_next, ``first_transition_syntax, ``second_transition_syntax,
      ``nested_next_rejected, ``nested_next_not_transition_syntax,
      ``reset_guard_not_transition_syntax, ``positive_subsumption,
      ``reset_capture_not_subsumed, ``atom_rule_closed, ``upper_not_rule_closed,
      ``terminalCheck_normalizes, ``terminalCheck_actual_branch,
      ``terminalCheck_subsumed, ``printedClosure_upper_rule_closed,
      ``printedClosure_closed, ``printedClosure_same_resets,
      ``closureInput_subsumed, ``printedClosure_subsumed_of_forced,
      ``printedClosure_isClosure] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
