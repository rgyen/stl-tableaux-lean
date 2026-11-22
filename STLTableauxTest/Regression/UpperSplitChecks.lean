import STLTableaux.Compatibility

/-! Zero-clock boundary regressions and audits for current-containing splits. -/
open STLTableau
open scoped STL

-- Matching markers include closed, open, and singleton current intervals.
example (J : MarkedInterval) (hne : J.carrier.Nonempty) :
    J.carrier ⊆
      (⟨J.leftBoundary, J.left - ((0 : NNReal) : ℝ), J.right,
        J.rightBoundary⟩ : Scope).carrier := by
  exact (IntervalPredicate.current_subset_upperScope_iff J
    (fun _ : Unit => 0) () J.leftBoundary hne).2 (fun _ h => h)

-- A closed stored marker also covers an open current left endpoint at age zero.
example (J : MarkedInterval) (hne : J.carrier.Nonempty) :
    J.carrier ⊆ (⟨●, J.left, J.right, J.rightBoundary⟩ : Scope).carrier := by
  simpa using (IntervalPredicate.current_subset_upperScope_iff J
    (fun _ : Unit => 0) () ● hne).2 (by simp)

-- The excluded case really fails, rather than being silently normalized.
example (J : MarkedInterval) (hne : J.carrier.Nonempty)
    (hm : J.leftBoundary.Includes) :
    ¬ J.carrier ⊆ (⟨○, J.left, J.right, J.rightBoundary⟩ : Scope).carrier := by
  intro h
  have hc := (IntervalPredicate.current_subset_upperScope_iff J
    (fun _ : Unit => 0) () ○ hne).1 (by simpa using h)
  exact hc rfl hm

-- Both temporal kinds and terminal positions are covered by these interfaces.
#check STLTableau.satisfies_upper_iff_reset_split_of_contains
#check STLTableau.UnboundedClocked.reset_split_correct_of_contains

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``IntervalPredicate.current_subset_upperScope_iff,
    ``STLTableau.satisfies_upper_iff_reset_split_of_contains,
    ``STLTableau.UnboundedClocked.reset_split_correct_of_contains] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
