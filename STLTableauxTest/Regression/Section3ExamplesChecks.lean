import STLTableaux.Examples.IntervalPredicates

open STLTableau STLTableau.Examples.Section3

example (σ : FiniteSignal Unit) (α : ClockValuation Clock) (hc : α .c = 1) :
    STLTableau.predicateSatisfies σ alwaysCell α alwaysExample ↔
      ∀ t : σ.Time, 8 < t.val ∧ t.val < 12 → 0 ≤ σ.value t () :=
  always_domain_clipped σ α hc

example (σ : FiniteSignal Unit) (α : ClockValuation Clock)
    (hc : α .c = 3) (hd : α .d = 1) :
    STLTableau.predicateSatisfies σ eventuallyCell α eventuallyExample ↔
      ∀ t : ℝ, 1 ≤ t ∧ t ≤ 3 →
        ∃ u : σ.Time, u.val ∈ (TimeInterval.bounded timing34).translate t ∧
          0 ≤ σ.value u () := eventually_witnesses σ α hc hd

example (α : ClockValuation Clock) :
    reset0.apply α .c = 0 ∧ reset73.apply α .c = 7 ∧ reset73.apply α .d = 3 :=
  reset_values α

example (v : {t : ℝ // 0 ≤ t ∧ t < 4} → Unit → ℝ) (α : ClockValuation Clock) :
    STLTableau.satisfies (signal4 v) STLTableau.Examples.Section3.partition α
      ⟨0, by norm_num [STLTableau.Examples.Section3.partition]⟩ psi1 ↔
    STLTableau.predicateSatisfies (signal4 v) (cells 0) (reset0.apply α) upper24 :=
  partition_first v α

example (v : {t : ℝ // 0 ≤ t ∧ t < 4} → Unit → ℝ) (α : ClockValuation Clock) :
    STLTableau.satisfies (signal4 v) STLTableau.Examples.Section3.partition α
      ⟨2, by norm_num [STLTableau.Examples.Section3.partition]⟩ psi2 ↔
    STLTableau.predicateSatisfies (signal4 v) (cells 2) (reset73.apply α) bounded24 ∧
    ∀ t : (signal4 v).Time, t.val ∈ cells 2 → 0 ≤ (signal4 v).value t () :=
  partition_last v α

example (σ : FiniteSignal Unit) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    STLTableau.satisfies σ P (reset5.apply (reset2.apply α)) k clockExample ↔
      STLTableau.satisfies σ P ((reset2.union reset5).apply α) k clockExample :=
  reset_clock_satisfaction σ P α k

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``always_scope, ``eventually_scope, ``always_domain_clipped,
      ``always_untruncated, ``eventually_witnesses, ``reset_values, ``partition,
      ``first_judgement, ``last_judgement, ``partition_first, ``partition_last,
      ``reset_disjoint, ``reset_consistent, ``free_clock, ``reset_assignment,
      ``reset_clock_satisfaction, ``reset_clock_true, ``other_clock_irrelevant] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
