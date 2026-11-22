import STLTableaux.Rules.Finite.Correctness

/-! A missing stability premise in the arbitrary-generator path lemma.
This file proves failure of its first local completeness obligation; it does
not introduce a tableau/path definition or claim to formalize its negation. -/
namespace STLTableau.Section4Counterexamples
open scoped STL

def signal : FiniteSignal Unit where
  horizon := 2
  horizon_pos := by norm_num
  value := fun t _ => t.val

def piece : MarkedInterval := ⟨0, 2, ●, ○⟩

def partition : IntervalPartition signal.domain where
  size := 1
  interval := fun _ => piece
  nonempty := by intro i; norm_num [piece, MarkedInterval.carrier_eq]
  pairwiseDisjoint := by intro i j hij; exact (hij (Subsingleton.elim i j)).elim
  covers := by ext t; simp [piece, MarkedInterval.carrier_eq, FiniteSignal.domain, signal]
  ordered := by intro i j hij; exact (not_lt_of_ge (Subsingleton.elim i j).ge hij).elim

/-- Uses the primitive comparison `f(x) ≥ 0`. -/
def atom : Formula Unit := .atom ⟨1, fun _ => (), fun x => x 0 - 1, .ge⟩
def generatorFormula : Formula Unit := Formula.or atom (.neg atom)
def position : Judgement.Position partition := ⟨0, by norm_num [partition]⟩
def clocks : ClockValuation Nat := fun _ => 0

theorem root_truth_fully_stable : signal.StablePartition (.truth : Formula Unit) partition := by
  intro i ψ hψ
  cases hψ
  intro u v hu hv
  rfl

/-- A tautological primitive root explicitly using the very same variable
as both generator atoms. This avoids an unrelated variable-universe issue. -/
def rootSameVariable : Formula Unit :=
  .atom ⟨1, fun _ => (), fun x => x 0 - x 0, .ge⟩

theorem rootSameVariable_fully_stable : signal.StablePartition rootSameVariable partition := by
  intro i ψ hψ
  cases hψ
  intro u v hu hv
  change (u.1 - u.1 ≥ 0) ↔ (v.1 - v.1 ≥ 0)
  simp

theorem generator_satisfied : satisfies signal partition clocks position
    (.predicate (.plain generatorFormula)) := by
  change ∀ t : signal.Time, t.1 ∈ piece → (signal,t)⊨generatorFormula
  intro t ht
  rw [generatorFormula, FiniteSignal.satisfies_or]
  change _ ∨ ¬ _
  exact Classical.em _

theorem generator_invariant :
    ∀ hk : position.1 < partition.size,
      Invariant signal partition clocks position hk (.plain generatorFormula) := by
  intro hk
  trivial

theorem positive_branch_not_satisfied :
    ¬ satisfies signal partition clocks position (.predicate (.plain atom)) := by
  intro h
  let t : signal.Time := ⟨0, by norm_num [signal]⟩
  have ht : t.1 ∈ piece := by norm_num [t, piece, MarkedInterval.mem_iff, Marker.Includes]
  have hf := h t ht
  change (0 : ℝ) - 1 ≥ 0 at hf
  linarith

theorem negative_branch_not_satisfied :
    ¬ satisfies signal partition clocks position (.predicate (.plain (.neg atom))) := by
  intro h
  let t : signal.Time := ⟨1, by norm_num [signal]⟩
  have ht : t.1 ∈ piece := by norm_num [t, piece, MarkedInterval.mem_iff, Marker.Includes]
  have hf := h t ht
  change ¬ (1 : ℝ) - 1 ≥ 0 at hf
  exact hf (by norm_num)

theorem generator_no_satisfied_branch :
    ¬ branchSatisfied (ExpansionRule.plainOr atom (.neg atom)) signal partition clocks position := by
  rintro ⟨B, hB, h⟩
  simp only [ExpansionRule.plainOr, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl
  · exact positive_branch_not_satisfied h
  · exact negative_branch_not_satisfied h

/-- Stability of an unrelated root formula plus the generator's full invariant
and satisfaction cannot justify completeness of its actual expansion rule. -/
theorem arbitrary_generator_stability_gap :
    signal.StablePartition (.truth : Formula Unit) partition ∧
    satisfies signal partition clocks position (.predicate (.plain generatorFormula)) ∧
    (∀ hk : position.1 < partition.size,
      Invariant signal partition clocks position hk (.plain generatorFormula)) ∧
    ¬ branchSatisfied (ExpansionRule.plainOr atom (.neg atom)) signal partition clocks position :=
  ⟨root_truth_fully_stable, generator_satisfied, generator_invariant, generator_no_satisfied_branch⟩

/-- The issue persists inside the admitted normalized grammar, using only
primitive non-strict comparisons: `(x ≥ 1) ∨ (x ≤ 1)`. -/
def otherAtom : Formula Unit := .atom ⟨1, fun _ => (), fun x => 1 - x 0, .ge⟩

theorem normalized_generator_ready : (Formula.or atom otherAtom).TableauReady :=
  .or (.atom _) (.atom _)

theorem normalized_generator_satisfied : satisfies signal partition clocks position
    (.predicate (.plain (Formula.or atom otherAtom))) := by
  change ∀ t : signal.Time, t.1 ∈ piece → (signal,t)⊨Formula.or atom otherAtom
  intro t ht
  rw [FiniteSignal.satisfies_or]
  change t.1 - 1 ≥ 0 ∨ 1 - t.1 ≥ 0
  rcases le_total 1 t.1 with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

theorem other_branch_not_satisfied :
    ¬ satisfies signal partition clocks position (.predicate (.plain otherAtom)) := by
  intro h
  let t : signal.Time := ⟨3 / 2, by norm_num [signal]⟩
  have ht : t.1 ∈ piece := by norm_num [t, piece, MarkedInterval.mem_iff, Marker.Includes]
  have hf := h t ht
  change (1 : ℝ) - 3 / 2 ≥ 0 at hf
  linarith

theorem normalized_generator_no_satisfied_branch :
    ¬ branchSatisfied (ExpansionRule.plainOr atom otherAtom) signal partition clocks position := by
  rintro ⟨B, hB, h⟩
  simp only [ExpansionRule.plainOr, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl
  · exact positive_branch_not_satisfied h
  · exact other_branch_not_satisfied h

theorem normalized_arbitrary_generator_stability_gap :
    signal.StablePartition (.truth : Formula Unit) partition ∧
    (Formula.or atom otherAtom).TableauReady ∧
    satisfies signal partition clocks position (.predicate (.plain (Formula.or atom otherAtom))) ∧
    (∀ hk : position.1 < partition.size,
      Invariant signal partition clocks position hk (.plain (Formula.or atom otherAtom))) ∧
    ¬ branchSatisfied (ExpansionRule.plainOr atom otherAtom) signal partition clocks position :=
  ⟨root_truth_fully_stable, normalized_generator_ready, normalized_generator_satisfied,
    fun _ => trivial, normalized_generator_no_satisfied_branch⟩

end STLTableau.Section4Counterexamples
