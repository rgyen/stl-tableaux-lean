import STLTableaux.Automata.Execution.ForwardTraceExecution
import STLTableaux.Automata.Translation.EndPositionReverse

namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
variable (X : Set Var) (root : Formula.NormalizedInput Var)
local notation "U" => (localClosureGraph (Clock := Clock) X root)

private theorem subformula_of_inventory {φ root : Formula Var}
    (hm : φ ∈ Finiteness.rootPlainFormulas root) : Formula.IsSubformula φ root := by
  classical
  induction root with
  | truth | atom =>
    simp only [Finiteness.rootPlainFormulas,Finset.mem_singleton] at hm
    exact hm ▸ .refl _
  | neg φ ih =>
    simp only [Finiteness.rootPlainFormulas,Finset.mem_insert] at hm
    rcases hm with rfl | hm
    · exact .refl _
    · exact .neg (ih hm)
  | and φ ψ ih ik =>
    simp only [Finiteness.rootPlainFormulas,Finset.mem_insert,Finset.mem_union] at hm
    rcases hm with rfl | hm | hm
    · exact .refl _
    · exact .and_left (ih hm)
    · exact .and_right (ik hm)
  | «until» I φ ψ ih ik =>
    simp only [Finiteness.rootPlainFormulas,Finset.mem_insert,Finset.mem_union] at hm
    rcases hm with rfl | hm | hm
    · exact .refl _
    · exact .until_left (ih hm)
    · exact .until_right (ik hm)

theorem localClosure_atom_subformula (q : (U).states) (a : AtomicProposition Var)
    (hm : Local.predicate (.plain (.atom a)) ∈ (U).label q.val) :
    Formula.IsSubformula (.atom a) root.val := by
  rcases q.property.1 with he | old
  · change Local.predicate (.plain (.atom a)) ∈
      (withEmptyContinuation (Clock := Clock) X root).label q.val at hm
    rw [he,empty_label] at hm
    exact hm.elim
  · exact subformula_of_inventory (FiniteInventory.atom_mem_plain_inventory _ _ a (old.2.1.1 hm.1))

/-- Forward correctness for the automaton with a residence clock, an
endpoint marker, and a final jump at the horizon. The root atoms are non-strict and their values
are right-continuous on the signal domain. -/
theorem endPosition_forward (h : (U).TranslationReady) (σ : FiniteSignal Var)
    (hw : SignalAtomRightContinuous σ root.val)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) root.val → a.relation = .ge)
    (P : IntervalPartition σ.domain) (hrec : (U).recognizes JudgementTableau.labels_finite σ P) :
    ∃ aug, (U).TypedProjectsTo aug σ ∧
      ((U).endPositionAutomaton h σ.horizon).Reaches aug (U).goalModes := by
  obtain ⟨empty,_,hg,hl,he⟩ := local_empty_continuation_data (Clock := Clock) X root
  exact (U).corrected_forward h σ root.val hw P JudgementTableau.labels_finite hrec
    (fun q a ha => let hs := localClosure_atom_subformula X root q a ha; ⟨nonStrict a hs,hs⟩)
    empty hg hl he

/-- Both directions, with the translation well-formedness proof supplied
for any finite set containing the variables of the root. The reverse
quantifier ranges over witnesses and their induced partitions, not a
partition chosen independently of the signal. -/
theorem endPosition_correctness (hX : X.Finite)
    (vars : ∀ x ∈ rootVariables root.val, x ∈ X)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) root.val → a.relation = .ge)
    (ρ : FiniteSignal Var) :
    let h := localClosure_ready (Clock := Clock) X root
      (finiteRootTableau_translationReady X hX root.val vars)
    (SignalAtomRightContinuous ρ root.val → ∀ P : IntervalPartition ρ.domain,
      (U).recognizes JudgementTableau.labels_finite ρ P →
        ∃ aug, (U).TypedProjectsTo aug ρ ∧
          ((U).endPositionAutomaton h ρ.horizon).Reaches aug (U).goalModes) ∧
    (∀ (P : IntervalPartition ρ.domain) (aug : FiniteSignal (U).TypedVar)
      (e : ((U).endPositionAutomaton h ρ.horizon).Execution aug)
      (proj : (U).TypedProjectsTo aug ρ),
      (U).EndInducedPartition h ρ.horizon e proj.1 ρ P →
      (U).recognizes JudgementTableau.labels_finite ρ P) := by
  intro h
  constructor
  · intro hw P hr
    exact endPosition_forward X root h ρ hw nonStrict P hr
  · intro P aug e proj hp
    exact endPosition_reverse X root h e proj.1 ρ proj P hp

run_elab do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for n in #[``endPosition_forward,``endPosition_reverse,``endPosition_correctness] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do throwError "{n} uses unexpected axiom {ax}"

end STLTableau.Section4.Finiteness
