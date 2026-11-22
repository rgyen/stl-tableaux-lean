import STLTableaux.Finiteness.ClockAllocation.SelectedNextClockSupport
import STLTableaux.Finiteness.Derivation.Branches.BranchPlainOpening

/-! With no inherited next judgements, each clock of the normalized next state
comes from a clocked branch of the same derivation. This includes clocks
occurring only in guards or resets. Opening an unclocked predicate introduces a
clock in the current part. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

private theorem next_syntax_subset (J : MixedJ Clock Var) : nextSyntaxClocks J⊆syntaxClocks J := by
  induction J with
  | terminal | clock | marker | predicate | next => simp [nextSyntaxClocks,syntaxClocks]
  | conj J K ih ik => exact Set.union_subset_union ih ik
  | reset R J ih => exact ih.trans Set.subset_union_right

variable [DecidableEq Clock]

/-- Expanding an unclocked predicate leaves the next part free of clocks. An
opening branch can introduce the `↑` form in the current part. -/
theorem RawBranch.plain_next_clocks_empty
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (branch : RawBranch p B)
    (hp : ∃φ,p=.plain φ) : nextSyntaxClocks B=∅ := by
  rcases branch.plain_opening_or_empty hp with hEmpty | ⟨c,m,kind,I,φ,hs,hB⟩
  · apply Set.eq_empty_of_subset_empty
    rw [←hEmpty]
    exact next_syntax_subset B
  · rw [hB]
    simp [nextSyntaxClocks]

/-- With no inherited next judgements, every clock of the normalized next
state occurs in the next part of a raw branch in the selected derivation. -/
theorem SelectedTree.next_clock_ledger_origin
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) (hEmpty : owned.nextInputs=[])
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization H F)
    {N : Section3.StateForm Clock Var} (hn : F.nextPart=some N)
    (c : Clock) (hc : c∈(Section3.TransitionForm.ofState N).allClocks) :
    ∃entry∈T.rawLedger,c∈nextSyntaxClocks entry.body := by
  have hnext : c∈nextSyntaxClocks H := by
    rw [←hSafe.nextClocks_eq_syntax]
    simpa [normalizedNextClocks,hn] using hc
  obtain ⟨K,hK,hc⟩ := (nextSyntaxClocks_payloads H c).1 hnext
  rcases (T.nextPayloads_iff K).1 hK with hK | ⟨entry,he,hK⟩
  · rw [owned.nextPayloads_eq] at hK
    simp [hEmpty] at hK
  · exact ⟨entry,he,(nextSyntaxClocks_payloads entry.body c).2 ⟨K,hK,hc⟩⟩

/-- Every actual outgoing supported name belongs to an upper or bounded event.
This includes guard/reset-only next pieces and makes no bounded-local claim. -/
theorem SelectedTree.next_clock_clocked_ledger_origin
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) (hEmpty : owned.nextInputs=[])
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization H F)
    {N : Section3.StateForm Clock Var} (hn : F.nextPart=some N)
    (c : Clock) (hc : c∈(Section3.TransitionForm.ofState N).allClocks) :
    ∃entry∈T.rawLedger,c∈nextSyntaxClocks entry.body ∧
      ((∃a m kind I φ,entry.source=.upper a m kind I φ) ∨
        (∃a d m q kind I φ,entry.source=.bounded a d m q kind I φ)) := by
  obtain ⟨entry,he,hc⟩ := T.next_clock_ledger_origin hEmpty hSafe hn c hc
  refine ⟨entry,he,hc,?_⟩
  cases hs : entry.source with
  | plain φ =>
      have hz := entry.actual.plain_next_clocks_empty ⟨φ,hs⟩
      rw [hz] at hc
      exact hc.elim
  | upper a m kind I φ => exact Or.inl ⟨a,m,kind,I,φ,rfl⟩
  | bounded a d m q kind I φ => exact Or.inr ⟨a,d,m,q,kind,I,φ,rfl⟩
end STLTableau.Section4.Finiteness
