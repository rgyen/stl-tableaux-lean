import STLTableaux.Finiteness.Derivation.Selection.SelectedClockSupport
import STLTableaux.Finiteness.Derivation.NextResetProvenance

/-! Traces the clock support of the next judgement to branches of the selected
derivation. Resets inherited in the current state do not enter next judgements. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

def normalizedNextClocks (F : Section3.TransitionForm Clock Var) : Set Clock :=
  match F.nextPart with
  | none => ∅
  | some N => (Section3.TransitionForm.ofState N).allClocks

private theorem state_union_clocks (N M : Section3.StateForm Clock Var) :
    (Section3.TransitionForm.ofState (N.union M)).allClocks =
      (Section3.TransitionForm.ofState N).allClocks ∪
      (Section3.TransitionForm.ofState M).allClocks :=
  NormalizationSupport.allClocks_union (.ofState N) (.ofState M)

private theorem next_union (F G : Section3.TransitionForm Clock Var) :
    normalizedNextClocks (F.union G) = normalizedNextClocks F ∪ normalizedNextClocks G := by
  cases hf : F.nextPart <;> cases hg : G.nextPart <;>
    simp [normalizedNextClocks,Section3.TransitionForm.union,
      Section3.TransitionForm.unionNext,hf,hg,state_union_clocks]

theorem SafeNormalization.nextClocks_eq_syntax
    {J : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : SafeNormalization J F) : normalizedNextClocks F = nextSyntaxClocks J := by
  induction h with
  | terminal | clock | marker | predicate => rfl
  | conj h g hc ih ig => exact (next_union _ _).trans (congrArg₂ Set.union ih ig)
  | reset R h hd ih => exact ih
  | @next J F h hn ih =>
      change (Section3.TransitionForm.ofState _).allClocks = syntaxClocks _
      have he : Section3.TransitionForm.ofState F.current = F := by
        cases F with
        | mk current nextPart => cases nextPart <;> simp_all [Section3.TransitionForm.ofState]
      rw [he]
      exact h.allClocks_eq_syntax

theorem nextSyntaxClocks_payloads (J : MixedJ Clock Var) (c : Clock) :
    c∈nextSyntaxClocks J ↔ ∃K∈nextPayloads J,c∈syntaxClocks K := by
  induction J with
  | terminal | clock | marker | predicate => simp [nextSyntaxClocks,nextPayloads]
  | next K => simp [nextSyntaxClocks,nextPayloads]
  | reset R J ih => exact ih
  | conj J K ih ik =>
      simp only [nextSyntaxClocks,nextPayloads,Set.mem_union,ih,ik]
      aesop

private theorem payload_support {J K : MixedJ Clock Var} (h : K∈nextPayloads J) :
    syntaxClocks K ⊆ syntaxClocks J := by
  induction J with
  | terminal | clock | marker | predicate => cases h
  | next L => have he : K=L := h; subst K; exact Set.Subset.rfl
  | reset R J ih => exact (ih h).trans Set.subset_union_right
  | conj J L ih il =>
      rcases h with h | h
      · exact (ih h).trans Set.subset_union_left
      · exact (il h).trans Set.subset_union_right

variable [DecidableEq Clock]

theorem SelectedTree.ledger_body_fresh_support
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) :
    ∀entry∈T.rawLedger, ∃x∈T.freshClocks,
      syntaxClocks entry.body ⊆ syntaxClocks (.predicate entry.source) ∪ {x} := by
  induction T with
  | zero => simp [SelectedTree.rawLedger]
  | ordinary owned choice tail ih =>
      intro entry he
      rcases List.mem_cons.1 he with he | he
      · subst entry
        exact ⟨choice.x,by simp [SelectedTree.freshClocks],
          choice.branch.syntaxClocks_subset_source_union_singleton choice.x choice.reset_support⟩
      · obtain ⟨x,hx,hs⟩ := ih entry he
        exact ⟨x,List.mem_cons_of_mem _ hx,hs⟩
  | required owned choice tail ih => exact ih
  | optional owned choice upper forced tail ih =>
      intro entry he
      rcases List.mem_cons.1 he with he | he
      · subst entry
        exact ⟨upper.x,by simp [SelectedTree.freshClocks],
          upper.branch.syntaxClocks_subset_source_union_singleton upper.x upper.reset_support⟩
      · obtain ⟨x,hx,hs⟩ := ih entry he
        exact ⟨x,List.mem_cons_of_mem _ hx,hs⟩

/-- Every outgoing name, including guard-only payload/reset names, comes from
 an actual branch of this tree when the incoming syntax has no next payload. -/
theorem SelectedTree.next_clock_ledger_support
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) (hEmpty : owned.nextInputs=[])
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization H F)
    {N : Section3.StateForm Clock Var} (hn : F.nextPart=some N) :
    ∀c∈(Section3.TransitionForm.ofState N).allClocks,
      ∃entry∈T.rawLedger,c∈syntaxClocks entry.body := by
  intro c hc
  have hnext : c∈nextSyntaxClocks H := by
    rw [← hSafe.nextClocks_eq_syntax]
    simpa [normalizedNextClocks,hn] using hc
  obtain ⟨K,hK,hc⟩ := (nextSyntaxClocks_payloads H c).1 hnext
  rcases (T.nextPayloads_iff K).1 hK with hK | ⟨entry,he,hK⟩
  · rw [owned.nextPayloads_eq] at hK
    simp [hEmpty] at hK
  · exact ⟨entry,he,payload_support hK hc⟩

private theorem predicate_card (p : Predicate Clock Var) :
    (syntaxClocks_finite (.predicate p)).toFinset.card ≤ 2 := by
  cases p <;> simp [syntaxClocks]
  · exact Nat.le_trans (Finset.card_insert_le _ _) (by simp)

private theorem body_card {p : Predicate Clock Var} {B : MixedJ Clock Var} {x : Clock}
    (h : syntaxClocks B ⊆ syntaxClocks (.predicate p) ∪ {x}) :
    (syntaxClocks_finite B).toFinset.card ≤ 3 := by
  have hs : (syntaxClocks_finite B).toFinset ⊆
      (syntaxClocks_finite (.predicate p)).toFinset ∪ {x} := by
    intro c hc
    simpa only [Set.Finite.mem_toFinset,Finset.mem_union,Finset.mem_singleton,Set.mem_union,Set.mem_singleton_iff] using
      h ((Set.Finite.mem_toFinset _).1 hc)
  calc
    _ ≤ ((syntaxClocks_finite (.predicate p)).toFinset ∪ {x}).card := Finset.card_le_card hs
    _ ≤ (syntaxClocks_finite (.predicate p)).toFinset.card+({x} : Finset Clock).card := Finset.card_union_le _ _
    _ ≤ 2+1 := Nat.add_le_add (predicate_card p) (by simp)

private noncomputable def ledgerClocks : List (RawLedgerEntry (Clock := Clock) (Var := Var)) → Finset Clock
  | [] => ∅
  | e::es => (syntaxClocks_finite e.body).toFinset ∪ ledgerClocks es

private theorem ledgerClocks_mem (es : List (RawLedgerEntry (Clock := Clock) (Var := Var))) (c : Clock) :
    c∈ledgerClocks es ↔ ∃e∈es,c∈syntaxClocks e.body := by
  induction es with
  | nil => simp [ledgerClocks]
  | cons e es ih =>
      simp only [ledgerClocks,Finset.mem_union,Set.Finite.mem_toFinset,ih,List.mem_cons]
      aesop

private theorem ledgerClocks_card (es : List (RawLedgerEntry (Clock := Clock) (Var := Var)))
    (h : ∀e∈es,(syntaxClocks_finite e.body).toFinset.card≤3) :
    (ledgerClocks es).card≤3*es.length := by
  induction es with
  | nil => simp [ledgerClocks]
  | cons e es ih =>
      calc
        _ ≤ (syntaxClocks_finite e.body).toFinset.card+(ledgerClocks es).card := Finset.card_union_le _ _
        _ ≤ 3+3*es.length := Nat.add_le_add (h e (by simp)) (ih (fun e he => h e (List.mem_cons_of_mem _ he)))
        _ = 3*(e::es).length := by simp; omega

/-- An actual outgoing state's WHOLE clock support is at most three times
 this position's actual expansion count, independent of input/history size. -/
theorem SelectedTree.normalized_next_clock_card
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) (hEmpty : owned.nextInputs=[])
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization H F)
    {N : Section3.StateForm Clock Var} (hn : F.nextPart=some N) :
    (Section3.TransitionForm.ofState N).allClocks_finite.toFinset.card≤3*T.rawLedger.length := by
  have hs : (Section3.TransitionForm.ofState N).allClocks_finite.toFinset ⊆ ledgerClocks T.rawLedger := by
    intro c hc
    exact (ledgerClocks_mem _ _).2 (T.next_clock_ledger_support hEmpty hSafe hn c
      ((Set.Finite.mem_toFinset _).1 hc))
  apply (Finset.card_le_card hs).trans
  apply ledgerClocks_card
  intro e he
  obtain ⟨x,_,hx⟩ := T.ledger_body_fresh_support e he
  exact body_card hx

end STLTableau.Section4.Finiteness
