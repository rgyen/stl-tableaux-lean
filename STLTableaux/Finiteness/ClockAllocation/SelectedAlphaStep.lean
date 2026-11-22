import STLTableaux.Finiteness.ClockAllocation.SupportedClockPermutations
import STLTableaux.Finiteness.Derivation.Selection.SelectedClockSupport
import STLTableaux.Finiteness.Derivation.ResolveFreeSupport

/-! Extends the clock renaming across one selected expansion. The assignment
covers the entire input, including clocks that disappear from the output. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

noncomputable def SelectedTree.allocationSupport
    {E : Set (Predicate Clock Var)} {U : Set Clock} {J : MixedJ Clock Var}
    {N : Section3.StateForm Clock Var} {W : Set Clock}
    {owned : OwnedPending J N.resets W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) : Finset Clock :=
  (Section3.TransitionForm.ofState N).allClocks_finite.toFinset ∪ T.freshClocks.toFinset

theorem SelectedTree.allocationSupport_card
    {E : Set (Predicate Clock Var)} {U : Set Clock} {J : MixedJ Clock Var}
    {N : Section3.StateForm Clock Var} {W : Set Clock}
    {owned : OwnedPending J N.resets W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) (B : ℕ)
    (hi : (Section3.TransitionForm.ofState N).allClocks_finite.toFinset.card ≤ 3*B)
    (hl : T.rawLedger.length ≤ B) : T.allocationSupport.card ≤ 4*B := by
  have h := Finset.card_union_le (Section3.TransitionForm.ofState N).allClocks_finite.toFinset T.freshClocks.toFinset
  have hf := List.toFinset_card_le T.freshClocks
  rw [T.freshClocks_length] at hf
  unfold allocationSupport
  omega

theorem SelectedTree.output_support_allocation
    {E : Set (Predicate Clock Var)} {U : Set Clock} {J : MixedJ Clock Var}
    {N : Section3.StateForm Clock Var} {W : Set Clock}
    {owned : OwnedPending J N.resets W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) (hI : SafeNormalization J (.ofState N))
    {F : Section3.TransitionForm Clock Var} (hF : SafeNormalization H F) :
    F.allClocks ⊆ (T.allocationSupport : Set Clock) := by
  intro c hc
  have hm := T.normalized_clock_support hF hc
  rw [input_clock_support_of_safe hI] at hm
  rcases hm with hi | hf
  · exact Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).2 hi)
  · exact Finset.mem_union_right _ (List.mem_toFinset.2 hf)

omit [DecidableEq Clock] in
/-- A literal permutation acts contravariantly on valuations. -/
theorem transition_holds_rename (e : Equiv.Perm Clock) (F : Section3.TransitionForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (renameTransition e F).holds σ P α k ↔ F.holds σ P (α ∘ e) k := by
  have helapse : ∀ d, ClockResetSet.elapse ((F.current.rename e).resets.apply α) d ∘ e =
      ClockResetSet.elapse (F.current.resets.apply (α ∘ e)) d := by
    intro d
    funext c
    exact congrArg (fun x => x+d) (congrFun (F.current.resets.apply_rename e α) c)
  cases hn : F.nextPart <;>
    simp only [renameTransition,Section3.TransitionForm.holds,hn,Option.map_none,
      Option.map_some,Section3.StateForm.holds_rename,helapse]

/-- Actual selected resolution needs agreement only on INPUT free clocks. -/
theorem resolved_rename_holds
    {J H A : MixedJ Clock Var} {N : Section3.StateForm Clock Var}
    {F : Section3.TransitionForm Clock Var} (D : Resolve J H A)
    (hI : SafeNormalization J (.ofState N)) (hF : SafeNormalization H F)
    (e : Equiv.Perm Clock) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α β : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (ha : ∀ c ∈ N.freeClocks, β (e c)=α c) (hs : F.holds σ P α k) :
    (renameTransition e F).holds σ P β k := by
  apply (transition_holds_rename e F σ P β k).2
  apply (F.holds_congr_of_agree σ P α (β ∘ e) k _).1 hs
  intro c hc
  exact (ha c (selected_resolution_free_subset D hI hF hc)).symm

omit [DecidableEq Clock] in
/-- Compatibility on the actual next interface propagates valuation agreement.
The reset case is exact; unreset names are free in the full source form. -/
theorem renamed_successor_agreement
    {N M : Section3.StateForm Clock Var} {F : Section3.TransitionForm Clock Var}
    (hn : F.nextPart=some M) (hf : F.freeClocks ⊆ N.freeClocks)
    (e f : Equiv.Perm Clock) (α β : ClockValuation Clock) (d : NNReal)
    (ha : ∀ c ∈ N.freeClocks, β (e c)=α c)
    (he : ∀ c ∈ stateClockSupport M, e c=f c) :
    ∀ c ∈ M.freeClocks,
      ClockResetSet.elapse ((renameTransition e F).current.resets.apply β) d (f c) =
      ClockResetSet.elapse (F.current.resets.apply α) d c := by
  intro c hc
  have hs : c∈stateClockSupport M := by
    rcases hc with hg | ⟨hl,_⟩
    · exact Or.inl (Or.inl hg)
    · exact Or.inl (Or.inr hl)
  rw [← he c hs]
  change ((F.current.resets.rename e).apply β) (e c)+d = F.current.resets.apply α c+d
  have hx := congrFun (F.current.resets.apply_rename e β) c
  change (F.current.resets.rename e).apply β (e c) = F.current.resets.apply (β ∘ e) c at hx
  rw [hx]
  apply congrArg (fun x=>x+d)
  cases hv : F.current.resets.value c with
  | some a => simp only [ClockResetSet.apply,hv]
  | none =>
      have hnot : c∉F.current.resets.clocks := by
        rintro ⟨a,ha⟩
        rw [hv] at ha
        cases ha
      have hfree : c∈F.freeClocks := Or.inr ⟨Or.inr (by simpa only [hn] using hc),hnot⟩
      simpa only [ClockResetSet.apply,hv,Function.comp_apply] using ha c (hf hfree)
end STLTableau.Section4.Finiteness
