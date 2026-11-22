import STLTableaux.Finiteness.Correctness.SelectedOriginPath
import STLTableaux.Finiteness.Derivation.ResolveSubformula
import STLTableaux.Finiteness.Bounds.SelectedRootBudget
import STLTableaux.Finiteness.ClockAllocation.SelectedNextClockSupport

/-! Uniform full-label and WHOLE-clock bounds carried through the actual path
recursion. Input support is linked to the preceding actual normalized next.
The local-count interface must be discharged in the final root application. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

/-- Numerical bounds concern every current local (including retained
nonatomic predicates) and all current/next clocks, including reset bindings. -/
def UniformStateBounds (H : ℕ) (F : Section3.TransitionForm Clock Var) : Prop :=
  F.current.locals_finite.toFinset.card ≤ H+3 ∧ F.allClocks_finite.toFinset.card ≤ 4*H

/-- Integration of local counts with a LINKED input clock invariant. This
lemma is generic; its final root-formula application supplies actual proved
counts, never a representative-path or state-bound existence premise. -/
theorem uniform_path_of_local_counts
    (X : Set Var) (Q : Set Clock) (root : Formula Var) (H : ℕ)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (localCounts : ∀ (β : ClockValuation Clock) (j : STLTableau.Judgement.Position P)
      (N : Section3.StateForm Clock Var) (O : InputOrigins σ P β j N),
      Finiteness.StateFormulasBelow root N →
      ∀ (J : MixedJ Clock Var) (W : Set Clock) (owned : OwnedPending J N.resets W)
        (Hraw Er : MixedJ Clock Var) (F : Section3.TransitionForm Clock Var)
        (T : SelectedTree O.eligible O.strictClocks owned Hraw Er),
      SafeNormalization J (.ofState N) → Derives N F →
      SelectedOutputFacts owned ∅ O.strictClocks σ P β j Hraw Er F →
      T.rawLedger.length ≤ H ∧ F.current.locals_finite.toFinset.card ≤ H+3)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hReady : root.MixedReady) (hPlain : Judgement.holds σ P α k (.predicate (.plain root)))
    (hStable : σ.StablePartition root P) :
    ∃ p : Path Clock (Section3.TransitionForm Clock Var),
      p.run (JudgementTableau.tableau X Q (plainInitialState (Clock := Clock) root) Derives) ∧
      p.accepting (JudgementTableau.tableau X Q (plainInitialState (Clock := Clock) root) Derives) ∧
      (JudgementTableau.fullTrace p).holds σ P α k ∧
      Subgraph.AllStates {F | UniformStateBounds H F ∧
        Finiteness.FormFormulasBelow root F ∧ OriginCertifiedState σ P F} p := by
  let Inv := fun (β : ClockValuation Clock) (j : STLTableau.Judgement.Position P)
    (N : Section3.StateForm Clock Var) => Nonempty (InputOrigins σ P β j N) ∧
      Finiteness.StateFormulasBelow root N ∧
      (Section3.TransitionForm.ofState N).allClocks_finite.toFinset.card ≤ 3*H
  let Good := fun (F : Section3.TransitionForm Clock Var) => UniformStateBounds H F ∧
    Finiteness.FormFormulasBelow root F ∧ OriginCertifiedState σ P F
  let O := plainInitialOrigins (Clock := Clock) root σ P α k hReady hPlain hStable
  have hZero : (Section3.TransitionForm.ofState (plainInitialState (Clock := Clock) root)).allClocks_finite.toFinset.card = 0 := by
    have hs : (Section3.TransitionForm.ofState (plainInitialState (Clock := Clock) root)).allClocks = ∅ :=
      (SafeNormalization.predicate (Predicate.plain root)).allClocks_eq_syntax
    have hf : (Section3.TransitionForm.ofState (plainInitialState (Clock := Clock) root)).allClocks_finite.toFinset = ∅ := by
      ext c
      simp [hs]
    rw [hf,Finset.card_empty]
  apply initial_accepting_path_of_nonempty_steps X Q (plainInitialState (Clock := Clock) root)
    σ P Inv Good _ _ α k ⟨⟨O⟩,Finiteness.plain_formulas_below root,by rw [hZero]; omega⟩ O.holds
    (Or.inl ⟨.predicate (.plain root),by simp [plainInitialState,Section3.StateForm.ofLocal]⟩)
  · intro β j N hInv _ hne
    obtain ⟨O⟩ := hInv.1
    obtain ⟨J,W,owned,Hraw,Er,F,T,hnil,hInput,hNext,hD,hFacts,hGuard,hSuccessor⟩ := O.nonempty_origin_step hne
    obtain ⟨hLedger,hLabels⟩ := localCounts β j N O hInv.2.1 J W owned Hraw Er F T hInput hD hFacts
    have hClock := T.normalized_clock_card_of_input hInput hFacts.1
    have hFClock : F.allClocks_finite.toFinset.card ≤ 4*H := by have hi := hInv.2.2; omega
    have hBelow := hD.formulas_below root hInv.2.1
    refine ⟨F,Hraw,hD,hFacts.1,hFacts.2.2.1,⟨⟨hLabels,hFClock⟩,hBelow,
      OriginCertifiedState.selected β j N O J W owned Hraw Er F T hnil hInput hNext hD hFacts⟩,?_⟩
    intro M hn hj
    have hNextClock := T.normalized_next_clock_card hnil hFacts.1 hn
    refine ⟨hSuccessor hj M hn,hBelow.2 M hn,?_⟩
    omega
  · intro β j N hInv he
    obtain ⟨O⟩ := hInv.1
    have hLabels : N.locals_finite.toFinset.card = 0 := by
      have hf : N.locals_finite.toFinset = ∅ := by ext l; simp [he]
      rw [hf,Finset.card_empty]
    refine ⟨⟨?_,?_⟩,?_,OriginCertifiedState.empty β j N O he⟩
    · change N.locals_finite.toFinset.card ≤ H+3
      omega
    · have hi := hInv.2.2
      change (Section3.TransitionForm.ofState N).allClocks_finite.toFinset.card ≤ 4*H
      omega
    · exact ⟨hInv.2.1,by intro M hm; cases hm⟩
end STLTableau.Section4.Finiteness
