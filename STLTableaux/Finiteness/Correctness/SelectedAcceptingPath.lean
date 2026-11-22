import STLTableaux.Finiteness.Derivation.DerivationRelation
import STLTableaux.Finiteness.Derivation.EmptyStateCompletion
import STLTableaux.Finiteness.Inventory.Subgraph

/-! Actual finite-partition path assembly in the judgement-state tableau.
The invariant/local-step and per-state Good premises are explicit interfaces to
be discharged by the selected origin construction; this is not a bounded-path
completion theorem. Empty successors use their actual safe input certificate. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

omit [DecidableEq Clock] in
/-- A concrete local relation transition preserving an invariant builds an
actual initial accepting path and retains Good at EVERY judgement state. -/
theorem initial_accepting_path_of_relation_steps
    (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (R : Section3.StateForm Clock Var → Section3.TransitionForm Clock Var → Prop)
    (Inv : ClockValuation Clock → STLTableau.Judgement.Position P → Section3.StateForm Clock Var → Prop)
    (Good : Section3.TransitionForm Clock Var → Prop)
    (select : ∀ (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
      (N : Section3.StateForm Clock Var), Inv α k N → N.holds σ P α k →
      ∃ F : Section3.TransitionForm Clock Var, R N F ∧ F.holds σ P α k ∧ Good F ∧
        ∀ M, F.nextPart=some M → ∀hk : k.1<P.size,
          Inv (ClockResetSet.elapse (F.current.resets.apply α)
            (STLTableau.Judgement.duration P ⟨k.1,hk⟩)) ⟨k.1+1,by omega⟩ M)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hInv : Inv α k root) (hHolds : root.holds σ P α k) :
    ∃ p : Path Clock (Section3.TransitionForm Clock Var),
      p.run (JudgementTableau.tableau X Q root R) ∧
      p.accepting (JudgementTableau.tableau X Q root R) ∧
      (JudgementTableau.fullTrace p).holds σ P α k ∧
      Subgraph.AllStates {F | Good F} p := by
  have main : ∀n : ℕ, ∀ (j : STLTableau.Judgement.Position P)
      (β : ClockValuation Clock) (N : Section3.StateForm Clock Var),
      P.size-j.1=n → Inv β j N → N.holds σ P β j →
      ∃ p : Path Clock (Section3.TransitionForm Clock Var),
        R N p.firstState ∧ p.firstIncoming=JudgementTableau.incoming p.firstState ∧
        p.accepting (JudgementTableau.tableau X Q root R) ∧
        (JudgementTableau.fullTrace p).holds σ P β j ∧ Subgraph.AllStates {F | Good F} p := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j β N hn hI hN
      obtain ⟨F,hD,hF,hGood,hNextInv⟩ := select β j N hI hN
      cases hnext : F.nextPart with
      | none =>
          refine ⟨.last (JudgementTableau.incoming F) F,hD,rfl,?_,?_,hGood⟩
          · exact ⟨⟨N,hD⟩,hnext⟩
          · exact hF.1
      | some M =>
          have hj : j.1<P.size := by
            by_contra hnot
            have hh := hF.2
            simp only [hnext,dif_neg hnot] at hh
          let j' : STLTableau.Judgement.Position P := ⟨j.1+1,by omega⟩
          let γ := ClockResetSet.elapse (F.current.resets.apply β)
            (STLTableau.Judgement.duration P ⟨j.1,hj⟩)
          have hM : M.holds σ P γ j' := by simpa only [hnext,dif_pos hj] using hF.2
          have hlt : P.size-j'.1<n := by dsimp [j']; omega
          obtain ⟨tail,hTailD,hTailIncoming,hTailA,hTailTrace,hTailGood⟩ :=
            ih (P.size-j'.1) hlt j' γ M rfl (hNextInv M hnext hj) hM
          refine ⟨.step (JudgementTableau.incoming F) F tail,hD,rfl,?_,?_,hGood,hTailGood⟩
          · refine ⟨⟨⟨N,hD⟩,hTailA.1,?_⟩,hTailA.2⟩
            exact ⟨⟨N,hD⟩,⟨M,hTailD⟩,M,hnext,hTailD,hTailIncoming⟩
          · change F.current.holds σ P β j ∧ (if hk : j.1<P.size then _ else False)
            exact ⟨hF.1,by simpa only [dif_pos hj,JudgementTableau.fullTrace,Path.trace,Trace.holds,JudgementTableau.incoming,γ,j'] using hTailTrace⟩
  obtain ⟨p,hFirstD,hIncoming,hAccept,hTrace,hGood⟩ := main (P.size-k.1) k α root rfl hInv hHolds
  refine ⟨p,⟨hAccept.1,?_⟩,hAccept,hTrace,hGood⟩
  exact ⟨hFirstD,hIncoming⟩

/-- A concrete local Derives transition preserving an invariant builds an
actual initial accepting path and retains Good at EVERY judgement state. -/
theorem initial_accepting_path_of_invariant_steps
    (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (Inv : ClockValuation Clock → STLTableau.Judgement.Position P → Section3.StateForm Clock Var → Prop)
    (Good : Section3.TransitionForm Clock Var → Prop)
    (select : ∀ (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
      (N : Section3.StateForm Clock Var), Inv α k N → N.holds σ P α k →
      ∃ F : Section3.TransitionForm Clock Var, Derives N F ∧ F.holds σ P α k ∧ Good F ∧
        ∀ M, F.nextPart=some M → ∀hk : k.1<P.size,
          Inv (ClockResetSet.elapse (F.current.resets.apply α)
            (STLTableau.Judgement.duration P ⟨k.1,hk⟩)) ⟨k.1+1,by omega⟩ M)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hInv : Inv α k root) (hHolds : root.holds σ P α k) :
    ∃ p : Path Clock (Section3.TransitionForm Clock Var),
      p.run (JudgementTableau.tableau X Q root Derives) ∧
      p.accepting (JudgementTableau.tableau X Q root Derives) ∧
      (JudgementTableau.fullTrace p).holds σ P α k ∧
      Subgraph.AllStates {F | Good F} p :=
  initial_accepting_path_of_relation_steps X Q root σ P Derives Inv Good select α k hInv hHolds

/-- The adapter retains Inv even for empty locals. Actual output safety gives
an empty next state's raw presentation; zero completion keeps its guards and
unused resets rather than inventing a neutral judgement or selected tree. -/
theorem initial_accepting_path_of_nonempty_steps
    (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (Inv : ClockValuation Clock → STLTableau.Judgement.Position P → Section3.StateForm Clock Var → Prop)
    (Good : Section3.TransitionForm Clock Var → Prop)
    (select : ∀ (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
      (N : Section3.StateForm Clock Var), Inv α k N → N.holds σ P α k → N.locals.Nonempty →
      ∃ (F : Section3.TransitionForm Clock Var) (H : MixedJ Clock Var),
        Derives N F ∧ SafeNormalization H F ∧ F.holds σ P α k ∧ Good F ∧
        ∀ M, F.nextPart=some M → ∀hk : k.1<P.size,
          Inv (ClockResetSet.elapse (F.current.resets.apply α)
            (STLTableau.Judgement.duration P ⟨k.1,hk⟩)) ⟨k.1+1,by omega⟩ M)
    (emptyGood : ∀ (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
      (N : Section3.StateForm Clock Var), Inv α k N → N.locals=∅ → Good (.ofState N))
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hInv : Inv α k root) (hHolds : root.holds σ P α k)
    (hRoot : root.locals.Nonempty ∨ ∃K,SafeNormalization K (.ofState root)) :
    ∃ p : Path Clock (Section3.TransitionForm Clock Var),
      p.run (JudgementTableau.tableau X Q root Derives) ∧
      p.accepting (JudgementTableau.tableau X Q root Derives) ∧
      (JudgementTableau.fullTrace p).holds σ P α k ∧
      Subgraph.AllStates {F | Good F} p := by
  classical
  let Inv' := fun β j N => Inv β j N ∧ (N.locals.Nonempty ∨ ∃K,SafeNormalization K (.ofState N))
  apply initial_accepting_path_of_invariant_steps X Q root σ P Inv' Good _ α k ⟨hInv,hRoot⟩ hHolds
  intro β j N hNInv hNHolds
  by_cases hnonempty : N.locals.Nonempty
  · obtain ⟨F,H,hD,hSafe,hF,hGood,hNext⟩ := select β j N hNInv.1 hNHolds hnonempty
    refine ⟨F,hD,hF,hGood,?_⟩
    intro M hM hj
    refine ⟨hNext M hM hj,?_⟩
    by_cases hMnonempty : M.locals.Nonempty
    · exact Or.inl hMnonempty
    · exact Or.inr (hSafe.next_input hM)
  · have hempty : N.locals=∅ := by
      ext l
      exact ⟨fun hl => False.elim (hnonempty ⟨l,hl⟩),False.elim⟩
    obtain ⟨K,hK⟩ : ∃K,SafeNormalization K (.ofState N) := by
      rcases hNInv.2 with hnonempty' | hsafe
      · exact False.elim (hnonempty hnonempty')
      · exact hsafe
    refine ⟨.ofState N,Derives.empty_locals_terminal hK hempty,⟨hNHolds,trivial⟩,
      emptyGood β j N hNInv.1 hempty,?_⟩
    intro M hM
    cases hM

end STLTableau.Section4.Finiteness
