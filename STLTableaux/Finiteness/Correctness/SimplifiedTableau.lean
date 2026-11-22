/-
Copyright (c) 2026 STLTableau contributors. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: STLTableau contributors
-/
import STLTableaux.Finiteness.Correctness.JudgementTableauSoundness
import STLTableaux.Finiteness.Correctness.JudgementTraceFreeSupport
import STLTableaux.Finiteness.Inventory.Subgraph

/-! The paired graph of Definition D.4, parameterized by an admission relation.
The stored generator determines state membership. Edges use the next
judgement of the source transition form. -/
namespace STLTableau.Section4.Finiteness.PairedTableau
open Section3
local notation "StateForm" => Section3.StateForm
local notation "TransitionForm" => Section3.TransitionForm

variable {Clock Var : Type*} [DecidableEq Clock]

/-- The stored generator must occur in the original (nonfinite) tableau. -/
def OriginalGenerator (M : StateForm Clock Var) : Prop :=
  ∃ G, ConcreteContextual.catalogue.IsClosure (.ofState M) G

def tableau (X : Set Var) (Q : Set Clock) (root : StateForm Clock Var)
    (R : StateForm Clock Var → TransitionForm Clock Var → Prop) :
    Tableau Clock Var (ClosureState Clock Var) where
  realVariables := X
  clocks := Q
  states := {s | OriginalGenerator s.generator ∧ R s.generator s.form}
  edges := {e | (OriginalGenerator e.1.generator ∧ R e.1.generator e.1.form) ∧
    (OriginalGenerator e.2.2.generator ∧ R e.2.2.generator e.2.2.form) ∧
    ∃ M, e.1.form.nextPart = some M ∧ R M e.2.2.form ∧ e.2.1 = e.2.2.incoming}
  initial := {e | (OriginalGenerator e.2.generator ∧ R e.2.generator e.2.form) ∧
    R root e.2.form ∧ e.1 = e.2.incoming}
  final := {s | s.form.nextPart = none}
  label := Generated.labels
  label_atomic := fun _ _ h => h.2

theorem forget_valid (X : Set Var) (Q : Set Clock) (root : StateForm Clock Var)
    (R : StateForm Clock Var → TransitionForm Clock Var → Prop)
    (p : Path Clock (ClosureState Clock Var)) (h : p.valid (tableau X Q root R)) :
    (JudgementTableau.forgetGenerator p).valid (JudgementTableau.tableau X Q root R) := by
  induction p with
  | last e s => exact ⟨s.generator, h.2⟩
  | step e s p ih =>
    obtain ⟨hS, hP, hEdge⟩ := h
    obtain ⟨_, hT, M, hn, hM, he⟩ := hEdge
    refine ⟨⟨s.generator, hS.2⟩, ih hP, ?_⟩
    rw [JudgementTableau.first_state, JudgementTableau.first_incoming]
    exact ⟨⟨s.generator, hS.2⟩, ⟨p.firstState.generator, hT.2⟩, M, hn, hM, he⟩

theorem forget_run (X : Set Var) (Q : Set Clock) (root : StateForm Clock Var)
    (R : StateForm Clock Var → TransitionForm Clock Var → Prop)
    (p : Path Clock (ClosureState Clock Var)) (h : p.run (tableau X Q root R)) :
    (JudgementTableau.forgetGenerator p).run (JudgementTableau.tableau X Q root R) := by
  refine ⟨forget_valid X Q root R p h.1, ?_⟩
  rw [JudgementTableau.first_state, JudgementTableau.first_incoming]
  exact h.2.2

theorem forget_accepting (X : Set Var) (Q : Set Clock) (root : StateForm Clock Var)
    (R : StateForm Clock Var → TransitionForm Clock Var → Prop)
    (p : Path Clock (ClosureState Clock Var)) (h : p.accepting (tableau X Q root R)) :
    (JudgementTableau.forgetGenerator p).accepting (JudgementTableau.tableau X Q root R) := by
  refine ⟨forget_valid X Q root R p h.1, ?_⟩
  change (JudgementTableau.forgetGenerator p).lastState.nextPart = none
  rw [JudgementTableau.last_state]
  exact h.2

/-- Construct the paired run directly by induction on the remaining partition.
The generator at each chosen state is its actual input, with a witness that it
also occurs as a generator in the original tableau. -/
theorem accepting_path_of_steps
    (X : Set Var) (Q : Set Clock) (root : StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (R : StateForm Clock Var → TransitionForm Clock Var → Prop)
    (Inv : ClockValuation Clock → STLTableau.Judgement.Position P → StateForm Clock Var → Prop)
    (Good : ClosureState Clock Var → Prop)
    (select : ∀ (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
      (M : StateForm Clock Var), Inv α k M →
      ∃ F : TransitionForm Clock Var, OriginalGenerator M ∧ R M F ∧
        F.holds σ P α k ∧ Good ⟨F, M⟩ ∧
        ∀ M', F.nextPart = some M' → ∀ hk : k.val < P.size,
          Inv (ClockResetSet.elapse (F.current.resets.apply α)
            (STLTableau.Judgement.duration P ⟨k.val,hk⟩)) ⟨k.val+1,by omega⟩ M')
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) (hInv : Inv α k root) :
    ∃ p : Path Clock (ClosureState Clock Var),
      p.run (tableau X Q root R) ∧ p.accepting (tableau X Q root R) ∧
      p.fullTrace.holds σ P α k ∧ Subgraph.AllStates {s | Good s} p := by
  let T := tableau X Q root R
  have main : ∀ n : ℕ, ∀ (j : STLTableau.Judgement.Position P)
      (β : ClockValuation Clock) (M : StateForm Clock Var),
      P.size - j.val = n → Inv β j M →
      ∃ p : Path Clock (ClosureState Clock Var),
        p.firstState.generator = M ∧ p.firstIncoming = p.firstState.incoming ∧
        p.accepting T ∧ p.fullTrace.holds σ P β j ∧ Subgraph.AllStates {s | Good s} p := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j β M hn hM
      obtain ⟨F, hOriginal, hR, hF, hGood, hNext⟩ := select β j M hM
      let s : ClosureState Clock Var := ⟨F,M⟩
      have hS : s ∈ T.states := ⟨hOriginal,hR⟩
      cases hnext : F.nextPart with
      | none => exact ⟨.last s.incoming s, rfl, rfl, ⟨hS,hnext⟩, hF.1, hGood⟩
      | some M' =>
        have hj : j.val < P.size := by
          by_contra hnot
          have hh := hF.2
          simp only [hnext, dif_neg hnot] at hh
        let j' : STLTableau.Judgement.Position P := ⟨j.val+1,by omega⟩
        let γ := ClockResetSet.elapse (F.current.resets.apply β)
          (STLTableau.Judgement.duration P ⟨j.val,hj⟩)
        have hlt : P.size - j'.val < n := by dsimp [j']; omega
        obtain ⟨tail, hTailGen, hTailIn, hTail, hTailTrace, hTailGood⟩ :=
          ih (P.size-j'.val) hlt j' γ M' rfl (hNext M' hnext hj)
        have hT : tail.firstState ∈ T.states := Subgraph.first_state_of_valid T tail hTail.1
        have hR' : R tail.firstState.generator tail.firstState.form := hT.2
        rw [hTailGen] at hR'
        have hEdge : (s, tail.firstIncoming, tail.firstState) ∈ T.edges :=
          ⟨hS,hT,M',hnext,hR',hTailIn⟩
        refine ⟨.step s.incoming s tail, rfl, rfl, ⟨⟨hS,hTail.1,hEdge⟩,hTail.2⟩, ?_,
          hGood,hTailGood⟩
        change F.current.holds σ P β j ∧ (if hk : j.val < P.size then _ else False)
        exact ⟨hF.1, by simpa only [dif_pos hj, γ, j', s, ClosureState.incoming,
          Path.fullTrace, Trace.holds] using hTailTrace⟩
  obtain ⟨p, hG, hIn, hA, hTrace, hGood⟩ := main (P.size-k.val) k α root rfl hInv
  have hf : p.firstState ∈ T.states := Subgraph.first_state_of_valid T p hA.1
  have hRoot : R p.firstState.generator p.firstState.form := hf.2
  rw [hG] at hRoot
  exact ⟨p, ⟨hA.1,hf,hRoot,hIn⟩, hA, hTrace, hGood⟩

end STLTableau.Section4.Finiteness.PairedTableau
