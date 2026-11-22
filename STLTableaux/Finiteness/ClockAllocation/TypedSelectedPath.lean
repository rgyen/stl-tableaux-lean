import STLTableaux.Finiteness.ClockAllocation.AllocatedSelectedPath
import STLTableaux.Finiteness.Correctness.JudgementTraceFreeSupport

/-! Path composition interface for a LOCAL typed owner allocator. This module
constructs an actual path from local syntactic extensions; it does not establish
that an owner-frame allocator exists for the sparse inventory. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

/-- A proof-only witness linked to the actual renamed input. Frame is supplied
by the typed allocator and may track supported generations rather than ghost
clock names. No graph admission condition is added. -/
structure RenamedInputWitness
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    (Inv : ClockValuation Clock → STLTableau.Judgement.Position P → Section3.StateForm Clock Var → Prop)
    (Frame : ClockValuation Clock → STLTableau.Judgement.Position P →
      Section3.StateForm Clock Var → Equiv.Perm Clock → Prop)
    (β : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (N : Section3.StateForm Clock Var) where
  originalValuation : ClockValuation Clock
  originalInput : Section3.StateForm Clock Var
  incoming : Equiv.Perm Clock
  invariant : Inv originalValuation k originalInput
  frame : Frame originalValuation k originalInput incoming
  input_eq : N=originalInput.rename incoming
  agreement : ∀c∈originalInput.freeClocks,β (incoming c)=originalValuation c

/-- Reuse the actual finite-partition recursion with an input-linked typed
allocator. Every local choice is an actual Resolve+safe certificate. The local
extension premise is explicit and must be discharged by the typed owner proof. -/
theorem typed_path_of_local_extensions
    (X : Set Var) (Q : Set Clock)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (Inv : ClockValuation Clock → STLTableau.Judgement.Position P → Section3.StateForm Clock Var → Prop)
    (Frame : ClockValuation Clock → STLTableau.Judgement.Position P →
      Section3.StateForm Clock Var → Equiv.Perm Clock → Prop)
    (Good : Section3.TransitionForm Clock Var → Prop)
    (extend : ∀ α k N, Inv α k N → ∀e0,Frame α k N e0 →
      ∃ (F : Section3.TransitionForm Clock Var) (C : ResolvedCertificate N F) (e : Equiv.Perm Clock),
        (∀c∈(Section3.TransitionForm.ofState N).allClocks,e c=e0 c) ∧
        F.holds σ P α k ∧ Good (renameTransition e F) ∧
        ∀ M, F.nextPart=some M → ∀hk : k.1<P.size,
          let α' := ClockResetSet.elapse (F.current.resets.apply α)
            (STLTableau.Judgement.duration P ⟨k.1,hk⟩)
          Inv α' ⟨k.1+1,by omega⟩ M ∧ Frame α' ⟨k.1+1,by omega⟩ M e)
    (α β : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (N : Section3.StateForm Clock Var) (hInv : Inv α k N) (hHolds : N.holds σ P α k)
    (e0 : Equiv.Perm Clock) (hFrame : Frame α k N e0)
    (hAgree : ∀c∈N.freeClocks,β (e0 c)=α c) :
    ∃ p : Path Clock (Section3.TransitionForm Clock Var),
      p.run (JudgementTableau.tableau X Q (N.rename e0) FreeDerives) ∧
      p.accepting (JudgementTableau.tableau X Q (N.rename e0) FreeDerives) ∧
      (JudgementTableau.fullTrace p).holds σ P β k ∧ Subgraph.AllStates {F | Good F} p := by
  let Inv' := fun (b : ClockValuation Clock) (j : STLTableau.Judgement.Position P)
    (M : Section3.StateForm Clock Var) => Nonempty (RenamedInputWitness Inv Frame b j M)
  have hN : (N.rename e0).holds σ P β k := by
    apply (Section3.StateForm.holds_rename N e0 σ P β k).2
    apply (N.holds_congr_of_agree σ P α (β ∘ e0) k _).1 hHolds
    exact fun c hc=>(hAgree c hc).symm
  apply initial_accepting_path_of_relation_steps X Q (N.rename e0) σ P FreeDerives Inv' Good _ β k
    ⟨⟨α,N,e0,hInv,hFrame,rfl,hAgree⟩⟩ hN
  intro b j M hW _
  obtain ⟨w⟩ := hW
  obtain ⟨F,C,e,he,hF,hGood,hNext⟩ := extend w.originalValuation j w.originalInput w.invariant w.incoming w.frame
  have hEq : w.originalInput.rename e=w.originalInput.rename w.incoming := by
    apply state_rename_congr
    intro c hc
    apply he c
    rw [ofState_support]
    exact hc
  have ha : ∀c∈w.originalInput.freeClocks,b (e c)=w.originalValuation c := by
    intro c hc
    have hs : c∈stateClockSupport w.originalInput := by
      rcases hc with hg | ⟨hl,_⟩
      · exact Or.inl (Or.inl hg)
      · exact Or.inl (Or.inr hl)
    rw [he c (by rw [ofState_support]; exact hs)]
    exact w.agreement c hc
  have hD : FreeDerives M (renameTransition e F) := by
    rw [w.input_eq,←hEq]
    exact C.rename_freeDerives e
  refine ⟨renameTransition e F,hD,
    resolved_rename_holds C.resolves C.input_safe C.full_safe e σ P _ b j ha hF,hGood,?_⟩
  intro M' hn hj
  cases hnext : F.nextPart with
  | none => simp [renameTransition,hnext] at hn
  | some K =>
      have hM : M'=K.rename e := by simpa [renameTransition,hnext] using hn.symm
      obtain ⟨hI,hFr⟩ := hNext K hnext hj
      refine ⟨⟨_,K,e,hI,hFr,hM,?_⟩⟩
      exact renamed_successor_agreement hnext C.freeDerives.2 e e _ b _ ha (fun _ _=>rfl)
end STLTableau.Section4.Finiteness
