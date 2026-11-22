/-
Copyright (c) 2026 STLTableau contributors. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: STLTableau contributors
-/
import STLTableaux.Finiteness.Derivation.SimplifiedClosure
import STLTableaux.Finiteness.Correctness.SimplifiedTableau
import STLTableaux.Finiteness.ClockAllocation.AllocatedSelectedPath
import STLTableaux.Closure.Normalization.FaithfulAlphaInvariant
import STLTableaux.Closure.Normalization.FaithfulAlphaStability

/-! The selected raw branches are replayed as completed derivations.
The fixed palette is applied before deleting unused resets; the resulting
literal next input is carried to the next state of the paired path. -/
namespace STLTableau.Section4.Finiteness
open Section3 ResetTrimming
local notation "StateForm" => Section3.StateForm
local notation "TransitionForm" => Section3.TransitionForm

variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

/-- Replay the selected expansion using the completion rules. At a boundary
merge, an opening branch supplies the `↑` form with its left clock reset to zero. -/
noncomputable def Resolve.completedTree {J H A : MixedJ Clock Var} (D : Resolve J H A) :
    CompletedDerivation.Tree J H A := by
  induction D with
  | leaf h => exact .leaf h
  | conj _ _ ih ig => exact .conj ih ig
  | reset R _ ih => exact .reset R ih
  | structural h _ ih => exact .structural h ih
  | expandCtx hb hn hf _ ih => exact .expandCtx hb hn hf ih
  | expandSolo hb hn hf _ ih => exact .expandSolo hb hn hf ih
  | @boundaryRequired c d m ℓ kind I φ Γ H A frozen hdΓ _ ih =>
      exact .boundaryRequired frozen.distinct
        (CompletedDerivation.opening_exists c d ℓ kind I φ Γ) hdΓ ih
  | @boundaryOptional c d m ℓ kind I φ Γ H A frozen hdΓ _ ih =>
      exact .boundaryOptional frozen.distinct
        (CompletedDerivation.opening_exists c d ℓ kind I φ Γ) hdΓ ih
  | unusedReset d v hdJ hdH _ ih => exact .unusedReset d v hdJ hdH ih

theorem ResolvedCertificate.completed_admitted
    {M : StateForm Clock Var} {F : TransitionForm Clock Var}
    (C : ResolvedCertificate M F) (e : Equiv.Perm Clock) :
    CompletedDerivation.Admitted (trimState (M.rename e)) (trim (renameTransition e F)) := by
  have hJ : SafeNormalization (renameJudgement e C.input) (.ofState (M.rename e)) := by
    simpa only [rename_ofState] using C.input_safe.rename e
  have hH := C.full_safe.rename e
  have hA : SafeNormalization (renameJudgement e C.erased)
      (renameTransition e F).atomicProjection := by
    simpa only [rename_atomicProjection] using C.erased_safe.rename e
  have D := C.resolves.rename e
  exact CompletedDerivation.admitted_trim (.completed D.completedTree hJ hH hA)

/-- The original closure needed for the stored generator is chosen after
renaming and trim, under the same signal and partition invariants. -/
theorem originalGenerator_trim_rename (X : Set Var) (Q : Set Clock)
    (root N : StateForm Clock Var) (e : Equiv.Perm Clock) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α β : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (agree : ∀ c ∈ N.freeClocks, β (e c) = α c)
    (hs : N.holds σ P α k) (hi : N.EvaluatedInvariant σ P α k)
    (hst : N.UnderlyingStable σ P) : PairedTableau.OriginalGenerator (trimState (N.rename e)) := by
  have ha : ∀ c ∈ N.freeClocks, α c = (β ∘ e) c := fun c hc => (agree c hc).symm
  have hs' := (N.holds_rename e σ P β k).2 ((N.holds_congr_of_agree σ P α (β ∘ e) k ha).1 hs)
  have hi' := (N.evaluatedInvariant_rename e σ P β k).2
    ((N.evaluatedInvariant_congr σ P α (β ∘ e) k ha).1 hi)
  have hst' : (trimState (N.rename e)).UnderlyingStable σ P := by
    change ∀ φ ∈ (N.rename e).underlyingFormulas, σ.StablePartition φ P
    rw [Section3.StateForm.underlyingFormulas_rename]
    exact hst
  obtain ⟨F, _, hF, _, _, _⟩ := Generated.generator_path_exists_with_closure
    X Q root σ P β k (trimState (N.rename e)) hst'
    ((trimState_invariant _ _ _ _ _).2 hi') ((trimState_holds _ _ _ _ _).2 hs')
  exact ⟨F,hF⟩

private structure TrimmedInputWitness
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    (Inv : ClockValuation Clock → STLTableau.Judgement.Position P → StateForm Clock Var → Prop)
    (Frame : ClockValuation Clock → STLTableau.Judgement.Position P → StateForm Clock Var →
      Equiv.Perm Clock → Prop)
    (β : ClockValuation Clock) (k : STLTableau.Judgement.Position P) (M : StateForm Clock Var) where
  valuation : ClockValuation Clock
  raw : StateForm Clock Var
  incoming : Equiv.Perm Clock
  invariant : Inv valuation k raw
  frame : Frame valuation k raw incoming
  input_eq : M = trimState (raw.rename incoming)
  agreement : ∀ c ∈ raw.freeClocks, β (incoming c) = valuation c

/-- Assemble the finite-palette path using the actual next input of each
trimmed judgement, choosing its stored generator to be that same input. -/
theorem path_of_local_extensions
    (X : Set Var) (Q : Set Clock) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (Inv : ClockValuation Clock → STLTableau.Judgement.Position P → StateForm Clock Var → Prop)
    (Frame : ClockValuation Clock → STLTableau.Judgement.Position P → StateForm Clock Var →
      Equiv.Perm Clock → Prop)
    (Good : ClosureState Clock Var → Prop)
    (sem : ∀ α k N, Inv α k N →
      N.holds σ P α k ∧ N.EvaluatedInvariant σ P α k ∧ N.UnderlyingStable σ P)
    (extend : ∀ α k N, Inv α k N → ∀ e₀, Frame α k N e₀ →
      ∃ (F : TransitionForm Clock Var) (C : ResolvedCertificate N F) (e : Equiv.Perm Clock),
        (∀ c ∈ (Section3.TransitionForm.ofState N).allClocks, e c = e₀ c) ∧ F.holds σ P α k ∧
        Good ⟨trim (renameTransition e F), trimState (N.rename e₀)⟩ ∧
        ∀ M, F.nextPart = some M → ∀ hk : k.val < P.size,
          let α' := ClockResetSet.elapse (F.current.resets.apply α)
            (STLTableau.Judgement.duration P ⟨k.val,hk⟩)
          Inv α' ⟨k.val+1,by omega⟩ M ∧ Frame α' ⟨k.val+1,by omega⟩ M e)
    (α β : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (N : StateForm Clock Var) (hInv : Inv α k N)
    (e₀ : Equiv.Perm Clock) (hFrame : Frame α k N e₀)
    (agree : ∀ c ∈ N.freeClocks, β (e₀ c) = α c) :
    ∃ p : Path Clock (ClosureState Clock Var),
      p.run (PairedTableau.tableau X Q (trimState (N.rename e₀)) CompletedDerivation.Admitted) ∧
      p.accepting (PairedTableau.tableau X Q (trimState (N.rename e₀))
        CompletedDerivation.Admitted) ∧
      p.fullTrace.holds σ P β k ∧ Subgraph.AllStates {s | Good s} p := by
  let root := trimState (N.rename e₀)
  let Inv' := fun b j M => Nonempty (TrimmedInputWitness Inv Frame b j M)
  apply PairedTableau.accepting_path_of_steps X Q root σ P
    CompletedDerivation.Admitted Inv' Good _ β k
    ⟨⟨α,N,e₀,hInv,hFrame,rfl,agree⟩⟩
  intro b j M hW
  obtain ⟨w⟩ := hW
  obtain ⟨F,C,e,he,hF,hGood,hNext⟩ := extend w.valuation j w.raw w.invariant w.incoming w.frame
  have hEq : w.raw.rename e = w.raw.rename w.incoming := by
    apply state_rename_congr
    intro c hc
    exact he c (by rw [ofState_support]; exact hc)
  have ha : ∀ c ∈ w.raw.freeClocks, b (e c) = w.valuation c := by
    intro c hc
    have hs : c ∈ stateClockSupport w.raw := by
      rcases hc with hg | ⟨hl,_⟩
      · exact Or.inl (Or.inl hg)
      · exact Or.inl (Or.inr hl)
    rw [he c (by rw [ofState_support]; exact hs)]
    exact w.agreement c hc
  obtain ⟨hs,hi,hst⟩ := sem w.valuation j w.raw w.invariant
  have hOriginal := originalGenerator_trim_rename X Q root w.raw w.incoming σ P
    w.valuation b j w.agreement hs hi hst
  rw [← w.input_eq] at hOriginal hGood
  have hF' := resolved_rename_holds C.resolves C.input_safe C.full_safe e σ P w.valuation b j ha hF
  have hAdmit : CompletedDerivation.Admitted M (trim (renameTransition e F)) := by
    rw [w.input_eq, ← hEq]
    exact C.completed_admitted e
  refine ⟨_, hOriginal, hAdmit, (trim_holds _ _ _ _ _).2 hF', hGood, ?_⟩
  intro M' hn hj
  cases hnext : F.nextPart with
  | none => simp [renameTransition,hnext] at hn
  | some K =>
    have heNext : (renameTransition e F).nextPart = some (K.rename e) := by
      simp [renameTransition,hnext]
    have hM : M' = trimState (K.rename e) := by
      simpa only [trim_next, heNext, Option.map_some, Option.some.injEq] using hn.symm
    obtain ⟨hI,hFr⟩ := hNext K hnext hj
    refine ⟨⟨_,K,e,hI,hFr,hM,?_⟩⟩
    intro c hc
    have hc' : e c ∈ (K.rename e).freeClocks := by
      rw [Section3.StateForm.freeClocks_rename]
      exact ⟨c,hc,rfl⟩
    rw [trim_elapse_agree_next heNext b _ hc']
    exact renamed_successor_agreement hnext
      (selected_resolution_free_subset C.resolves C.input_safe C.full_safe) e e _ b _
      ha (fun _ _=>rfl) c hc

end STLTableau.Section4.Finiteness
