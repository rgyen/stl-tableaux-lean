import STLTableaux.Finiteness.Derivation.Selection.SelectedSuccessorOrigins
import STLTableaux.Finiteness.Derivation.Selection.SelectedInitialCompletion
import STLTableaux.Finiteness.Correctness.SelectedAcceptingPath
import STLTableaux.Finiteness.Correctness.Step1AcceptingEquivalence

/-! Actual initial accepting paths constructed from origin-preserving selected
steps. Per-state origin/ledger evidence is retained for the subsequent uniform
count theorem; this module does not assert a numerical state bound. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

/-- Proof-only evidence about actual constructed path states. It changes no
state or edge admission: every selected witness is the SAME tree that supplies
its real Derives transition and full output semantics. -/
inductive OriginCertifiedState (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) :
    Section3.TransitionForm Clock Var → Prop
  | empty (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
      (N : Section3.StateForm Clock Var) (O : InputOrigins σ P α k N) (he : N.locals = ∅) :
      OriginCertifiedState σ P (.ofState N)
  | selected (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
      (N : Section3.StateForm Clock Var) (O : InputOrigins σ P α k N)
      (J : MixedJ Clock Var) (W : Set Clock) (owned : OwnedPending J N.resets W)
      (H Er : MixedJ Clock Var) (F : Section3.TransitionForm Clock Var)
      (T : SelectedTree O.eligible O.strictClocks owned H Er)
      (hnil : owned.nextInputs = []) (hInput : SafeNormalization J (.ofState N))
      (hNext : NextPrivate J) (hD : Derives N F)
      (facts : SelectedOutputFacts owned ∅ O.strictClocks σ P α k H Er F) :
      OriginCertifiedState σ P F

/-- The actual finite-partition path construction, with origin-certified
proof data at EVERY actual judgement state. Empty successors keep their actual
safe representation and zero completion; no selected tree is fabricated there. -/
theorem origin_certified_accepting_path
    (X : Set Var) (Q : Set Clock) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hReady : φ.MixedReady)
    (hPlain : Judgement.holds σ P α k (.predicate (.plain φ)))
    (hStable : σ.StablePartition φ P) :
    ∃ p : Path Clock (Section3.TransitionForm Clock Var),
      p.run (JudgementTableau.tableau X Q (plainInitialState (Clock := Clock) φ) Derives) ∧
      p.accepting (JudgementTableau.tableau X Q (plainInitialState (Clock := Clock) φ) Derives) ∧
      (JudgementTableau.fullTrace p).holds σ P α k ∧
      Subgraph.AllStates {F | OriginCertifiedState σ P F} p := by
  let Inv := fun (β : ClockValuation Clock) (j : STLTableau.Judgement.Position P)
    (N : Section3.StateForm Clock Var) => Nonempty (InputOrigins σ P β j N)
  let O := plainInitialOrigins (Clock := Clock) φ σ P α k hReady hPlain hStable
  apply initial_accepting_path_of_nonempty_steps X Q (plainInitialState (Clock := Clock) φ)
    σ P Inv (OriginCertifiedState σ P) _ _ α k ⟨O⟩ O.holds
    (Or.inl ⟨.predicate (.plain φ),by simp [plainInitialState,Section3.StateForm.ofLocal]⟩)
  · intro β j N hInv _ hne
    obtain ⟨O⟩ := hInv
    obtain ⟨J,W,owned,H,Er,F,T,hnil,hInput,hNext,hD,hFacts,hGuards,hSuccessor⟩ := O.nonempty_origin_step hne
    refine ⟨F,H,hD,hFacts.1,hFacts.2.2.1,
      OriginCertifiedState.selected β j N O J W owned H Er F T hnil hInput hNext hD hFacts,?_⟩
    intro M hn hj
    exact hSuccessor hj M hn
  · intro β j N hInv he
    obtain ⟨O⟩ := hInv
    exact OriginCertifiedState.empty β j N O he

/-- Point truth plus the same fully stable partition supplies the initial
plain piece, then the concrete origin-preserving accepting path. -/
theorem origin_certified_path_of_formula
    (X : Set Var) (Q : Set Clock) (φ : Formula Var) (hReady : φ.MixedReady)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (hStable : σ.StablePartition φ P)
    (hTruth : σ.Satisfies φ ⟨0,le_rfl,σ.horizon_pos⟩) :
    ∃ p : Path Clock (Section3.TransitionForm Clock Var),
      p.run (JudgementTableau.tableau X Q (plainInitialState (Clock := Clock) φ) Derives) ∧
      p.accepting (JudgementTableau.tableau X Q (plainInitialState (Clock := Clock) φ) Derives) ∧
      (JudgementTableau.fullTrace p).holds σ P α ⟨0,by omega⟩ ∧
      Subgraph.AllStates {F | OriginCertifiedState σ P F} p := by
  apply origin_certified_accepting_path X Q φ σ P α ⟨0,by omega⟩ hReady _ hStable
  change if hk : 0 < P.size then _ else False
  simp only [dif_pos (Generated.partition_size_pos σ P)]
  intro t ht
  exact ((hStable ⟨0,Generated.partition_size_pos σ P⟩).stable
    ⟨0,le_rfl,σ.horizon_pos⟩ t (Generated.zero_mem_first_interval σ P) ht).mp hTruth

/-- Starting from an arbitrary satisfied revised accepting run, construct an
origin-certified accepting path on the SAME signal, partition and valuation. -/
theorem origin_certified_path_of_satisfied_run
    (X : Set Var) (Q : Set Clock) (φ : Formula Var) (hReady : φ.MixedReady)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (hStable : σ.StablePartition φ P) (p : Path Clock (Section3.TransitionForm Clock Var))
    (hr : p.run (JudgementTableau.tableau X Q (plainInitialState (Clock := Clock) φ) Derives))
    (ha : p.accepting (JudgementTableau.tableau X Q (plainInitialState (Clock := Clock) φ) Derives))
    (hs : (JudgementTableau.fullTrace p).holds σ P α ⟨0,by omega⟩) :
    ∃ q : Path Clock (Section3.TransitionForm Clock Var),
      q.run (JudgementTableau.tableau X Q (plainInitialState (Clock := Clock) φ) Derives) ∧
      q.accepting (JudgementTableau.tableau X Q (plainInitialState (Clock := Clock) φ) Derives) ∧
      (JudgementTableau.fullTrace q).holds σ P α ⟨0,by omega⟩ ∧
      Subgraph.AllStates {F | OriginCertifiedState σ P F} q :=
  origin_certified_path_of_formula X Q φ hReady σ P α hStable
    (formula_of_satisfied_derives_run X Q φ σ P α p hr ha hs)
/-- The same construction starting from an arbitrary satisfied original
closure-tableau run, using the already verified Step 1 full-trace equivalence. -/
theorem origin_certified_path_of_original_run
    (X : Set Var) (Q : Set Clock) (φ : Formula Var) (hReady : φ.MixedReady)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (hStable : σ.StablePartition φ P) (p : Path Clock (ClosureState Clock Var))
    (hr : p.run (Generated.closureTableau ConcreteContextual.catalogue X Q
      (Section3.StateForm.ofLocal (.predicate (.plain φ)))))
    (ha : p.accepting (Generated.closureTableau ConcreteContextual.catalogue X Q
      (Section3.StateForm.ofLocal (.predicate (.plain φ)))))
    (hs : p.fullTrace.holds σ P α ⟨0,by omega⟩) :
    ∃ q : Path Clock (Section3.TransitionForm Clock Var),
      q.run (JudgementTableau.tableau X Q (plainInitialState (Clock := Clock) φ) Derives) ∧
      q.accepting (JudgementTableau.tableau X Q (plainInitialState (Clock := Clock) φ) Derives) ∧
      (JudgementTableau.fullTrace q).holds σ P α ⟨0,by omega⟩ ∧
      Subgraph.AllStates {F | OriginCertifiedState σ P F} q := by
  obtain ⟨q,hq,haq,hsq⟩ := (step1_satisfied_accepting_iff X Q φ hReady σ P hStable α).1 ⟨p,hr,ha,hs⟩
  exact origin_certified_path_of_satisfied_run X Q φ hReady σ P α hStable q hq haq hsq
end STLTableau.Section4.Finiteness
