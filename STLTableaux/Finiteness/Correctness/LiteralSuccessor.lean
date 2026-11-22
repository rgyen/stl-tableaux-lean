import STLTableaux.Finiteness.Correctness.LiteralRootTableau
import STLTableaux.Closure.Subsumption.InvariantTransport
import STLTableaux.Closure.Correctness.FaithfulFreeClosure

/-! Continue with the actual next judgement of a literal closure.
No next judgement from the extended derivation graph is substituted. -/
namespace STLTableau.Section4.Finiteness
variable {Clock Var : Type*} [DecidableEq Clock]

theorem LiteralDerives.ready {N : Section3.StateForm Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : LiteralDerives N F) : F.Ready :=
  Section3.ConcreteContextual.closure_ready h.1
    ((Section3.TransitionForm.ready_ofState N).2 h.2)

/-- The successor uses the selected closure's resets and the current interval's
duration, including zero duration for a singleton interval. -/
theorem LiteralDerives.next_data {N M : Section3.StateForm Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : LiteralDerives N F)
    (hn : F.nextPart = some M)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hk : k.1 < P.size)
    (hs : F.holds σ P α k) (hi : F.EvaluatedInvariant σ P α k)
    (hst : F.UnderlyingStable σ P) :
    let β := ClockResetSet.elapse (F.current.resets.apply α)
      (STLTableau.Judgement.duration P ⟨k.1, hk⟩)
    M.Ready ∧ M.holds σ P β ⟨k.1 + 1, by omega⟩ ∧
      M.EvaluatedInvariant σ P β ⟨k.1 + 1, by omega⟩ ∧ M.UnderlyingStable σ P := by
  refine ⟨h.ready.2 M hn, ?_, hi.2 M hn hk, hst.next M hn⟩
  simpa only [Section3.TransitionForm.holds, hn, dif_pos hk] using hs.2

variable [Infinite Clock]

/-- Apply the closure-existence lemma to the actual successor.
This result does not claim that the new clocks fit the fixed finite inventory. -/
theorem LiteralDerives.next_closure_exists {N M : Section3.StateForm Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : LiteralDerives N F)
    (hn : F.nextPart = some M)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hk : k.1 < P.size)
    (hs : F.holds σ P α k) (hi : F.EvaluatedInvariant σ P α k)
    (hst : F.UnderlyingStable σ P) :
    let β := ClockResetSet.elapse (F.current.resets.apply α)
      (STLTableau.Judgement.duration P ⟨k.1, hk⟩)
    ∃ G, LiteralDerives M G ∧ G.holds σ P β ⟨k.1 + 1, by omega⟩ ∧
      G.EvaluatedInvariant σ P β ⟨k.1 + 1, by omega⟩ ∧
      G.UnderlyingStable σ P ∧ G.freeClocks ⊆ M.freeClocks := by
  obtain ⟨hr, hsM, hiM, hstM⟩ := h.next_data hn σ P α k hk hs hi hst
  obtain ⟨G, hc, hsG, hiG, hstG, hfG⟩ :=
    Section3.FaithfulClosure.satisfied_closure_exists_free M σ P _ _ hsM hiM hstM
  exact ⟨G, ⟨hc, hr⟩, hsG, hiG, hstG, hfG⟩

/-- Minimalization retains all semantic premises needed at the next position.
The rule-closed extension and finite-inventory evidence are explicit premises. -/
theorem finiteLiteralRootTableau_exists_minimal_state_preserving
    (X : Set Var) (root : Formula Var) {N : Section3.StateForm Clock Var}
    {U : Section3.TransitionForm Clock Var} (hn : N.Ready)
    (hu : Section3.SyntacticallySubsumed (.ofState N) U)
    (hc : Section3.ConcreteContextual.catalogue.IsClosed U)
    (hinv : FiniteInventory.TransitionWithin
      (FiniteInventory.locals (Finiteness.rootPlainFormulas root) (rootSlotTriples root))
      (FiniteInventory.guards (rootSlotTriples root))
      (FiniteInventory.resets (rootSlotTriples root)) U)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hs : U.holds σ P α k)
    (hi : U.EvaluatedInvariant σ P α k) (hst : U.UnderlyingStable σ P) :
    ∃ V, V ∈ (finiteLiteralRootTableau X root).states ∧ LiteralDerives N V ∧
      Section3.SyntacticallySubsumed V U ∧ V.holds σ P α k ∧
      V.EvaluatedInvariant σ P α k ∧ V.UnderlyingStable σ P ∧ V.Ready := by
  obtain ⟨V, hv, hd, hVU, hsV⟩ :=
    finiteLiteralRootTableau_exists_minimal_state X root hn hu hc hinv σ P α k hs
  exact ⟨V, hv, hd, hVU, hsV, hVU.evaluatedInvariant σ P α k hi,
    hVU.underlyingStable σ P hst, hd.ready⟩

end STLTableau.Section4.Finiteness
