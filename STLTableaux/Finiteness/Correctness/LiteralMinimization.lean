import STLTableaux.Finiteness.Inventory.FiniteInventory

/-! Minimalization preserves a finite inventory and satisfaction.
These local results do not assert preservation of a path's next generators. -/
namespace STLTableau.Section4.Finiteness.FiniteInventory
open Section3
variable {Clock Var : Type*}

theorem Within.of_componentsIncluded
    {L : Finset (Local Clock Var)} {G : Finset (Guard Clock)}
    {R : Finset (Clock × NNReal)} {S T : Section3.StateForm Clock Var}
    (hT : Within L G R T) (h : ComponentsIncluded S T) : Within L G R S :=
  ⟨h.locals.trans hT.1, h.guards.trans hT.2.1,
    fun c a hc => hT.2.2 c a (h.resets c a hc)⟩

theorem TransitionWithin.of_subsumed
    {L : Finset (Local Clock Var)} {G : Finset (Guard Clock)}
    {R : Finset (Clock × NNReal)} {S T : Section3.TransitionForm Clock Var}
    (hT : TransitionWithin L G R T) (h : Section3.SyntacticallySubsumed S T) :
    TransitionWithin L G R S := by
  refine ⟨hT.1.of_componentsIncluded h.current, ?_⟩
  intro N hn
  obtain ⟨M, hm, hi, _⟩ := h.next N hn
  exact (hT.2 M hm).of_componentsIncluded hi

theorem exists_satisfied_minimal_within
    (E : Section3.ClosureCatalogue Clock Var)
    {L : Finset (Local Clock Var)} {G : Finset (Guard Clock)}
    {R : Finset (Clock × NNReal)} {Φ U : Section3.TransitionForm Clock Var}
    (hu : Section3.SyntacticallySubsumed Φ U) (hc : E.IsClosed U)
    (hi : TransitionWithin L G R U)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hs : U.holds σ P α k) :
    ∃ V, E.IsClosure Φ V ∧ Section3.SyntacticallySubsumed V U ∧
      TransitionWithin L G R V ∧ V.holds σ P α k := by
  obtain ⟨V, hv, hVU, hsV⟩ := E.exists_satisfied_minimal_below hu hc σ P α k hs
  exact ⟨V, hv, hVU, hi.of_subsumed hVU, hsV⟩

end STLTableau.Section4.Finiteness.FiniteInventory
