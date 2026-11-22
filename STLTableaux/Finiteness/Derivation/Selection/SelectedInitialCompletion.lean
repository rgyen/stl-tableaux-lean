import STLTableaux.Finiteness.Derivation.Selection.SelectedPathOrigins

/-! The initial state containing `[φ]` has an empty origin domain. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

def plainInitialState (φ : Formula Var) : Section3.StateForm Clock Var :=
  .ofLocal (.predicate (.plain φ))

omit [DecidableEq Clock] in
private theorem initial_predicate_eq (φ : Formula Var) (p : Predicate Clock Var)
    (hp : Local.predicate p ∈ (plainInitialState (Clock:=Clock) φ).locals) : p=.plain φ := by
  simpa only [plainInitialState,Section3.StateForm.ofLocal,Set.mem_singleton_iff,Local.predicate.injEq] using hp

omit [DecidableEq Clock] in
private theorem initial_bounded_false (φ : Formula Var)
    (q : BoundedLocal (plainInitialState (Clock:=Clock) φ)) : False := by
  have he := initial_predicate_eq φ q.val q.property.1
  have hb := q.property.2
  rw [he] at hb
  exact hb

/-- Genuine initial proof data: all origin assertions are vacuous because
there is no local predicate in the `↑↓` form in the singleton state containing an unclocked
predicate. -/
def plainInitialOrigins (φ : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hReady : φ.MixedReady)
    (hHolds : Judgement.holds σ P α k (.predicate (.plain φ)))
    (hStable : σ.StablePartition φ P) : InputOrigins σ P α k (plainInitialState (Clock:=Clock) φ) := by
  have hInput : SafeNormalization (.predicate (.plain φ))
      (Section3.TransitionForm.ofState (plainInitialState (Clock:=Clock) φ)) := .predicate (.plain φ)
  have hi : (Section3.Judgement.predicate (.plain φ) : MixedJ Clock Var).EvaluatedInvariant σ P α k := by
    intro hk
    trivial
  have hs : (Section3.Judgement.predicate (.plain φ) : MixedJ Clock Var).UnderlyingStable σ P := by
    intro ψ hψ
    have he : ψ=φ := hψ
    subst ψ
    exact hStable
  refine {
    ready := hInput.ready.2 hReady
    holds := ((hInput.holds σ P α k).2 hHolds).1
    fullInvariant := ((hInput.fullInvariant σ P α k).2 hi).1
    stable := (hInput.stable σ P).2 hs
    private_current := ?_
    no_upper := ?_
    last := fun q => False.elim (initial_bounded_false φ q)
    is_end := fun q => False.elim (initial_bounded_false φ q)
    injective_per_formula := fun q => False.elim (initial_bounded_false φ q)
    classification := fun q => False.elim (initial_bounded_false φ q)
    current_entry := fun q => False.elim (initial_bounded_false φ q)
    ended_endpoint := fun q => False.elim (initial_bounded_false φ q) }
  · intro p q hp hq hne
    exact False.elim (hne ((initial_predicate_eq φ p hp).trans (initial_predicate_eq φ q hq).symm))
  · intro c m kind I ψ hp
    have he := initial_predicate_eq φ (.upper c m kind I ψ) hp
    cases he

end STLTableau.Section4.Finiteness
