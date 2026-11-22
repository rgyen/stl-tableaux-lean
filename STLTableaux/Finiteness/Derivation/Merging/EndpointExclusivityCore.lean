import STLTableaux.Closure.Normalization.ConcreteNormalization

/-! Endpoint syntax and exclusivity, independent of representative choices. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

def endpointClocks : Predicate Clock Var → Set Clock
  | .plain _ => ∅
  | .upper c _ _ _ _ => {c}
  | .bounded c d _ _ _ _ _ => {c, d}

def localEndpointClocks : Local Clock Var → Set Clock
  | .predicate p => endpointClocks p
  | _ => ∅

theorem localEndpointClocks_eq_freeClocks (l : Local Clock Var) :
    localEndpointClocks l = l.freeClocks := by
  cases l with
  | terminal | marker => rfl
  | predicate p =>
    cases p <;> simp [localEndpointClocks, endpointClocks, Local.freeClocks,
      Local.toJudgement, Section3.Judgement.freeClocks]

def ExclusiveState (S : Section3.StateForm Clock Var) : Prop :=
  ∀ p, Local.predicate p ∈ S.locals → ∀ q, Local.predicate q ∈ S.locals →
    p ≠ q → Disjoint (endpointClocks p) (endpointClocks q)

theorem ExclusiveState.of_locals_subset {S R : Section3.StateForm Clock Var}
    (h : ExclusiveState S) (hr : R.locals ⊆ S.locals) : ExclusiveState R :=
  fun p hp q hq hn => h p (hr hp) q (hr hq) hn

theorem ExclusiveState.endpoints_ne {S : Section3.StateForm Clock Var}
    (h : ExclusiveState S) {p q : Predicate Clock Var}
    (hp : Local.predicate p ∈ S.locals) (hq : Local.predicate q ∈ S.locals)
    (hne : p ≠ q) {c d : Clock} (hc : c ∈ endpointClocks p) (hd : d ∈ endpointClocks q) :
    c ≠ d := by
  intro he
  subst d
  exact Set.disjoint_left.mp (h p hp q hq hne) hc hd

theorem plain_exclusive (φ : Formula Var) :
    ExclusiveState (Section3.StateForm.ofLocal (.predicate (.plain φ)) :
      Section3.StateForm Clock Var) := by
  intro p hp q hq hne
  have hp' : p = .plain φ := Local.predicate.inj hp
  have hq' : q = .plain φ := Local.predicate.inj hq
  exact (hne (hp'.trans hq'.symm)).elim

end STLTableau.Section4.Finiteness
