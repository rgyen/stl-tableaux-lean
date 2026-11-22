import STLTableaux.Tableau.Construction.TableauState

/-! Pure temporal label-family inventories and their finite support.
No representative selection or path construction is imported here. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

def FiniteEventualChild (I : BoundedTimeInterval) (φ : Formula Var)
    (p : Predicate Clock Var) : Prop :=
  ∃ c d b q, p = .bounded c d b q .eventually (.bounded I) φ

def upperKindSignature (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    Set (Local Clock Var) := {l | ∃ c b, l = .predicate (.upper c b kind I φ)}

def unboundedEventualSignature (a : NNReal) (φ : Formula Var) : Set (Local Clock Var) :=
  {l | ∃ c d b q, l = .predicate (.bounded c d b q .eventually (.unbounded a) φ)}

def boundedEventualParents (S : Section3.StateForm Clock Var)
    (I : BoundedTimeInterval) (φ : Formula Var) : Set (Predicate Clock Var) :=
  {p | Local.predicate p ∈ S.locals ∧ FiniteEventualChild I φ p}

theorem boundedEventualParents_finite (S : Section3.StateForm Clock Var)
    (I : BoundedTimeInterval) (φ : Formula Var) : (boundedEventualParents S I φ).Finite := by
  have hinj : Function.Injective (Local.predicate : Predicate Clock Var → Local Clock Var) :=
    fun _ _ h => Local.predicate.inj h
  exact (S.locals_finite.preimage hinj.injOn).subset (fun _ h => h.1)

def boundedAlwaysParents (S : Section3.StateForm Clock Var)
    (I : TimeInterval) (φ : Formula Var) : Set (Predicate Clock Var) :=
  {p | Local.predicate p ∈ S.locals ∧ ∃ c d b q, p = .bounded c d b q .always I φ}

theorem boundedAlwaysParents_finite (S : Section3.StateForm Clock Var)
    (I : TimeInterval) (φ : Formula Var) : (boundedAlwaysParents S I φ).Finite := by
  have hinj : Function.Injective (Local.predicate (Clock := Clock) (Var := Var)) :=
    fun _ _ h => Local.predicate.inj h
  exact (S.locals_finite.preimage hinj.injOn).subset (fun _ h => h.1)

def upperLocals (S : Section3.StateForm Clock Var) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var) : Set (Local Clock Var) :=
  S.locals ∩ upperKindSignature kind I φ

theorem upperLocals_finite (S : Section3.StateForm Clock Var) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var) : (upperLocals S kind I φ).Finite :=
  S.locals_finite.subset Set.inter_subset_left

def unboundedEventualLocals (S : Section3.StateForm Clock Var) (a : NNReal)
    (φ : Formula Var) : Set (Local Clock Var) := S.locals ∩ unboundedEventualSignature a φ

end STLTableau.Section4.Finiteness
