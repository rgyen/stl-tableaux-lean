import STLTableaux.Finiteness.Bounds.SelectedOriginCount
import STLTableaux.Finiteness.Inventory.StateSignatureConfinement
import STLTableaux.Finiteness.Inventory.RootFormulaInventory

/-! Bounds for the root formula, summed over its timed subformulas. These sums
do not depend on the size of the partition. Used in the proof of Lemma 4.36. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped BigOperators
variable {Clock Var : Type*} [DecidableEq Clock]

noncomputable def temporalOriginCap : TimeInterval → ℕ
  | .bounded I => 2*⌊I.upper/(I.upper-I.lower)⌋₊+7
  | .unbounded _ => 1

noncomputable def rootOriginBudget (root : Formula Var) : ℕ :=
  ∑ s ∈ Finiteness.rootTemporalSignatures root, temporalOriginCap s.2.1

noncomputable def rootStepBudget (root : Formula Var) : ℕ :=
  rootOriginBudget root + 2*(Finiteness.rootPlainFormulas root).card

/-- Actual input origins give a uniform total bounded-local count. Each local
is covered by a literal root temporal signature and that family's proved cap. -/
theorem InputOrigins.bounded_domain_card_root
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}
    {N : Section3.StateForm Clock Var} (O : InputOrigins σ P α k N)
    (root : Formula Var) (hN : Finiteness.StateFormulasBelow root N) :
    Fintype.card (BoundedLocal N) ≤ rootOriginBudget root := by
  classical
  let S := Finiteness.rootTemporalSignatures root
  let family := fun s : TemporalKind × TimeInterval × Formula Var => boundedFamily N s.1 s.2.1 s.2.2
  have hcover : (Finset.univ : Finset (BoundedLocal N)) ⊆ S.biUnion family := by
    intro q hq
    rcases q with ⟨p,hp,hb⟩
    cases p with
    | plain | upper => cases hb
    | bounded c d m r kind I φ =>
      apply Finset.mem_biUnion.mpr
      refine ⟨(kind,I,φ),?_,?_⟩
      · exact (Finiteness.state_signatures_confined_of_formulas_below root N hN).2 c d m r kind I φ hp
      · exact (mem_boundedFamily N kind I φ _).2 ⟨c,d,m,r,rfl⟩
  calc
    Fintype.card (BoundedLocal N) = (Finset.univ : Finset (BoundedLocal N)).card := (Finset.card_univ).symm
    _ ≤ (S.biUnion family).card := Finset.card_le_card hcover
    _ ≤ ∑ s ∈ S, (family s).card := Finset.card_biUnion_le
    _ ≤ ∑ s ∈ S, temporalOriginCap s.2.1 := by
      apply Finset.sum_le_sum
      intro s hs
      rcases s with ⟨kind,I,φ⟩
      cases I with
      | bounded I => exact O.boundedFamily_card_floor_bound kind I φ
      | unbounded a => exact O.unboundedFamily_card_le_one kind a φ
    _ = rootOriginBudget root := rfl
end STLTableau.Section4.Finiteness
