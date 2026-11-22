import STLTableaux.Finiteness.Derivation.Branches.BranchBoundedSupport
import STLTableaux.Finiteness.Bounds.SelectedRootBudget

/-! A clock assignment for a single state. Each clock in the state's support
maps to one of three positions in a fixed slot. Clocks outside the support
have no assignment. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var Slot : Type*}

abbrev ClockRoles (Clock Slot : Type*) := Clock → Option (Slot × Fin 3)

/-- Partial injection whose domain is the set of clocks `A`. -/
structure RoleAllocation (A : Set Clock) where
  role : ClockRoles Clock Slot
  domain : ∀c, c∈A ↔ ∃s r,role c=some (s,r)
  injective : ∀c d s r,role c=some (s,r) → role d=some (s,r) → c=d

namespace SlotFrame

def PredicateTyped (τ : Slot → FiniteInventory.Triple Clock Var)
    (role : ClockRoles Clock Slot) : Predicate Clock Var → Prop
  | .plain _ => True
  | .upper c _ kind I φ => ∃s,role c=some (s,0) ∧
      kind=(τ s).kind ∧ I=(τ s).interval ∧ φ=(τ s).body
  | .bounded c d _ _ kind I φ => ∃s r,(r=1 ∨ r=2) ∧
      role c=some (s,0) ∧ role d=some (s,r) ∧
      kind=(τ s).kind ∧ I=(τ s).interval ∧ φ=(τ s).body

def GuardTyped (τ : Slot → FiniteInventory.Triple Clock Var)
    (role : ClockRoles Clock Slot) (g : Section3.Guard Clock) : Prop :=
  ∃s r j,role g.clock=some (s,r) ∧ g.bound=FiniteInventory.endpoint (τ s).interval j

def ResetTyped (τ : Slot → FiniteInventory.Triple Clock Var)
    (role : ClockRoles Clock Slot) (c : Clock) (a : NNReal) : Prop :=
  ∃s r j,role c=some (s,r) ∧ a=FiniteInventory.endpoint (τ s).interval j

noncomputable def occupied [Fintype Slot] (role : ClockRoles Clock Slot) : Finset Slot := by
  classical
  exact Finset.univ.filter (fun s => ∃c r,role c=some (s,r))

noncomputable def occupiedFamily [Fintype Slot] (τ : Slot → FiniteInventory.Triple Clock Var)
    (role : ClockRoles Clock Slot) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) : Finset Slot := by
  classical
  exact (occupied role).filter (fun s => (τ s).kind=kind ∧ (τ s).interval=I ∧ (τ s).body=φ)

end SlotFrame

/-- Input-only right uniqueness: full current output may temporarily contain
 both old and newly chosen right names. Retired guard-only slots are occupied
 whenever any of their supported names remains present. -/
structure SlotFrame [Fintype Slot] (τ : Slot → FiniteInventory.Triple Clock Var)
    (N : Section3.StateForm Clock Var) (incoming : Clock ≃ Clock) extends
    RoleAllocation (Slot := Slot) (Section3.TransitionForm.ofState N).allClocks where
  realizes : ∀c s r,role c=some (s,r) → incoming c=FiniteInventory.clockAt (τ s) r
  predicates : ∀p,Local.predicate p∈N.locals → SlotFrame.PredicateTyped τ role p
  guards : ∀g∈N.guards,SlotFrame.GuardTyped τ role g
  resets : ∀c a,N.resets.value c=some a → SlotFrame.ResetTyped τ role c a
  right_unique : ∀s,¬((∃c,role c=some (s,1)) ∧ (∃c,role c=some (s,2)))
  occupied_bound : ∀kind I φ,(SlotFrame.occupiedFamily τ role kind I φ).card≤temporalOriginCap I+2

end STLTableau.Section4.Finiteness
