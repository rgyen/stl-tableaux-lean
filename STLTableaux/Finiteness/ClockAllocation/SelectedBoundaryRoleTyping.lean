import STLTableaux.Finiteness.Derivation.Selection.SelectedPathOrigins
import STLTableaux.Finiteness.Inventory.RoleTypedInventory

/-! Newly introduced strict boundary guards are typed by an ACTUAL eligible
local predicate in the `↑↓` form of the input. Finite history support alone is not used as
typing. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var Slot : Type*} [DecidableEq Clock] [Fintype Slot]

namespace InputOrigins
variable {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}
    {N : Section3.StateForm Clock Var}

/-- A strict comparison clock has an actual input left-role binding. -/
theorem strict_clock_role (O : InputOrigins σ P α k N)
    {τ : Slot→FiniteInventory.Triple Clock Var} {incoming : Equiv.Perm Clock}
    (frame : SlotFrame τ N incoming) (c : Clock) (hc : c∈O.strictClocks) :
    ∃s,frame.role c=some (s,0) := by
  obtain ⟨q,_,d,m,r,kind,I,φ,hq,_⟩ := hc
  have hp : Local.predicate (.bounded c d m r kind I φ)∈N.locals := hq ▸ q.property.1
  obtain ⟨s,_,_,hleft,_,_,_,_⟩ := frame.predicates _ hp
  exact ⟨s,hleft⟩

/-- The strict guard's zero constant is endpoint index zero of that slot's
actual family, for both bounded and unbounded intervals. -/
theorem strict_guard_typed (O : InputOrigins σ P α k N)
    {τ : Slot→FiniteInventory.Triple Clock Var} {incoming : Equiv.Perm Clock}
    (frame : SlotFrame τ N incoming) (g : Section3.Guard Clock)
    (hg : g∈strictBoundaryGuards O.strictClocks) :
    SlotFrame.GuardTyped τ frame.role g := by
  obtain ⟨c,hc,rfl⟩ := hg
  obtain ⟨s,hs⟩ := O.strict_clock_role frame c hc
  exact ⟨s,0,0,hs,by simp [FiniteInventory.endpoint]⟩
end InputOrigins

namespace SlotFrame
omit [DecidableEq Clock] [Fintype Slot] in
/-- Typing survives extension of the actual supported role graph. -/
theorem GuardTyped.mono {τ : Slot→FiniteInventory.Triple Clock Var}
    {role role' : ClockRoles Clock Slot} {g : Section3.Guard Clock}
    (h : GuardTyped τ role g)
    (he : ∀c s r,role c=some (s,r)→ role' c=some (s,r)) : GuardTyped τ role' g := by
  obtain ⟨s,r,j,hc,hj⟩ := h
  exact ⟨s,r,j,he _ _ _ hc,hj⟩
end SlotFrame

/-- Concrete strict-guard typing after retaining input role bindings in an
actual larger role map; no role is inferred from a mere clock-budget cover. -/
theorem InputOrigins.strict_guard_typed_extended
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}
    {N : Section3.StateForm Clock Var} (O : InputOrigins σ P α k N)
    {τ : Slot→FiniteInventory.Triple Clock Var} {incoming : Equiv.Perm Clock}
    (frame : SlotFrame τ N incoming) (role : ClockRoles Clock Slot)
    (he : ∀c s r,frame.role c=some (s,r)→ role c=some (s,r))
    (g : Section3.Guard Clock) (hg : g∈strictBoundaryGuards O.strictClocks) :
    SlotFrame.GuardTyped τ role g :=
  (O.strict_guard_typed frame g hg).mono he
end STLTableau.Section4.Finiteness
