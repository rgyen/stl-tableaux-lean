import STLTableaux.Finiteness.Bounds.TemporalLocalClockBudget
import STLTableaux.Finiteness.Inventory.StateSignatureConfinement
import STLTableaux.Finiteness.Inventory.RootFiniteEventualSignatures
import STLTableaux.Finiteness.Inventory.RootFiniteAlwaysSignatures
import STLTableaux.Finiteness.Inventory.RootUnboundedEventualSignatures

/-! Root temporal caps and state-level local-clock budget; no path selection. -/
namespace STLTableau.Section4.Finiteness
open Section3 TemporalLocalClockBudget
variable {Clock Var : Type*} [DecidableEq Clock]

noncomputable def boundedTemporalCap : TemporalKind × TimeInterval × Formula Var → ℕ
  | (.eventually, .bounded I, _) => ⌈I.upper / (I.upper - I.lower)⌉₊ + 2
  | (.always, .bounded I, _) => ⌈I.upper / (I.upper - I.lower)⌉₊ + 1
  | (.eventually, .unbounded _, _) => 1
  | (.always, .unbounded _, _) => 0

noncomputable def rootLocalClockBudget (root : Formula Var) : ℕ :=
  ∑ s ∈ rootTemporalSignatures root, (1 + 2 * boundedTemporalCap s)

/-- All concrete label caps, without introducing clock-count assumptions. -/
def StateTemporalCaps (root : Formula Var) (S : Section3.StateForm Clock Var) : Prop :=
  (∀ s ∈ rootFiniteEventualSignatures root,
    (boundedEventualParents S s.1 s.2).ncard ≤ ⌈s.1.upper / (s.1.upper - s.1.lower)⌉₊ + 2) ∧
  (∀ s ∈ rootFiniteAlwaysSignatures root,
    (boundedAlwaysParents S (.bounded s.1) s.2).ncard ≤
      ⌈s.1.upper / (s.1.upper - s.1.lower)⌉₊ + 1) ∧
  (∀ s ∈ rootTemporalSignatures root, (upperLocals S s.1 s.2.1 s.2.2).ncard ≤ 1) ∧
  (∀ a φ, (boundedAlwaysParents S (.unbounded a) φ).ncard ≤ 0) ∧
  ∀ s ∈ rootUnboundedEventualSignatures root, (unboundedEventualLocals S s.1 s.2).ncard ≤ 1

theorem root_state_local_clock_budget (root : Formula Var) (S : Section3.StateForm Clock Var)
    (hc : StateSignaturesConfined root S) (h : StateTemporalCaps root S) :
    (stateLocalClockNames S).card ≤ rootLocalClockBudget root := by
  apply stateLocalClockNames_card_le_sum S (rootTemporalSignatures root) (fun _ => 1)
    boundedTemporalCap hc.1 hc.2 h.2.2.1
  intro s hs
  obtain ⟨kind, I, φ⟩ := s
  cases kind with
  | always =>
    cases I with
    | bounded I =>
      rw [boundedLocals_always_ncard]
      exact h.2.1 (I, φ) ((mem_rootFiniteAlwaysSignatures_iff root I φ).mpr
        ((mem_rootTemporalSignatures_iff root .always (.bounded I) φ).mp hs))
    | unbounded a =>
      rw [boundedLocals_always_ncard]
      exact h.2.2.2.1 a φ
  | eventually =>
    cases I with
    | bounded I =>
      rw [boundedLocals_eventual_ncard]
      exact h.1 (I, φ) ((mem_rootFiniteEventualSignatures_iff root I φ).mpr
        ((mem_rootTemporalSignatures_iff root .eventually (.bounded I) φ).mp hs))
    | unbounded a =>
      rw [boundedLocals_unbounded_eventual_eq]
      exact h.2.2.2.2 (a, φ) ((mem_rootUnboundedEventualSignatures_iff root a φ).mpr hs)

end STLTableau.Section4.Finiteness
