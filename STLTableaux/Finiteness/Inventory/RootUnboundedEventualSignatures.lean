import STLTableaux.Finiteness.Inventory.RootTemporalSignatures

/-! The unbounded-eventual subinventory is an exact projection of the
root's finite temporal-signature inventory, not a path-confinement premise. -/
namespace STLTableau.Section4.Finiteness
open scoped STL
variable {Var : Type*}

noncomputable def rootUnboundedEventualSignatures (root : Formula Var) :
    Finset (NNReal × Formula Var) := by
  classical
  exact (rootTemporalSignatures root).biUnion (fun s =>
    match s with
    | (.eventually,.unbounded a,φ) => {(a,φ)}
    | _ => ∅)

theorem mem_rootUnboundedEventualSignatures_iff
    (root : Formula Var) (a : NNReal) (φ : Formula Var) :
    (a,φ) ∈ rootUnboundedEventualSignatures root ↔
      (.eventually,.unbounded a,φ) ∈ rootTemporalSignatures root := by
  classical
  constructor
  · intro hm
    obtain ⟨⟨kind,I,ψ⟩,hs,hm⟩ := Finset.mem_biUnion.mp hm
    cases kind <;> cases I <;> simp_all
  · intro hm
    apply Finset.mem_biUnion.mpr
    exact ⟨(.eventually,.unbounded a,φ),hm,by simp⟩

theorem mem_rootUnboundedEventualSignatures_formula_iff
    (root : Formula Var) (a : NNReal) (φ : Formula Var) :
    (a,φ) ∈ rootUnboundedEventualSignatures root ↔
      Formula.eventually (.unbounded a) φ ≼ root := by
  rw [mem_rootUnboundedEventualSignatures_iff,mem_rootTemporalSignatures_iff]
  rfl

end STLTableau.Section4.Finiteness
