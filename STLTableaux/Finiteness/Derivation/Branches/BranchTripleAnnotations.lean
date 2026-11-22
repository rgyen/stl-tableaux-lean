import STLTableaux.Finiteness.ClockAllocation.SelectedNextAnnotations
import STLTableaux.Finiteness.Derivation.Branches.RawBranchSupport
import STLTableaux.Finiteness.Inventory.FiniteInventory

/-! Local formula-specific annotation typing. This is a branch lemma, not a
 globally consistent slot allocation or a representative-path theorem. -/
namespace STLTableau.Section4.Finiteness
open Section3 Finiteness
variable {Clock Var : Type*}

namespace BranchTriple

def names (t : FiniteInventory.Triple Clock Var) : Set Clock := {t.left,t.right₀,t.right₁}

/-- A timed unclocked source opens the left role; clocked sources retain the
 family's left role and use one of its two right roles. -/
def SourceFits (t : FiniteInventory.Triple Clock Var) : Predicate Clock Var → Prop
  | .plain φ => φ=timedFormula t.kind t.interval t.body
  | .upper c _ kind I φ => c=t.left ∧ kind=t.kind ∧ I=t.interval ∧ φ=t.body
  | .bounded c d _ _ kind I φ =>
      c=t.left ∧ (d=t.right₀ ∨ d=t.right₁) ∧ kind=t.kind ∧ I=t.interval ∧ φ=t.body

def FreshRoleFits (t : FiniteInventory.Triple Clock Var) (p : Predicate Clock Var) (x : Clock) : Prop :=
  match p with
  | .plain _ => x=t.left
  | .upper .. | .bounded .. => x=t.right₀ ∨ x=t.right₁

theorem source_names {t : FiniteInventory.Triple Clock Var} {p : Predicate Clock Var}
    (h : SourceFits t p) : syntaxClocks (.predicate p)⊆names t := by
  cases p with
  | plain => exact Set.empty_subset _
  | upper c m kind I φ =>
      rcases h with ⟨rfl,_,_,_⟩
      simp [syntaxClocks,names]
  | bounded c d m q kind I φ =>
      rcases h with ⟨rfl,hd,_,_,_⟩
      rcases hd with rfl | rfl <;> simp [syntaxClocks,names,Set.insert_subset_iff]

theorem fresh_name {t : FiniteInventory.Triple Clock Var} {p : Predicate Clock Var} {x : Clock}
    (h : FreshRoleFits t p x) : x∈names t := by
  cases p <;> simp only [FreshRoleFits] at h
  · rw [h]; simp [names]
  all_goals rcases h with rfl | rfl <;> simp [names]

private theorem source_constants {t : FiniteInventory.Triple Clock Var} {p : Predicate Clock Var}
    (h : SourceFits t p) : branchConstants p ⊆ intervalClockConstants t.interval := by
  classical
  cases p with
  | plain φ =>
      intro a ha
      have he : a=0 := by simpa only [branchConstants,Finset.mem_singleton] using ha
      subst a
      cases t.interval <;> simp [intervalClockConstants]
  | upper c m kind I φ => rw [branchConstants,h.2.2.1]
  | bounded c d m q kind I φ => rw [branchConstants,h.2.2.2.1]

private theorem name_index {t : FiniteInventory.Triple Clock Var} {c : Clock} (h : c∈names t) :
    ∃i : Fin 3,c=FiniteInventory.clockAt t i := by
  rcases h with h | h | h
  · exact ⟨0,h⟩
  · exact ⟨1,h⟩
  · exact ⟨2,h⟩

private theorem constant_index {I : TimeInterval} {a : NNReal} (h : a∈intervalClockConstants I) :
    ∃i : Fin 3,a=FiniteInventory.endpoint I i := by
  classical
  cases I with
  | bounded I =>
      simp only [intervalClockConstants,Finset.mem_insert,Finset.mem_singleton] at h
      rcases h with h | h | h
      · exact ⟨0,h⟩
      · exact ⟨1,h⟩
      · exact ⟨2,h⟩
  | unbounded b =>
      simp only [intervalClockConstants,Finset.mem_insert,Finset.mem_singleton] at h
      rcases h with h | h
      · exact ⟨0,h⟩
      · exact ⟨1,h⟩

end BranchTriple

theorem RawGuardAt.clock_support {J : MixedJ Clock Var} {c : Clock} {a : NNReal}
    (h : RawGuardAt c a J) : c∈syntaxClocks J := by
  induction J with
  | terminal | marker | predicate => cases h
  | clock d r b => exact h.1
  | next J ih => exact ih h
  | reset R J ih => exact Or.inr (ih h)
  | conj J K ih ik =>
      rcases h with h | h
      · exact Or.inl (ih h)
      · exact Or.inr (ik h)

theorem RawResetAt.clock_support {J : MixedJ Clock Var} {c : Clock} {a : NNReal}
    (h : RawResetAt c a J) : c∈syntaxClocks J := by
  induction J with
  | terminal | marker | predicate | clock => cases h
  | next J ih => exact ih h
  | reset R J ih =>
      rcases h with h | h
      · exact Or.inl ⟨a,h⟩
      · exact Or.inr (ih h)
  | conj J K ih ik =>
      rcases h with h | h
      · exact Or.inl (ih h)
      · exact Or.inr (ik h)

variable [DecidableEq Clock]

/-- Actual source/fresh-role evidence yields simultaneous clock and numeric
 membership in ONE formula-specific triple, not a root-wide scalar pool. -/
theorem RawBranch.guard_triple_indices
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B)
    (t : FiniteInventory.Triple Clock Var) (hs : BranchTriple.SourceFits t p) (x : Clock)
    (hx : BranchTriple.FreshRoleFits t p x)
    (hr : resetNames B⊆syntaxClocks (.predicate p) ∪ {x})
    {c : Clock} {a : NNReal} (ha : RawGuardAt c a B) :
    ∃i j : Fin 3,c=FiniteInventory.clockAt t i ∧ a=FiniteInventory.endpoint t.interval j := by
  have hc := h.syntaxClocks_subset_source_union_singleton x hr ha.clock_support
  have hn : c∈BranchTriple.names t := by
    rcases hc with hc | hc
    · exact BranchTriple.source_names hs hc
    · have he : c=x := hc
      subst c
      exact BranchTriple.fresh_name hx
  obtain ⟨i,hi⟩ := BranchTriple.name_index hn
  obtain ⟨j,hj⟩ := BranchTriple.constant_index (BranchTriple.source_constants hs (h.guard_constant ha))
  exact ⟨i,j,hi,hj⟩

theorem RawBranch.reset_triple_indices
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B)
    (t : FiniteInventory.Triple Clock Var) (hs : BranchTriple.SourceFits t p) (x : Clock)
    (hx : BranchTriple.FreshRoleFits t p x)
    (hr : resetNames B⊆syntaxClocks (.predicate p) ∪ {x})
    {c : Clock} {a : NNReal} (ha : RawResetAt c a B) :
    ∃i j : Fin 3,c=FiniteInventory.clockAt t i ∧ a=FiniteInventory.endpoint t.interval j := by
  have hc := h.syntaxClocks_subset_source_union_singleton x hr ha.clock_support
  have hn : c∈BranchTriple.names t := by
    rcases hc with hc | hc
    · exact BranchTriple.source_names hs hc
    · have he : c=x := hc
      subst c
      exact BranchTriple.fresh_name hx
  obtain ⟨i,hi⟩ := BranchTriple.name_index hn
  obtain ⟨j,hj⟩ := BranchTriple.constant_index (BranchTriple.source_constants hs (h.reset_constant ha))
  exact ⟨i,j,hi,hj⟩

/-- The support bound is supplied by the actual selected choice, rather than
 left as an extra assumption on a constructed path. -/
theorem OrdinaryChoice.guard_triple_indices
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} (choice : OrdinaryChoice E owned)
    (t : FiniteInventory.Triple Clock Var) (hs : BranchTriple.SourceFits t choice.p)
    (hx : BranchTriple.FreshRoleFits t choice.p choice.x)
    {c : Clock} {a : NNReal} (ha : RawGuardAt c a choice.B) :
    ∃i j : Fin 3,c=FiniteInventory.clockAt t i ∧ a=FiniteInventory.endpoint t.interval j :=
  choice.branch.guard_triple_indices t hs choice.x hx choice.reset_support ha

theorem OrdinaryChoice.reset_triple_indices
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} (choice : OrdinaryChoice E owned)
    (t : FiniteInventory.Triple Clock Var) (hs : BranchTriple.SourceFits t choice.p)
    (hx : BranchTriple.FreshRoleFits t choice.p choice.x)
    {c : Clock} {a : NNReal} (ha : RawResetAt c a choice.B) :
    ∃i j : Fin 3,c=FiniteInventory.clockAt t i ∧ a=FiniteInventory.endpoint t.interval j :=
  choice.branch.reset_triple_indices t hs choice.x hx choice.reset_support ha

end STLTableau.Section4.Finiteness
