import STLTableaux.Finiteness.Derivation.Branches.BranchPlainOpening
import STLTableaux.Finiteness.Derivation.Branches.RawBranchNextOrigin

/-! Actual local temporal-family/left-right role preservation. These triples
 are branch-local and may reuse unused names; no global allocation is asserted. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

private theorem conjunct_support {B K : MixedJ Clock Var} (h : Conjunct B K) :
    syntaxClocks K⊆syntaxClocks B := by
  induction h with
  | here => exact Set.Subset.rfl
  | left h ih => exact ih.trans Set.subset_union_left
  | right h ih => exact ih.trans Set.subset_union_right

private theorem current_support {J : MixedJ Clock Var} {p : Predicate Clock Var}
    (h : p∈J.currentPredicates) : syntaxClocks (.predicate p)⊆syntaxClocks J := by
  induction J with
  | terminal | clock | marker | next => cases h
  | predicate q => have he : p=q := h; subst p; exact Set.Subset.rfl
  | reset R J ih => exact (ih h).trans Set.subset_union_right
  | conj J K ih ik =>
      rcases h with h | h
      · exact (ih h).trans Set.subset_union_left
      · exact (ik h).trans Set.subset_union_right

variable [DecidableEq Clock]

/-- An opening branch for an unclocked predicate introduces the `↑` form. Its
left clock is the fresh clock selected for the branch. -/
theorem OrdinaryChoice.exists_annotation_triple
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} (choice : OrdinaryChoice E owned) :
    syntaxClocks choice.B=∅ ∨ ∃t : FiniteInventory.Triple Clock Var,
      BranchTriple.SourceFits t choice.p ∧ BranchTriple.FreshRoleFits t choice.p choice.x := by
  cases hp : choice.p with
  | plain φ =>
      rcases choice.branch.plain_opening_or_empty ⟨φ,hp⟩ with he | ⟨c,m,kind,I,ψ,hsource,hbody⟩
      · exact Or.inl he
      · have hc : c=choice.x := by
          have hh := choice.branch.syntaxClocks_subset_source_union_singleton choice.x choice.reset_support
          have hm : c∈syntaxClocks choice.B := by rw [hbody]; simp [syntaxClocks]
          have hs := hh hm
          simpa only [hp,syntaxClocks,Set.empty_union,Set.mem_singleton_iff] using hs
        refine Or.inr ⟨⟨choice.x,choice.x,choice.x,kind,I,ψ⟩,?_,?_⟩
        · exact Predicate.plain.inj (hp.symm.trans hsource)
        · rfl
  | upper c m kind I φ =>
      refine Or.inr ⟨⟨c,choice.x,choice.x,kind,I,φ⟩,?_,?_⟩ <;>
        simp [BranchTriple.SourceFits,BranchTriple.FreshRoleFits]
  | bounded c d m q kind I φ =>
      refine Or.inr ⟨⟨c,d,choice.x,kind,I,φ⟩,?_,?_⟩ <;>
        simp [BranchTriple.SourceFits,BranchTriple.FreshRoleFits]

/-- Clocked literal next descendants retain the actual source's family and
 left role. Their right name is one of this family's two available right roles. -/
theorem RawBranch.next_bounded_triple
    {p : Predicate Clock Var} {B N : MixedJ Clock Var} (h : RawBranch p B)
    (hNext : Conjunct B (.next N))
    (t : FiniteInventory.Triple Clock Var) (hs : BranchTriple.SourceFits t p)
    (x : Clock) (hx : BranchTriple.FreshRoleFits t p x)
    (hr : resetNames B⊆syntaxClocks (.predicate p) ∪ {x})
    (c d : Clock) (m q : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hq : Predicate.bounded c d m q kind I φ∈N.currentPredicates) :
    BranchTriple.SourceFits t (.bounded c d m q kind I φ) := by
  have horigin := h.next_bounded_source hNext c d m q kind I φ hq
  have hf : c=t.left ∧ kind=t.kind ∧ I=t.interval ∧ φ=t.body ∧ c≠d := by
    rcases horigin with ⟨b,hp,hcd⟩ | ⟨b,hp,hcd⟩
    · rw [hp] at hs
      exact ⟨hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,hcd⟩
    · rw [hp] at hs
      exact ⟨hs.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2,hcd⟩
  have hdN : d∈syntaxClocks N := current_support hq (by simp [syntaxClocks])
  have hdB : d∈syntaxClocks B := conjunct_support hNext hdN
  have hd : d∈BranchTriple.names t := by
    rcases h.syntaxClocks_subset_source_union_singleton x hr hdB with hd | hd
    · exact BranchTriple.source_names hs hd
    · have he : d=x := hd
      subst d
      exact BranchTriple.fresh_name hx
  have hright : d=t.right₀ ∨ d=t.right₁ := by
    rcases hd with hd | hd | hd
    · exact False.elim (hf.2.2.2.2 (hf.1.trans hd.symm))
    · exact Or.inl hd
    · exact Or.inr hd
  exact ⟨hf.1,hright,hf.2.1,hf.2.2.1,hf.2.2.2.1⟩

/-- The old right name is absent from the entire actual upper raw branch,
 including every next guard/reset binding, when it differs from left/newright. -/
theorem OrdinaryChoice.upper_old_right_absent
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} (choice : OrdinaryChoice E owned)
    {c d : Clock} {m : Marker} {kind : TemporalKind} {I : TimeInterval} {φ : Formula Var}
    (hp : choice.p=.upper c m kind I φ) (hdc : d≠c) (hdW : d∈W) :
    d∉syntaxClocks choice.B := by
  intro hd
  have hh := choice.branch.syntaxClocks_subset_source_union_singleton choice.x choice.reset_support hd
  rw [hp] at hh
  rcases hh with hdc' | hdx
  · exact hdc hdc'
  · have he : d=choice.x := hdx
    exact choice.fresh_name (he ▸ hdW)

/-- In the actual optional fusion, the old right name is already reserved in
 the incoming budget. Freshness therefore discharges the absence condition. -/
theorem BoundaryChoice.forced_upper_old_right_absent
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} (choice : BoundaryChoice E owned false)
    (upper : OrdinaryChoice E choice.child)
    (forced : upper.p=.upper choice.c choice.m choice.kind choice.I choice.phi) :
    choice.d∉syntaxClocks upper.B := by
  have hl : Local.predicate (.bounded choice.c choice.d choice.m (Marker.complement choice.ell)
      choice.kind choice.I choice.phi)∈owned.locals := by rw [choice.split]; simp
  have hd : choice.d∈syntaxClocks owned.canonical :=
    canonical_local_support owned.shape hl (by simp [Local.toJudgement,syntaxClocks])
  have hdW : choice.d∈W := owned.covers_input (Or.inl (Or.inr hd))
  exact upper.upper_old_right_absent forced choice.frozen.distinct.symm hdW

end STLTableau.Section4.Finiteness
