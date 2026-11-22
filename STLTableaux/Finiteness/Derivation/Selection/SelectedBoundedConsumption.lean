import STLTableaux.Finiteness.Derivation.Selection.SelectedPlainConsumption
import STLTableaux.Finiteness.Derivation.Branches.RawBranchCurrentShape

/-! Actual `↑↓` source consumption follows removal from the pending spine;
ordinary branches cannot regenerate current `↑↓` sources. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

private theorem bounded_not_raw {p q : Predicate Clock Var} {B : MixedJ Clock Var}
    (h : RawBranch p B) (hb : IsBoundedPredicate q) : q ∉ B.currentPredicates := by
  cases q with
  | bounded c d m ℓ kind I φ => exact h.no_current_bounded c d m ℓ kind I φ
  | plain | upper => cases hb

omit [DecidableEq Clock] in
private theorem bounded_not_upper {q : Predicate Clock Var} (hb : IsBoundedPredicate q)
    (c : Clock) (m : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    q ≠ .upper c m kind I φ := by cases q <;> simp_all [IsBoundedPredicate]

/-- Every boundary-consumed `↑↓` source was already present in the original
owned input of this SAME tree. Current branch descendants cannot fabricate it. -/
theorem SelectedTree.boundary_consumed_origin
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    {q : Predicate Clock Var} {required : Bool} (hq : (q,required) ∈ T.boundaryConsumed) :
    IsBoundedPredicate q ∧ q ∈ E ∧ Local.predicate q ∈ owned.locals := by
  induction T with
  | zero => cases hq
  | ordinary owned choice tail ih =>
    obtain ⟨hb,he,hm⟩ := ih hq
    rcases (ordinary_child_current owned choice q).1 hm with hnew | hold
    · exact False.elim (bounded_not_raw choice.branch hb hnew)
    · exact ⟨hb,he,ordinary_rest_subset owned choice hold⟩
  | required owned choice tail ih =>
    rcases List.mem_cons.mp hq with heq | ht
    · cases heq
      exact ⟨trivial,choice.eligible,by rw [choice.split]; simp⟩
    · obtain ⟨hb,he,hm⟩ := ih ht
      rcases (boundary_child_current owned choice q).1 hm with hu | hold
      · exact False.elim (bounded_not_upper hb _ _ _ _ _ hu)
      · exact ⟨hb,he,boundary_rest_subset owned choice hold⟩
  | optional owned choice upper forced tail ih =>
    rcases List.mem_cons.mp hq with heq | ht
    · cases heq
      exact ⟨trivial,choice.eligible,by rw [choice.split]; simp⟩
    · obtain ⟨hb,he,hm⟩ := ih ht
      rcases (ordinary_child_current choice.child upper q).1 hm with hnew | hold
      · exact False.elim (bounded_not_raw upper.branch hb hnew)
      · have hm := ordinary_rest_subset choice.child upper hold
        rcases (boundary_child_current owned choice q).1 hm with hu | hold
        · exact False.elim (bounded_not_upper hb _ _ _ _ _ hu)
        · exact ⟨hb,he,boundary_rest_subset owned choice hold⟩

private theorem boundary_source_absent
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) {required : Bool} (choice : BoundaryChoice E owned required) :
    Local.predicate (.bounded choice.c choice.d choice.m (Marker.complement choice.ell)
      choice.kind choice.I choice.phi) ∉ choice.child.locals := by
  intro hm
  rcases (boundary_child_current owned choice _).1 hm with he | hr
  · cases he
  · have hn : (Local.predicate (.bounded choice.c choice.d choice.m (Marker.complement choice.ell)
        choice.kind choice.I choice.phi) :: (choice.left++choice.right)).Nodup :=
      List.perm_middle.nodup_iff.mp (choice.split ▸ owned.locals_nodup)
    apply (List.nodup_cons.mp hn).1
    exact choice.selection.mem_iff.mpr (by cases required <;> simp [hr])

/-- A fixed eligible `↑↓` source can be boundary-consumed only once. -/
theorem SelectedTree.boundary_sources_nodup
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) : (T.boundaryConsumed.map Prod.fst).Nodup := by
  induction T with
  | zero => exact List.nodup_nil
  | ordinary owned choice tail ih => exact ih
  | required owned choice tail ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_,ih⟩
    intro hm
    obtain ⟨pair,hpair,he⟩ := List.mem_map.mp hm
    rcases pair with ⟨q,b⟩
    change q = _ at he
    subst q
    exact boundary_source_absent owned choice (tail.boundary_consumed_origin hpair).2.2
  | optional owned choice upper forced tail ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_,ih⟩
    intro hm
    obtain ⟨pair,hpair,he⟩ := List.mem_map.mp hm
    rcases pair with ⟨q,b⟩
    change q = _ at he
    subst q
    have h := (tail.boundary_consumed_origin hpair).2.2
    rcases (ordinary_child_current choice.child upper _).1 h with hnew | hold
    · exact upper.branch.no_current_bounded _ _ _ _ _ _ _ hnew
    · exact boundary_source_absent owned choice (ordinary_rest_subset choice.child upper hold)
end STLTableau.Section4.Finiteness
