import STLTableaux.Finiteness.Derivation.Selection.SelectedBoundedConsumption

/-! Ordinary bounded expansions in the SAME actual raw ledger: source origin
and no repetition. Boundary-only consumption is a separate ledger. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

def RawLedgerEntry.boundedSource (entry : RawLedgerEntry (Clock := Clock) (Var := Var)) : Option (Predicate Clock Var) :=
  match entry.source with
  | p@(.bounded _ _ _ _ _ _ _) => some p
  | _ => none

private theorem not_raw_bounded {p q : Predicate Clock Var} {B : MixedJ Clock Var}
    (h : RawBranch p B) (hb : IsBoundedPredicate q) : q ∉ B.currentPredicates := by
  cases q with
  | bounded c d m ℓ kind I φ => exact h.no_current_bounded c d m ℓ kind I φ
  | plain | upper => cases hb

omit [DecidableEq Clock] in
private theorem not_upper_bounded {q : Predicate Clock Var} (hb : IsBoundedPredicate q)
    (c : Clock) (m : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    q ≠ .upper c m kind I φ := by cases q <;> simp_all [IsBoundedPredicate]

/-- Every bounded raw-ledger source was an actual original pending source. -/
theorem SelectedTree.bounded_ledger_origin
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    {entry : RawLedgerEntry (Clock := Clock) (Var := Var)}
    (he : entry ∈ T.rawLedger) (hb : IsBoundedPredicate entry.source) :
    Local.predicate entry.source ∈ owned.locals := by
  induction T with
  | zero => cases he
  | ordinary owned choice tail ih =>
    rcases List.mem_cons.mp he with rfl | ht
    · rw [choice.split]; simp
    · have hm := ih ht
      rcases (ordinary_child_current owned choice _).1 hm with hnew | hold
      · exact False.elim (not_raw_bounded choice.branch hb hnew)
      · exact ordinary_rest_subset owned choice hold
  | required owned choice tail ih =>
    have hm := ih he
    rcases (boundary_child_current owned choice _).1 hm with hu | hold
    · exact False.elim (not_upper_bounded hb _ _ _ _ _ hu)
    · exact boundary_rest_subset owned choice hold
  | optional owned choice upper forced tail ih =>
    rcases List.mem_cons.mp he with rfl | ht
    · simp only [forced,IsBoundedPredicate] at hb
    · have hm := ih ht
      rcases (ordinary_child_current choice.child upper _).1 hm with hnew | hold
      · exact False.elim (not_raw_bounded upper.branch hb hnew)
      · rcases (boundary_child_current owned choice _).1
          (ordinary_rest_subset choice.child upper hold) with hu | hold
        · exact False.elim (not_upper_bounded hb _ _ _ _ _ hu)
        · exact boundary_rest_subset owned choice hold

private theorem bounded_projection_member
    (ledger : List (RawLedgerEntry (Clock := Clock) (Var := Var))) {q : Predicate Clock Var}
    (hq : q ∈ ledger.filterMap RawLedgerEntry.boundedSource) :
    ∃ entry ∈ ledger, entry.source = q ∧ IsBoundedPredicate q := by
  obtain ⟨entry,he,hq⟩ := List.mem_filterMap.mp hq
  cases hs : entry.source with
  | plain | upper => simp only [RawLedgerEntry.boundedSource,hs] at hq; cases hq
  | bounded c d m ℓ kind I φ =>
    have hEq : Predicate.bounded c d m ℓ kind I φ = q := by
      simpa only [RawLedgerEntry.boundedSource,hs,Option.some.injEq] using hq
    exact ⟨entry,he,hs.trans hEq,hEq ▸ trivial⟩

/-- The actual ordinary `↑↓` source projection contains no repeated source. -/
theorem SelectedTree.bounded_ledger_nodup
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) : (T.rawLedger.filterMap RawLedgerEntry.boundedSource).Nodup := by
  induction T with
  | zero => exact List.nodup_nil
  | ordinary owned choice tail ih =>
    simp only [SelectedTree.rawLedger,List.filterMap_cons,RawLedgerEntry.boundedSource]
    cases hp : choice.p with
    | plain => exact ih
    | upper => exact ih
    | bounded c d m ℓ kind I φ =>
      apply List.nodup_cons.mpr
      refine ⟨?_,ih⟩
      intro hq
      obtain ⟨entry,he,hs,hb⟩ := bounded_projection_member _ hq
      have hm := tail.bounded_ledger_origin he (hs ▸ hb)
      rw [hs] at hm
      rcases (ordinary_child_current owned choice _).1 hm with hnew | hold
      · exact choice.branch.no_current_bounded c d m ℓ kind I φ hnew
      · have hn : (Local.predicate choice.p :: (choice.left++choice.right)).Nodup :=
          List.perm_middle.nodup_iff.mp (choice.split ▸ owned.locals_nodup)
        exact (List.nodup_cons.mp hn).1 (hp ▸ hold)
  | required owned choice tail ih => exact ih
  | optional owned choice upper forced tail ih =>
    simp only [SelectedTree.rawLedger,List.filterMap_cons,RawLedgerEntry.boundedSource,forced]
    exact ih
end STLTableau.Section4.Finiteness
