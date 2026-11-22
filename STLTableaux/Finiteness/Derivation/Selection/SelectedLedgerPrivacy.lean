import STLTableaux.Finiteness.Derivation.Selection.SelectedPlainConsumption
import STLTableaux.Finiteness.Derivation.Branches.RawBranchSupport

/-! Distinct actual selected clocked branch events have private source clocks.
The boundary source is replaced, not retained as another ledger event. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

omit [DecidableEq Clock] in
private theorem local_budget {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (p : Predicate Clock Var) (hp : Local.predicate p∈owned.locals) :
    syntaxClocks (.predicate p)⊆W := by
  intro c hc
  exact owned.covers_input (Or.inl (Or.inr (canonical_local_support owned.shape hp hc)))

omit [DecidableEq Clock] in
private theorem protected_source {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W A : Set Clock}
    {owned : OwnedPending J R W} (h : protectedActive owned A)
    (p : Predicate Clock Var) (hp : Local.predicate p∈owned.locals) :
    Disjoint (syntaxClocks (.predicate p)) A := by
  apply Set.disjoint_left.mpr
  intro c hc ha
  exact Set.disjoint_left.mp h ⟨p,hp,hc⟩ ha

private theorem ordinary_protected {E : Set (Predicate Clock Var)}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W A : Set Clock}
    (owned : OwnedPending J R W) (choice : OrdinaryChoice E owned)
    (hA : A⊆W) (hp : protectedActive owned A) : protectedActive choice.child A := by
  apply Set.disjoint_left.mpr
  rintro c ⟨q,hq,hc⟩ ha
  rcases (ordinary_child_current owned choice q).1 hq with hn | hr
  · have hx : c=choice.x := choice.branch.current_child_subset_singleton choice.x choice.reset_support q hn hc
    subst c
    exact choice.fresh_name (hA ha)
  · exact Set.disjoint_left.mp hp ⟨q,ordinary_rest_subset owned choice hr,hc⟩ ha

private theorem boundary_protected {E : Set (Predicate Clock Var)}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W A : Set Clock}
    (owned : OwnedPending J R W) {required : Bool} (choice : BoundaryChoice E owned required)
    (hp : protectedActive owned A) : protectedActive choice.child A := by
  apply Set.disjoint_left.mpr
  rintro c ⟨q,hq,hc⟩ ha
  rcases (boundary_child_current owned choice q).1 hq with hu | hr
  · subst q
    have hleft : c=choice.c := hc
    subst c
    apply Set.disjoint_left.mp hp
    · refine ⟨.bounded choice.c choice.d choice.m (Marker.complement choice.ell) choice.kind choice.I choice.phi,?_,?_⟩
      · rw [choice.split]; simp
      · exact Or.inl rfl
    · exact ha
  · exact Set.disjoint_left.mp hp ⟨q,boundary_rest_subset owned choice hr,hc⟩ ha

/-- Protected incoming source clocks cannot reappear in a later ledger source. -/
theorem SelectedTree.ledger_sources_protected
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) (A : Set Clock) (hA : A⊆W)
    (hp : protectedActive owned A) :
    ∀e∈T.rawLedger,Disjoint (syntaxClocks (.predicate e.source)) A := by
  induction T with
  | zero => simp [SelectedTree.rawLedger]
  | ordinary owned choice tail ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | ht
    · apply protected_source hp
      rw [choice.split]; simp
    · exact ih (hA.trans choice.grows) (ordinary_protected owned choice hA hp) e ht
  | required owned choice tail ih =>
    exact ih hA (boundary_protected owned choice hp)
  | optional owned choice upper forced tail ih =>
    have hb := boundary_protected owned choice hp
    intro e he
    rcases List.mem_cons.mp he with rfl | ht
    · apply protected_source hb
      rw [upper.split]; simp
    · exact ih (hA.trans upper.grows) (ordinary_protected choice.child upper hA hb) e ht

private theorem ordinary_after_source {E : Set (Predicate Clock Var)}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (choice : OrdinaryChoice E owned) :
    protectedActive choice.child (syntaxClocks (.predicate choice.p)) := by
  have hr := remaining_active_protected owned ∅ (by simp [protectedActive]) choice.p choice.left choice.right choice.split
  apply Set.disjoint_left.mpr
  rintro c ⟨q,hq,hc⟩ hp
  rcases (ordinary_child_current owned choice q).1 hq with hn | hold
  · have hx : c=choice.x := choice.branch.current_child_subset_singleton choice.x choice.reset_support q hn hc
    subst c
    apply choice.fresh_name
    apply local_budget owned choice.p
    · rw [choice.split]; simp
    · exact hp
  · exact Set.disjoint_left.mp hr ⟨q,hold,hc⟩ (Or.inr hp)

/-- Pairwise privacy of ACTUAL raw-ledger source occurrences, including forced
upper events. No event-uniqueness or owner-assignment hypothesis is used. -/
theorem SelectedTree.rawLedger_sources_pairwise_disjoint
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) :
    T.rawLedger.Pairwise (fun e f=>Disjoint (syntaxClocks (.predicate e.source)) (syntaxClocks (.predicate f.source))) := by
  induction T with
  | zero => exact List.Pairwise.nil
  | ordinary owned choice tail ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih⟩
    intro e he
    have hA : syntaxClocks (.predicate choice.p)⊆_ := local_budget owned choice.p (by rw [choice.split];simp)
    exact (tail.ledger_sources_protected _ (hA.trans choice.grows) (ordinary_after_source owned choice) e he).symm
  | required owned choice tail ih => exact ih
  | optional owned choice upper forced tail ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih⟩
    intro e he
    have hA : syntaxClocks (.predicate upper.p)⊆_ := local_budget choice.child upper.p (by rw [upper.split];simp)
    exact (tail.ledger_sources_protected _ (hA.trans upper.grows) (ordinary_after_source choice.child upper) e he).symm
def RawLedgerEntry.leftClock (e : RawLedgerEntry (Clock := Clock) (Var := Var)) : Option Clock :=
  match e.source with | .plain _=>none | .upper c ..=>some c | .bounded c ..=>some c

private theorem leftClock_support (e : RawLedgerEntry (Clock := Clock) (Var := Var))
    (c : Clock) (hc : e.leftClock=some c) : c∈syntaxClocks (.predicate e.source) := by
  cases hs : e.source with
  | plain φ => simp [RawLedgerEntry.leftClock,hs] at hc
  | upper d m kind I φ =>
    have he : d=c := by simpa [RawLedgerEntry.leftClock,hs] using hc
    simp [syntaxClocks,he]
  | bounded d r m q kind I φ =>
    have he : d=c := by simpa [RawLedgerEntry.leftClock,hs] using hc
    simp [syntaxClocks,he]

private theorem leftClock_nodup
    (L : List (RawLedgerEntry (Clock := Clock) (Var := Var)))
    (hp : L.Pairwise (fun e f=>Disjoint (syntaxClocks (.predicate e.source)) (syntaxClocks (.predicate f.source)))) :
    (L.filterMap RawLedgerEntry.leftClock).Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons e L ih =>
    obtain ⟨hh,ht⟩ := List.pairwise_cons.mp hp
    simp only [List.filterMap_cons]
    cases hc : e.leftClock with
    | none => exact ih ht
    | some c =>
      apply List.nodup_cons.mpr
      refine ⟨?_,ih ht⟩
      intro hm
      obtain ⟨f,hf,hfc⟩ := List.mem_filterMap.mp hm
      exact Set.disjoint_left.mp (hh f hf) (leftClock_support e c hc) (leftClock_support f c hfc)

/-- Actual clocked event occurrences have distinct left clocks. -/
theorem SelectedTree.rawLedger_leftClocks_nodup
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) :
    (T.rawLedger.filterMap RawLedgerEntry.leftClock).Nodup :=
  leftClock_nodup _ T.rawLedger_sources_pairwise_disjoint
private theorem same_left_of_pairwise
    (L : List (RawLedgerEntry (Clock := Clock) (Var := Var)))
    (hp : L.Pairwise (fun e f=>Disjoint (syntaxClocks (.predicate e.source)) (syntaxClocks (.predicate f.source))))
    (e f : RawLedgerEntry (Clock := Clock) (Var := Var)) (c : Clock)
    (he : e∈L) (hf : f∈L) (hc : e.leftClock=some c) (hd : f.leftClock=some c) : e=f := by
  induction L with
  | nil => cases he
  | cons a L ih =>
    obtain ⟨hh,ht⟩ := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp he with heq | heTail
    · rcases List.mem_cons.mp hf with hfq | hfTail
      · exact heq.trans hfq.symm
      · exact False.elim (Set.disjoint_left.mp (hh f hfTail)
          (leftClock_support a c (heq ▸ hc)) (leftClock_support f c hd))
    · rcases List.mem_cons.mp hf with hfq | hfTail
      · exact False.elim (Set.disjoint_left.mp (hh e heTail)
          (leftClock_support a c (hfq ▸ hd)) (leftClock_support e c hc))
      · exact ih ht heTail hfTail

/-- Two actual clocked ledger events with the same left clock are identical. -/
theorem SelectedTree.rawLedger_same_left_unique
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    (e f : RawLedgerEntry (Clock := Clock) (Var := Var)) (c : Clock)
    (he : e∈T.rawLedger) (hf : f∈T.rawLedger)
    (hc : e.leftClock=some c) (hd : f.leftClock=some c) : e=f :=
  same_left_of_pairwise _ T.rawLedger_sources_pairwise_disjoint e f c he hf hc hd
end STLTableau.Section4.Finiteness
