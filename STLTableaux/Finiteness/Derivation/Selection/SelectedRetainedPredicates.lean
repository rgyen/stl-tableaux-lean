import STLTableaux.Finiteness.Derivation.Selection.SelectedLedger

/-! Exact nonatomic retained labels of the SAME selected tree. Boundary-consumed
sources are not retained; actual ordinary raw sources are. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

omit [DecidableEq Clock] in
private theorem guard_current_empty (G : List (Guard Clock)) {A : MixedJ Clock Var}
    (hg : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) = some A) :
    A.currentPredicates = ∅ := by
  obtain ⟨S,hS,hr,hl⟩ := CanonicalSafety.guards_safe G A hg
  ext p
  rw [← Section3.TransitionForm.normalize_currentPredicates A hS.normalizes p]
  simp only [Section3.TransitionForm.ofState,hl,Set.mem_empty_iff_false]

omit [DecidableEq Clock] in
private theorem outside_current (G : List (Guard Clock)) (R : ClockResetSet Clock) (K : MixedJ Clock Var) :
    (outsidePending G R K).currentPredicates = K.currentPredicates := by
  cases hg : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
  | none => simp only [outsidePending,hg,Section3.Judgement.currentPredicates]
  | some A =>
    simp only [outsidePending,hg,Section3.Judgement.currentPredicates,guard_current_empty G hg,Set.empty_union]

omit [DecidableEq Clock] in
private theorem current_atomic_of_zero (J : MixedJ Clock Var) (hz : pendingWeight J = 0)
    (p : Predicate Clock Var) (hp : p ∈ J.currentPredicates) : p.IsAtomic := by
  classical
  induction J with
  | predicate q =>
    have he : p = q := hp
    subst p
    by_contra hn
    have hh : 3 ^ q.complexity = 0 := by simpa only [pendingWeight,if_neg hn] using hz
    exact (Nat.ne_of_gt (pow_pos (by omega) _)) hh
  | conj J K ih ik =>
    change pendingWeight J + pendingWeight K = 0 at hz
    rcases hp with hp | hp
    · exact ih (Nat.add_eq_zero_iff.mp hz).1 hp
    · exact ik (Nat.add_eq_zero_iff.mp hz).2 hp
  | reset R J ih => exact ih hz hp
  | next | terminal | marker | clock => cases hp

/-- A nonatomic predicate labels the full selected output exactly when it is
an actual raw-expansion source in this SAME tree's ledger. -/
theorem SelectedTree.retained_nonatomic_iff
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) (p : Predicate Clock Var) (hp : ¬p.IsAtomic) :
    p ∈ H.currentPredicates ↔ ∃ entry ∈ T.rawLedger, entry.source = p := by
  induction T with
  | zero owned hz =>
    simp only [SelectedTree.rawLedger,List.not_mem_nil,false_and,exists_false,iff_false]
    exact fun h => hp (current_atomic_of_zero _ hz p h)
  | ordinary owned choice tail ih =>
    rw [outside_current]
    simp only [Section3.Judgement.currentPredicates,Set.mem_union,Set.mem_singleton_iff,ih,
      SelectedTree.rawLedger,List.mem_cons,or_and_right,exists_or,exists_eq_left]
    tauto
  | required owned choice tail ih =>
    rw [outside_current]
    exact ih
  | optional owned choice upper forced tail ih =>
    rw [outside_current,outside_current]
    simp only [Section3.Judgement.currentPredicates,Set.mem_union,Set.mem_singleton_iff,ih,
      SelectedTree.rawLedger,List.mem_cons,or_and_right,exists_or,exists_eq_left]
    tauto

/-- The identical fact in any actual safe normal form of the full output. -/
theorem SelectedTree.normalized_retained_nonatomic_iff
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    {F : Section3.TransitionForm Clock Var} (hF : SafeNormalization H F)
    (p : Predicate Clock Var) (hp : ¬p.IsAtomic) :
    Local.predicate p ∈ F.current.locals ↔ ∃ entry ∈ T.rawLedger, entry.source = p :=
  (Section3.TransitionForm.normalize_currentPredicates H hF.normalizes p).trans
    (T.retained_nonatomic_iff p hp)
end STLTableau.Section4.Finiteness
