import STLTableaux.Finiteness.Derivation.Selection.SelectedRealization
import STLTableaux.Finiteness.Derivation.CanonicalResetMap

/-! On the clocks in the inherited history, the current reset maps of both
outputs agree with the input reset map. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

omit [DecidableEq Clock] in
private theorem owned_raw_reset {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) : currentResetMap owned.canonical = R := by
  obtain ⟨F,hF⟩ := owned.input_safe
  exact (safe_reset_map hF).symm.trans (owned.current_resets_of_safe hF)

omit [DecidableEq Clock] in
private theorem guard_raw_reset (G : List (Guard Clock)) {A : MixedJ Clock Var}
    (hg : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) = some A) :
    currentResetMap A = ClockResetSet.empty := by
  obtain ⟨S,hS,hr,hl⟩ := CanonicalSafety.guards_safe G A hg
  exact (safe_reset_map hS).symm.trans hr

omit [DecidableEq Clock] in
private theorem outside_reset (G : List (Guard Clock)) (R : ClockResetSet Clock) (K : MixedJ Clock Var) :
    currentResetMap (outsidePending G R K) = (currentResetMap K).union R := by
  cases hg : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
  | none => simp only [outsidePending,hg,currentResetMap]
  | some A =>
    simp only [outsidePending,hg,currentResetMap,guard_raw_reset G hg]
    rfl

omit [DecidableEq Clock] in
private theorem union_value (A B : ClockResetSet Clock) (c : Clock) :
    (A.union B).value c = (match A.value c with | some a => some a | none => B.value c) := rfl

/-- Both actual raw outputs preserve every old inherited assignment. -/
theorem SelectedTree.raw_reset_agreement
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) :
    (∀ c ∈ W, (currentResetMap H).value c = R.value c) ∧
    (∀ c ∈ W, (currentResetMap Er).value c = R.value c) := by
  induction T with
  | zero owned hz =>
    rw [owned_raw_reset owned]
    exact ⟨fun _ _ => rfl,fun _ _ => rfl⟩
  | ordinary owned choice tail ih =>
    constructor <;> intro c hc
    · simp only [outside_reset,currentResetMap,union_value,ClockResetSet.empty]
      rw [ih.1 c (choice.grows hc)]
      exact choice.old_absorption c hc
    · rw [outside_reset,union_value,ih.2 c (choice.grows hc)]
      exact choice.old_absorption c hc
  | required owned choice tail ih =>
    constructor <;> intro c hc
    · rw [outside_reset,union_value,ih.1 c hc]
      exact congrArg (fun S : ClockResetSet Clock => S.value c)
        (copyActiveResets_absorb _ _)
    · rw [outside_reset,union_value,ih.2 c hc]
      exact congrArg (fun S : ClockResetSet Clock => S.value c)
        (copyActiveResets_absorb _ _)
  | optional owned choice upper forced tail ih =>
    constructor <;> intro c hc
    · simp only [outside_reset,currentResetMap,union_value,ClockResetSet.empty]
      rw [ih.1 c (upper.grows hc)]
      have ha := upper.old_absorption c hc
      rw [union_value] at ha
      rw [ha]
      exact congrArg (fun S : ClockResetSet Clock => S.value c)
        (copyActiveResets_absorb _ _)
    · simp only [outside_reset,union_value]
      rw [ih.2 c (upper.grows hc)]
      have ha := upper.old_absorption c hc
      rw [union_value] at ha
      rw [ha]
      exact congrArg (fun S : ClockResetSet Clock => S.value c)
        (copyActiveResets_absorb _ _)

/-- Any safe normal form of the same full selected output has the actual
inherited map's values on every old-history clock. -/
theorem SelectedTree.normalized_reset_agreement
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    {F : Section3.TransitionForm Clock Var} (hF : SafeNormalization H F) :
    ∀ c ∈ W, F.current.resets.value c = R.value c := by
  rw [safe_reset_map hF]
  exact T.raw_reset_agreement.1

/-- The identical reset conclusion for the same tree's erased output. -/
theorem SelectedTree.erased_reset_agreement
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    {F : Section3.TransitionForm Clock Var} (hF : SafeNormalization Er F) :
    ∀ c ∈ W, F.current.resets.value c = R.value c := by
  rw [safe_reset_map hF]
  exact T.raw_reset_agreement.2
end STLTableau.Section4.Finiteness
