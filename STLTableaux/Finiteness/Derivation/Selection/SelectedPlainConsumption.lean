import STLTableaux.Finiteness.Derivation.Selection.SelectedLedger

/-! No repeated plain consumption in the same actual selected tree. Maximality,
strict ordinary child rank and literal boundary source removal supply the proof. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

omit [DecidableEq Clock] in
private theorem owned_local {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (p : Predicate Clock Var) :
    Local.predicate p ∈ owned.locals ↔ p ∈ J.currentPredicates := by
  rw [owned.regroup.currentPredicates_eq]
  exact (canonical_currentPredicates_iff owned.shape p).symm

omit [DecidableEq Clock] in
private theorem fold_current {L : List (Local Clock Var)} {Ns : List (MixedJ Clock Var)}
    {J : MixedJ Clock Var}
    (hf : foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next) = some J)
    (p : Predicate Clock Var) : p ∈ J.currentPredicates ↔ Local.predicate p ∈ L := by
  have hs : canonicalSyntax ClockResetSet.empty [] L Ns = some (.reset ClockResetSet.empty J) := by
    simp only [canonicalSyntax,List.map_nil,foldCurrent,optionalConj,hf,Option.map_some]
  exact canonical_currentPredicates_iff hs p

theorem ordinary_rest_subset
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (choice : OrdinaryChoice E owned)
    {l : Local Clock Var} (hl : l ∈ choice.left++choice.right) : l ∈ owned.locals := by
  rw [choice.split]
  simp only [List.mem_append,List.mem_cons] at hl ⊢
  tauto

theorem ordinary_child_current
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (choice : OrdinaryChoice E owned) (q : Predicate Clock Var) :
    Local.predicate q ∈ choice.child.locals ↔
      q ∈ choice.B.currentPredicates ∨ Local.predicate q ∈ choice.left++choice.right := by
  rw [owned_local choice.child q]
  cases hf : foldCurrent ((choice.left++choice.right).map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) with
  | none =>
    have hn := (foldCurrent_none_iff _).1 hf
    have he : choice.left++choice.right = [] := by
      simpa only [List.map_eq_nil_iff] using (List.append_eq_nil_iff.mp hn).1
    simp only [ordinarySelectedInput,he,List.not_mem_nil,or_false]
  | some Γ =>
    simp only [ordinarySelectedInput,Section3.Judgement.currentPredicates,Set.mem_union]
    rw [fold_current hf q]

omit [DecidableEq Clock] in
private theorem marker_residual_current (ℓ : Marker) (L : List (Local Clock Var))
    (Ns : List (MixedJ Clock Var)) (q : Predicate Clock Var) :
    q ∈ (prependCurrent (.marker ℓ)
      (foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next))).currentPredicates ↔
      Local.predicate q ∈ L := by
  cases hf : foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next) with
  | none =>
    have hn := (foldCurrent_none_iff _).1 hf
    have he : L = [] := by
      simpa only [List.map_eq_nil_iff] using (List.append_eq_nil_iff.mp hn).1
    simp only [prependCurrent,Section3.Judgement.currentPredicates,Set.mem_empty_iff_false,he,List.not_mem_nil]
  | some Γ =>
    simp only [prependCurrent,Section3.Judgement.currentPredicates,Set.empty_union]
    exact fold_current hf q

theorem boundary_child_current
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) {required : Bool} (choice : BoundaryChoice E owned required)
    (q : Predicate Clock Var) :
    Local.predicate q ∈ choice.child.locals ↔
      q = .upper choice.c choice.m choice.kind choice.I choice.phi ∨ Local.predicate q ∈ choice.rest := by
  rw [owned_local choice.child q]
  simp only [boundaryReplacementChild,Section3.Judgement.currentPredicates,Set.mem_union,
    Set.mem_singleton_iff,Set.mem_empty_iff_false,false_or]
  have hg : (withBoundaryGuard choice.c (Marker.imp choice.ell choice.m)
      (.reset (copyActiveResets R (choice.left++choice.right)) choice.Gamma)).currentPredicates =
      choice.Gamma.currentPredicates := by
    cases Marker.imp choice.ell choice.m <;>
      simp only [withBoundaryGuard,Section3.Judgement.currentPredicates,Set.empty_union]
  rw [hg,choice.residual,marker_residual_current]

theorem boundary_rest_subset
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) {required : Bool} (choice : BoundaryChoice E owned required)
    {l : Local Clock Var} (hl : l ∈ choice.rest) : l ∈ owned.locals := by
  have hr : l ∈ choice.left++choice.right := choice.selection.mem_iff.mpr (by cases required <;> simp [hl])
  rw [choice.split]
  simp only [List.mem_append,List.mem_cons] at hr ⊢
  tauto

private theorem ordinary_barrier
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (choice : OrdinaryChoice E owned) (φ : Formula Var)
    (hb : ∀ q, Local.predicate q ∈ owned.locals → ¬q.IsAtomic →
      q.complexity ≤ (Predicate.plain φ : Predicate Clock Var).complexity)
    (ha : Local.predicate (.plain φ) ∉ choice.left++choice.right) :
    (∀ q, Local.predicate q ∈ choice.child.locals → ¬q.IsAtomic →
      q.complexity ≤ (Predicate.plain φ : Predicate Clock Var).complexity) ∧
      Local.predicate (.plain φ) ∉ choice.child.locals := by
  have hp : choice.p.complexity ≤ (Predicate.plain φ : Predicate Clock Var).complexity :=
    hb _ (by rw [choice.split]; simp) choice.maximal.1
  constructor
  · intro q hq hn
    rcases (ordinary_child_current owned choice q).1 hq with hnew | hold
    · exact (choice.branch.current_smaller q hnew).le.trans hp
    · exact hb q (ordinary_rest_subset owned choice hold) hn
  · intro hq
    rcases (ordinary_child_current owned choice (.plain φ)).1 hq with hnew | hold
    · exact (Nat.not_lt_of_ge hp) (choice.branch.current_smaller _ hnew)
    · exact ha hold

private theorem boundary_barrier
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) {required : Bool} (choice : BoundaryChoice E owned required) (φ : Formula Var)
    (hb : ∀ q, Local.predicate q ∈ owned.locals → ¬q.IsAtomic →
      q.complexity ≤ (Predicate.plain φ : Predicate Clock Var).complexity)
    (ha : Local.predicate (.plain φ) ∉ choice.rest) :
    (∀ q, Local.predicate q ∈ choice.child.locals → ¬q.IsAtomic →
      q.complexity ≤ (Predicate.plain φ : Predicate Clock Var).complexity) ∧
      Local.predicate (.plain φ) ∉ choice.child.locals := by
  constructor
  · intro q hq hn
    rcases (boundary_child_current owned choice q).1 hq with rfl | hold
    · have hs := hb (.bounded choice.c choice.d choice.m (Marker.complement choice.ell)
          choice.kind choice.I choice.phi) (by rw [choice.split]; simp)
          (by simp [Predicate.IsAtomic])
      exact hs
    · exact hb q (boundary_rest_subset owned choice hold) hn
  · intro hq
    rcases (boundary_child_current owned choice (.plain φ)).1 hq with he | hold
    · cases he
    · exact ha hold

/-- Once an unclocked predicate is absent and all active nonatomic ranks are at most
its rank, no subsequent selected step can consume it. -/
theorem SelectedTree.plain_consumption_barrier
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) (φ : Formula Var)
    (hb : ∀ q, Local.predicate q ∈ owned.locals → ¬q.IsAtomic →
      q.complexity ≤ (Predicate.plain φ : Predicate Clock Var).complexity)
    (ha : Local.predicate (.plain φ) ∉ owned.locals) : φ ∉ T.plainConsumed := by
  induction T generalizing φ with
  | zero => simp [SelectedTree.plainConsumed]
  | ordinary owned choice tail ih =>
    have hc := ordinary_barrier owned choice φ hb (fun h => ha (ordinary_rest_subset owned choice h))
    have ht := ih φ hc.1 hc.2
    change φ ∉ (match choice.p with
      | .plain ψ => ψ :: tail.plainConsumed
      | _ => tail.plainConsumed)
    cases hp : choice.p with
    | plain ψ =>
      simp only [List.mem_cons,not_or]
      refine ⟨?_,ht⟩
      intro he
      subst ψ
      apply ha
      rw [choice.split,hp]
      simp
    | upper => simpa only [SelectedTree.plainConsumed,hp] using ht
    | bounded => simpa only [SelectedTree.plainConsumed,hp] using ht
  | required owned choice tail ih =>
    have hc := boundary_barrier owned choice φ hb (fun h => ha (boundary_rest_subset owned choice h))
    simp only [SelectedTree.plainConsumed,List.mem_cons,not_or]
    refine ⟨?_,ih φ hc.1 hc.2⟩
    intro he
    apply ha
    have hm : Local.predicate (.plain (timedFormula choice.kind choice.I choice.phi)) ∈ owned.locals := by
      have hr := choice.selection.mem_iff.mpr (by simp : Local.predicate (.plain
        (timedFormula choice.kind choice.I choice.phi)) ∈
          (if true then .predicate (.plain (timedFormula choice.kind choice.I choice.phi)) :: .marker choice.ell :: choice.rest else .marker choice.ell :: choice.rest))
      rw [choice.split]
      simp only [List.mem_append,List.mem_cons] at hr ⊢
      tauto
    simpa only [he] using hm
  | optional owned choice upper forced tail ih =>
    have hc := boundary_barrier owned choice φ hb (fun h => ha (boundary_rest_subset owned choice h))
    have hu := ordinary_barrier choice.child upper φ hc.1
      (fun h => hc.2 (ordinary_rest_subset choice.child upper h))
    exact ih φ hu.1 hu.2

/-- Each unclocked predicate is consumed at most once in the selected tree.
This is derived from maximal rank and source removal, not a certificate field. -/
theorem SelectedTree.plainConsumed_nodup
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) : T.plainConsumed.Nodup := by
  induction T with
  | zero => exact List.nodup_nil
  | ordinary owned choice tail ih =>
    change (match choice.p with
      | .plain ψ => ψ :: tail.plainConsumed
      | _ => tail.plainConsumed).Nodup
    cases hp : choice.p with
    | plain φ =>
      have hb : ∀ q, Local.predicate q ∈ owned.locals → ¬q.IsAtomic →
          q.complexity ≤ (Predicate.plain φ : Predicate Clock Var).complexity := by
        intro q hq hn
        simpa only [hp] using choice.maximal.2 q hq hn
      have ha : Local.predicate (.plain φ) ∉ choice.left++choice.right := by
        have hn : (Local.predicate choice.p :: (choice.left++choice.right)).Nodup :=
          List.perm_middle.nodup_iff.mp (choice.split ▸ owned.locals_nodup)
        simpa only [hp] using (List.nodup_cons.mp hn).1
      have hc := ordinary_barrier owned choice φ hb ha
      exact List.nodup_cons.mpr ⟨tail.plain_consumption_barrier φ hc.1 hc.2,ih⟩
    | upper => exact ih
    | bounded => exact ih
  | required owned choice tail ih =>
    let θ := timedFormula choice.kind choice.I choice.phi
    have hb : ∀ q, Local.predicate q ∈ owned.locals → ¬q.IsAtomic →
        q.complexity ≤ (Predicate.plain θ : Predicate Clock Var).complexity :=
      choice.maximal.2
    have hn : (Local.predicate (.bounded choice.c choice.d choice.m
        (Marker.complement choice.ell) choice.kind choice.I choice.phi) ::
          (choice.left++choice.right)).Nodup :=
      List.perm_middle.nodup_iff.mp (choice.split ▸ owned.locals_nodup)
    have hs := choice.selection.nodup_iff.mp (List.nodup_cons.mp hn).2
    change (Local.predicate (.plain θ) :: Local.marker choice.ell :: choice.rest).Nodup at hs
    have ha : Local.predicate (.plain θ) ∉ choice.rest := by
      intro hm
      exact (List.nodup_cons.mp hs).1 (List.mem_cons_of_mem _ hm)
    have hc := boundary_barrier owned choice θ hb ha
    exact List.nodup_cons.mpr ⟨tail.plain_consumption_barrier θ hc.1 hc.2,ih⟩
  | optional owned choice upper forced tail ih => exact ih
end STLTableau.Section4.Finiteness
