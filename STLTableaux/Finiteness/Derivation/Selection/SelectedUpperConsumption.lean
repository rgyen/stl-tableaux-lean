import STLTableaux.Finiteness.Derivation.Selection.SelectedBoundedConsumption
import STLTableaux.Finiteness.Derivation.Branches.RawBranchUpperShape
import STLTableaux.Finiteness.Derivation.Pending.PendingComplexityBarrier

/-! Formula-level accounting for actual selected upper expansions. -/
namespace STLTableau.Section4.Finiteness
open Section3
noncomputable section
variable {Clock Var : Type*} [DecidableEq Clock]
local instance : DecidableEq (Formula Var) := Classical.decEq _

/-- Plain consumption and optional boundary birth are the only possible credits
for new current upper sources. This ledger is computed from the same tree. -/
noncomputable def SelectedTree.upperCredits
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) : List (Formula Var) :=
  match T with
  | .zero _ _ => []
  | .ordinary _ choice tail => match choice.p with
    | .plain φ => φ :: tail.upperCredits
    | _ => tail.upperCredits
  | .required _ choice tail => timedFormula choice.kind choice.I choice.phi :: tail.upperCredits
  | .optional _ choice _ _ tail => timedFormula choice.kind choice.I choice.phi :: tail.upperCredits

omit [DecidableEq Clock] in
private theorem bounded_formula (c d : Clock) (m q : Marker) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var) :
    (Predicate.bounded c d m q kind I φ).formula = timedFormula kind I φ := by
  cases kind <;> rfl

private theorem credit_origin
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) (φ : Formula Var) :
    φ ∈ T.upperCredits ↔ φ ∈ T.plainConsumed ∨
      ∃ q, (q,false) ∈ T.boundaryConsumed ∧ q.formula = φ := by
  induction T with
  | zero => simp [SelectedTree.upperCredits,SelectedTree.plainConsumed,SelectedTree.boundaryConsumed]
  | ordinary owned choice tail ih =>
    simp only [SelectedTree.upperCredits,SelectedTree.plainConsumed,SelectedTree.boundaryConsumed]
    cases choice.p <;> simp_all [List.mem_cons]
    tauto
  | required owned choice tail ih =>
    simp only [SelectedTree.upperCredits,SelectedTree.plainConsumed,SelectedTree.boundaryConsumed,List.mem_cons]
    simp only [Prod.mk.injEq,Bool.false_eq_true,and_false]
    rw [ih]
    aesop
  | optional owned choice upper forced tail ih =>
    simp only [SelectedTree.upperCredits,SelectedTree.plainConsumed,SelectedTree.boundaryConsumed,List.mem_cons]
    rw [ih]
    simp only [Prod.mk.injEq,and_true]
    constructor
    · rintro (he | hp | ⟨q,hq,hf⟩)
      · exact Or.inr ⟨.bounded choice.c choice.d choice.m (Marker.complement choice.ell)
          choice.kind choice.I choice.phi,Or.inl rfl,by simpa only [bounded_formula] using he.symm⟩
      · exact Or.inl hp
      · exact Or.inr ⟨q,Or.inr hq,hf⟩
    · rintro (hp | ⟨q,hq,hf⟩)
      · exact Or.inr (Or.inl hp)
      · rcases hq with rfl | hq
        · exact Or.inl (by simpa only [bounded_formula] using hf.symm)
        · exact Or.inr (Or.inr ⟨q,hq,hf⟩)

/-- Formula credits are unique: an ordinary opening cannot compete with a
future optional fusion, because that future eligible source was already pending. -/
theorem SelectedTree.upperCredits_nodup
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    (hunique : ∀ p ∈ E, ∀ q ∈ E, p.formula = q.formula → p = q)
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) : T.upperCredits.Nodup := by
  induction T with
  | zero => exact List.nodup_nil
  | ordinary owned choice tail ih =>
    change (match choice.p with
      | .plain φ => φ :: tail.upperCredits
      | _ => tail.upperCredits).Nodup
    cases hp : choice.p with
    | plain φ =>
      apply List.nodup_cons.mpr
      refine ⟨?_,ih⟩
      intro hcredit
      rcases (credit_origin tail φ).1 hcredit with hplain | ⟨q,hq,hformula⟩
      · have hn := (SelectedTree.ordinary owned choice tail).plainConsumed_nodup
        change (match choice.p with | .plain ψ => ψ :: tail.plainConsumed | _ => tail.plainConsumed).Nodup at hn
        rw [hp] at hn
        exact (List.nodup_cons.mp hn).1 hplain
      · obtain ⟨hb,he,hm⟩ := tail.boundary_consumed_origin hq
        have hold : Local.predicate q ∈ choice.left++choice.right := by
          rcases (ordinary_child_current owned choice q).1 hm with hnew | hold
          · cases q with
            | bounded c d m ℓ kind I ψ => exact False.elim (choice.branch.no_current_bounded c d m ℓ kind I ψ hnew)
            | plain | upper => cases hb
          · exact hold
        apply choice.allowed.2
        exact ⟨q,he,ordinary_rest_subset owned choice hold,by rw [hp,hformula]⟩
    | upper => exact ih
    | bounded => exact ih
  | required owned choice tail ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_,ih⟩
    intro hcredit
    rcases (credit_origin tail _).1 hcredit with hplain | ⟨q,hq,hformula⟩
    · exact (List.nodup_cons.mp (SelectedTree.required owned choice tail).plainConsumed_nodup).1 hplain
    · have he := (tail.boundary_consumed_origin hq).2.1
      have heq : q = .bounded choice.c choice.d choice.m (Marker.complement choice.ell)
          choice.kind choice.I choice.phi :=
        hunique q he _ choice.eligible (hformula.trans (bounded_formula _ _ _ _ _ _ _).symm)
      subst q
      have hn := (SelectedTree.required owned choice tail).boundary_sources_nodup
      apply (List.nodup_cons.mp hn).1
      exact List.mem_map.mpr ⟨(_,false),hq,rfl⟩
  | optional owned choice upper forced tail ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_,ih⟩
    intro hcredit
    rcases (credit_origin tail _).1 hcredit with hplain | ⟨q,hq,hformula⟩
    · let θ := timedFormula choice.kind choice.I choice.phi
      let p : Predicate Clock Var := .bounded choice.c choice.d choice.m
        (Marker.complement choice.ell) choice.kind choice.I choice.phi
      have hb : ∀ q, Local.predicate q ∈ owned.locals → ¬q.IsAtomic →
          q.complexity ≤ (Predicate.plain θ : Predicate Clock Var).complexity := by
        intro q hm hn
        exact (choice.maximal.2 q hm hn).trans
          (plain_timed_above_bounded choice.c choice.d choice.m (Marker.complement choice.ell)
            choice.kind choice.I choice.phi).le
      have ha : Local.predicate (.plain θ) ∉ owned.locals :=
        maximal_no_plain_timed owned.locals p choice.maximal.2 choice.c choice.m
          choice.kind choice.I choice.phi (by rfl)
      exact (SelectedTree.optional owned choice upper forced tail).plain_consumption_barrier θ hb ha hplain
    · have he := (tail.boundary_consumed_origin hq).2.1
      have heq : q = .bounded choice.c choice.d choice.m (Marker.complement choice.ell)
          choice.kind choice.I choice.phi :=
        hunique q he _ choice.eligible (hformula.trans (bounded_formula _ _ _ _ _ _ _).symm)
      subst q
      have hn := (SelectedTree.optional owned choice upper forced tail).boundary_sources_nodup
      apply (List.nodup_cons.mp hn).1
      exact List.mem_map.mpr ⟨(_,false),hq,rfl⟩
private noncomputable def upperMatch (θ : Formula Var) : Local Clock Var → Bool
  | .predicate (.upper _ _ kind I φ) => by classical exact decide (timedFormula kind I φ = θ)
  | _ => false

private noncomputable def upperCount (L : List (Local Clock Var)) (θ : Formula Var) : ℕ :=
  L.countP (upperMatch θ)

private noncomputable def plainCredit (p : Predicate Clock Var) (θ : Formula Var) : ℕ := by
  classical
  exact match p with | .plain φ => if φ = θ then 1 else 0 | _ => 0

omit [DecidableEq Clock] in
private theorem upperMatch_witness {θ : Formula Var} {l : Local Clock Var}
    (h : upperMatch θ l = true) :
    ∃ c m kind I φ, l = .predicate (.upper c m kind I φ) ∧ timedFormula kind I φ = θ := by
  cases l with
  | terminal | marker => cases h
  | predicate p =>
    cases p with
    | plain | bounded => cases h
    | upper c m kind I φ =>
      exact ⟨c,m,kind,I,φ,rfl,of_decide_eq_true h⟩

omit [DecidableEq Clock] in
private theorem count_cover (L M : List (Local Clock Var)) (θ : Formula Var)
    (hL : L.Nodup) (hcover : ∀ l ∈ L, upperMatch θ l = true → l ∈ M) :
    upperCount L θ ≤ upperCount M θ := by
  rw [upperCount,upperCount,List.countP_eq_length_filter,List.countP_eq_length_filter]
  apply List.Subperm.length_le
  apply List.subperm_of_subset (hL.filter _)
  intro l hl
  obtain ⟨hl,hm⟩ := List.mem_filter.mp hl
  exact List.mem_filter.mpr ⟨hcover l hl hm,hm⟩

private theorem ordinary_upper_count
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (choice : OrdinaryChoice E owned) (θ : Formula Var) :
    upperCount choice.child.locals θ + (if upperMatch θ (.predicate choice.p) then 1 else 0) ≤
      upperCount owned.locals θ + plainCredit choice.p θ := by
  classical
  have hsplit : upperCount owned.locals θ = upperCount (choice.left++choice.right) θ +
      (if upperMatch θ (.predicate choice.p) then 1 else 0) := by
    rw [choice.split]
    simp only [upperCount,List.countP_append,List.countP_cons]
    omega
  by_cases hex : ∃ c m kind I φ, Predicate.upper c m kind I φ ∈ choice.B.currentPredicates
  · obtain ⟨c,m,kind,I,φ,hq⟩ := hex
    obtain ⟨hp,hB⟩ := choice.branch.current_upper_opening c m kind I φ hq
    have hc := count_cover choice.child.locals
      ((choice.left++choice.right) ++ [.predicate (.upper c m kind I φ)]) θ choice.child.locals_nodup (by
      intro l hl hm
      obtain ⟨c',m',kind',I',φ',rfl,hθ⟩ := upperMatch_witness hm
      rcases (ordinary_child_current owned choice _).1 hl with hnew | hold
      · rw [hB] at hnew
        have he : Predicate.upper c' m' kind' I' φ' = Predicate.upper c m kind I φ := by
          simpa only [Section3.Judgement.currentPredicates,Set.mem_union,
            Set.mem_singleton_iff,Set.mem_empty_iff_false,or_false] using hnew
        exact List.mem_append_right _ (by simp [he])
      · exact List.mem_append_left _ hold)
    rw [hsplit]
    simpa only [upperCount,List.countP_append,List.countP_singleton,hp,upperMatch,plainCredit,decide_eq_true_eq,Bool.false_eq_true,if_false,Nat.add_zero] using hc
  · have hc := count_cover choice.child.locals (choice.left++choice.right) θ choice.child.locals_nodup (by
      intro l hl hm
      obtain ⟨c,m,kind,I,φ,rfl,hθ⟩ := upperMatch_witness hm
      rcases (ordinary_child_current owned choice _).1 hl with hnew | hold
      · exact False.elim (hex ⟨c,m,kind,I,φ,hnew⟩)
      · exact hold)
    rw [hsplit]
    omega

private theorem boundary_upper_count
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) {required : Bool} (choice : BoundaryChoice E owned required)
    (θ : Formula Var) :
    upperCount choice.child.locals θ ≤ upperCount owned.locals θ +
      (if timedFormula choice.kind choice.I choice.phi = θ then 1 else 0) := by
  classical
  have hc := count_cover choice.child.locals
    (owned.locals ++ [.predicate (.upper choice.c choice.m choice.kind choice.I choice.phi)]) θ
    choice.child.locals_nodup (by
      intro l hl hm
      obtain ⟨c,m,kind,I,φ,rfl,hθ⟩ := upperMatch_witness hm
      rcases (boundary_child_current owned choice _).1 hl with he | hold
      · exact List.mem_append_right _ (by simp [he])
      · exact List.mem_append_left _ (boundary_rest_subset owned choice hold))
  simpa only [upperCount,List.countP_append,List.countP_singleton,upperMatch,decide_eq_true_eq] using hc

/-- Formula projection of actual upper-expansion events. -/
noncomputable def SelectedTree.upperExpanded
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) : List (Formula Var) :=
  match T with
  | .zero _ _ => []
  | .ordinary _ choice tail => match choice.p with
    | .upper _ _ kind I φ => timedFormula kind I φ :: tail.upperExpanded
    | _ => tail.upperExpanded
  | .required _ _ tail => tail.upperExpanded
  | .optional _ choice _ _ tail => timedFormula choice.kind choice.I choice.phi :: tail.upperExpanded

/-- The event projection is exactly the upper-source projection of the actual
raw-branch ledger, rather than an independent list of assumed expansions. -/
theorem SelectedTree.upperExpanded_eq_rawLedger
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) :
    T.upperExpanded = T.rawLedger.filterMap (fun entry => match entry.source with
      | .upper _ _ kind I φ => some (timedFormula kind I φ) | _ => none) := by
  induction T with
  | zero => rfl
  | ordinary owned choice tail ih =>
    simp only [SelectedTree.upperExpanded,SelectedTree.rawLedger,List.filterMap_cons]
    cases choice.p <;> simp_all
  | required owned choice tail ih => exact ih
  | optional owned choice upper forced tail ih =>
    simp only [SelectedTree.upperExpanded,SelectedTree.rawLedger,List.filterMap_cons,forced]
    exact congrArg (List.cons _) ih

private theorem upper_conservation
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) (θ : Formula Var) :
    T.upperExpanded.count θ ≤ upperCount owned.locals θ + T.upperCredits.count θ := by
  induction T with
  | zero => simp [SelectedTree.upperExpanded,SelectedTree.upperCredits]
  | ordinary owned choice tail ih =>
    have hc := ordinary_upper_count owned choice θ
    simp only [SelectedTree.upperExpanded,SelectedTree.upperCredits]
    cases hp : choice.p with
    | plain φ =>
      simp only [hp,upperMatch,plainCredit,Bool.false_eq_true,if_false,Nat.add_zero] at hc
      simp only [List.count_cons,beq_iff_eq]
      omega
    | upper c m kind I φ =>
      simp only [hp,upperMatch,plainCredit,decide_eq_true_eq,Nat.add_zero] at hc
      simp only [List.count_cons,beq_iff_eq]
      omega
    | bounded c d m q kind I φ =>
      simp only [hp,upperMatch,plainCredit,Bool.false_eq_true,if_false,Nat.add_zero] at hc
      change tail.upperExpanded.count θ ≤ upperCount owned.locals θ + tail.upperCredits.count θ
      exact ih.trans (Nat.add_le_add_right hc _)
  | required owned choice tail ih =>
    have hc := boundary_upper_count owned choice θ
    simp only [SelectedTree.upperExpanded,SelectedTree.upperCredits,List.count_cons,beq_iff_eq]
    omega
  | optional owned choice upper forced tail ih =>
    have hb := boundary_upper_count owned choice θ
    have hc := ordinary_upper_count choice.child upper θ
    simp only [forced,upperMatch,plainCredit,decide_eq_true_eq,Nat.add_zero] at hc
    simp only [SelectedTree.upperExpanded,SelectedTree.upperCredits,List.count_cons,beq_iff_eq]
    omega

/-- At most one actual upper expansion per temporal formula, provided the
actual incoming local spine contains no upper source and E has unique formulas.
The conclusion is the FORMULA projection of the SAME raw-branch ledger. -/
theorem SelectedTree.upper_ledger_formulas_nodup
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    (hunique : ∀ p ∈ E, ∀ q ∈ E, p.formula = q.formula → p = q)
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    (hno : ∀ c m kind I φ, Local.predicate (.upper c m kind I φ) ∉ owned.locals) :
    (T.rawLedger.filterMap (fun entry => match entry.source with
      | .upper _ _ kind I φ => some (timedFormula kind I φ) | _ => none)).Nodup := by
  rw [← T.upperExpanded_eq_rawLedger]
  apply List.nodup_iff_count_le_one.mpr
  intro θ
  have hz : upperCount owned.locals θ = 0 := by
    apply List.countP_eq_zero.mpr
    intro l hl
    cases hm : upperMatch θ l with
    | false => simp
    | true =>
      obtain ⟨c,m,kind,I,φ,rfl,hφ⟩ := upperMatch_witness hm
      exact False.elim (hno c m kind I φ hl)
  have hc := upper_conservation T θ
  have hb := List.nodup_iff_count_le_one.mp (T.upperCredits_nodup hunique) θ
  omega
/-- With no initial upper, every actual expanded upper formula has a credit
computed from this same tree. -/
theorem SelectedTree.upperExpanded_credit
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    (hno : ∀ c m kind I φ, Local.predicate (.upper c m kind I φ) ∉ owned.locals)
    {θ : Formula Var} (hθ : θ ∈ T.upperExpanded) : θ ∈ T.upperCredits := by
  have hz : upperCount owned.locals θ = 0 := by
    apply List.countP_eq_zero.mpr
    intro l hl
    cases hm : upperMatch θ l with
    | false => simp
    | true =>
      obtain ⟨c,m,kind,I,φ,rfl,hφ⟩ := upperMatch_witness hm
      exact False.elim (hno c m kind I φ hl)
  have hc := upper_conservation T θ
  have hp : 0 < T.upperExpanded.count θ := List.count_pos_iff.mpr hθ
  apply List.count_pos_iff.mp
  omega

/-- Every credit comes from a real plain raw expansion or a real boundary
consumption; required fusion is in the boundary alternative. -/
theorem SelectedTree.upper_credit_source
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) {φ : Formula Var} (hφ : φ ∈ T.upperCredits) :
    (∃ entry ∈ T.rawLedger, entry.source = .plain φ) ∨
      (∃ q required, (q,required) ∈ T.boundaryConsumed ∧ q.formula = φ) := by
  induction T with
  | zero => cases hφ
  | ordinary owned choice tail ih =>
    change φ ∈ (match choice.p with | .plain ψ => ψ :: tail.upperCredits | _ => tail.upperCredits) at hφ
    by_cases hplain : ∃ ψ, choice.p = .plain ψ
    · obtain ⟨ψ,hp⟩ := hplain
      rw [hp] at hφ
      rcases List.mem_cons.mp hφ with rfl | ht
      · exact Or.inl ⟨_,List.mem_cons_self,hp⟩
      · rcases ih ht with ⟨entry,he,hs⟩ | ⟨q,b,hq,hf⟩
        · exact Or.inl ⟨entry,List.mem_cons_of_mem _ he,hs⟩
        · exact Or.inr ⟨q,b,hq,hf⟩
    · have ht : φ ∈ tail.upperCredits := by cases hp : choice.p <;> simp_all
      rcases ih ht with ⟨entry,he,hs⟩ | ⟨q,b,hq,hf⟩
      · exact Or.inl ⟨entry,List.mem_cons_of_mem _ he,hs⟩
      · exact Or.inr ⟨q,b,hq,hf⟩
  | required owned choice tail ih =>
    rcases List.mem_cons.mp hφ with rfl | ht
    · exact Or.inr ⟨_,true,List.mem_cons_self,bounded_formula _ _ _ _ _ _ _⟩
    · rcases ih ht with he | ⟨q,b,hq,hf⟩
      · exact Or.inl he
      · exact Or.inr ⟨q,b,List.mem_cons_of_mem _ hq,hf⟩
  | optional owned choice upper forced tail ih =>
    rcases List.mem_cons.mp hφ with rfl | ht
    · exact Or.inr ⟨_,false,List.mem_cons_self,bounded_formula _ _ _ _ _ _ _⟩
    · rcases ih ht with ⟨entry,he,hs⟩ | ⟨q,b,hq,hf⟩
      · exact Or.inl ⟨entry,List.mem_cons_of_mem _ he,hs⟩
      · exact Or.inr ⟨q,b,List.mem_cons_of_mem _ hq,hf⟩

end
end STLTableau.Section4.Finiteness
