import STLTableaux.Finiteness.Bounds.SelectedOriginCount
import STLTableaux.Finiteness.Derivation.Selection.SelectedRetainedPredicates

/-! Counts of actual entries and retained labels of the same selected tree. -/
set_option linter.unusedSimpArgs false
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

namespace LedgerList

omit [DecidableEq Clock] in
theorem filterMap_fiber_unique {A B : Type*} (f : A → Option B)
    (L : List A) (hn : (L.filterMap f).Nodup) {a b : A} {v : B}
    (ha : a ∈ L) (hb : b ∈ L) (hfa : f a = some v) (hfb : f b = some v) : a=b := by
  induction L with
  | nil => cases ha
  | cons x L ih =>
    cases hx : f x with
    | none =>
      have hn' : (L.filterMap f).Nodup := by simpa only [List.filterMap_cons,hx] using hn
      have ha' : a ∈ L := by
        rcases List.mem_cons.mp ha with rfl | ha
        · rw [hx] at hfa; cases hfa
        · exact ha
      have hb' : b ∈ L := by
        rcases List.mem_cons.mp hb with rfl | hb
        · rw [hx] at hfb; cases hfb
        · exact hb
      exact ih hn' ha' hb'
    | some y =>
      have hn' : y ∉ L.filterMap f ∧(L.filterMap f).Nodup :=
        List.nodup_cons.mp (by simpa only [List.filterMap_cons,hx] using hn)
      rcases List.mem_cons.mp ha with hax | haTail
      · rcases List.mem_cons.mp hb with hbx | hbTail
        · exact hax.trans hbx.symm
        · have hfx : f x = some v := by rw [←hax];exact hfa
          have hv : y = v := Option.some.inj (hx.symm.trans hfx)
          have hm : y ∈ L.filterMap f := by rw [hv];exact List.mem_filterMap.mpr ⟨b,hbTail,hfb⟩
          exact False.elim (hn'.1 hm)
      · rcases List.mem_cons.mp hb with hbx | hbTail
        · have hfx : f x = some v := by rw [←hbx];exact hfb
          have hv : y = v := Option.some.inj (hx.symm.trans hfx)
          have hm : y ∈ L.filterMap f := by rw [hv];exact List.mem_filterMap.mpr ⟨a,haTail,hfa⟩
          exact False.elim (hn'.1 hm)
        · exact ih hn'.2 haTail hbTail

end LedgerList

def RawLedgerEntry.plainFormula (e : RawLedgerEntry (Clock := Clock) (Var := Var)) : Option (Formula Var) :=
  match e.source with | .plain φ => some φ | _ => none

def RawLedgerEntry.upperFormula (e : RawLedgerEntry (Clock := Clock) (Var := Var)) : Option (Formula Var) :=
  match e.source with | .upper _ _ kind I φ => some (timedFormula kind I φ) | _ => none

/-- Required fusion consumes an unclocked predicate without creating a raw branch. -/
theorem SelectedTree.plain_ledger_sublist
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) :
    (T.rawLedger.filterMap RawLedgerEntry.plainFormula).Sublist T.plainConsumed := by
  induction T with
  | zero => exact List.Sublist.refl _
  | ordinary owned choice tail ih =>
    simp only [SelectedTree.rawLedger, SelectedTree.plainConsumed, List.filterMap_cons, RawLedgerEntry.plainFormula]
    cases hp : choice.p <;>
      simpa only [SelectedTree.rawLedger, SelectedTree.plainConsumed,
        List.filterMap_cons, RawLedgerEntry.plainFormula, hp] using
          (by first | exact ih.cons_cons _ | exact ih)
  | required owned choice tail ih => exact ih.cons _
  | optional owned choice upper forced tail ih =>
    simpa only [SelectedTree.rawLedger, SelectedTree.plainConsumed,
      List.filterMap_cons, RawLedgerEntry.plainFormula, forced] using ih

/-- Every branch source has exactly one of the three predicate constructors. -/
theorem rawLedger_length_decomposition
    (L : List (RawLedgerEntry (Clock := Clock) (Var := Var))) :
    L.length = (L.filterMap RawLedgerEntry.plainFormula).length +
      (L.filterMap RawLedgerEntry.upperFormula).length +
      (L.filterMap RawLedgerEntry.boundedSource).length := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [RawLedgerEntry.plainFormula, RawLedgerEntry.upperFormula, RawLedgerEntry.boundedSource] at ih
    cases hs : e.source <;>
      simp only [List.length_cons, List.filterMap_cons, RawLedgerEntry.plainFormula,
        RawLedgerEntry.upperFormula, RawLedgerEntry.boundedSource, hs,
        List.length_cons] <;> omega

private theorem list_length_le_finset {α : Type*} (L : List α) (Q : Finset α)
    (hn : L.Nodup) (hm : ∀ a∈L,a∈Q) : L.length≤Q.card := by
  classical
  rw [← List.toFinset_card_of_nodup hn]
  exact Finset.card_le_card (fun a ha=>hm a (List.mem_toFinset.mp ha))

/-- The recorded sources in the `↑↓` form are counted by the local
predicates of that form in the input. -/
theorem SelectedTree.bounded_ledger_length_bound
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {N : Section3.StateForm Clock Var} {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    (hLocal : ∀l,l∈owned.locals ↔l∈N.locals) :
    (T.rawLedger.filterMap RawLedgerEntry.boundedSource).length≤Fintype.card (BoundedLocal N) := by
  classical
  let L := T.rawLedger.filterMap RawLedgerEntry.boundedSource
  have hm : ∀p∈L,Local.predicate p∈N.locals ∧IsBoundedPredicate p := by
    intro p hp
    obtain ⟨e,he,hp⟩ := List.mem_filterMap.mp hp
    have hs : e.source=p ∧IsBoundedPredicate p := by
      cases hs : e.source with
      | plain | upper => simp [RawLedgerEntry.boundedSource,hs] at hp
      | bounded c d m r kind I φ =>
        have hEq : Predicate.bounded c d m r kind I φ=p := by
          simpa [RawLedgerEntry.boundedSource,hs] using hp
        exact ⟨hEq,hEq ▸ trivial⟩
    exact ⟨(hLocal _).1 (hs.1 ▸ T.bounded_ledger_origin he (hs.1 ▸ hs.2)),hs.2⟩
  let f : {p : Predicate Clock Var // p∈L.toFinset} →BoundedLocal N := fun p=>⟨p.val,hm p.val (List.mem_toFinset.mp p.property)⟩
  have hi : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    exact congrArg (fun z : BoundedLocal N=>z.val) h
  have hc := Fintype.card_le_of_injective f hi
  simpa [L,List.toFinset_card_of_nodup T.bounded_ledger_nodup] using hc

/-- Actual raw branch count: incoming `↑↓` sources and two formula inventories. -/
theorem SelectedTree.rawLedger_length_bound
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}
    {N : Section3.StateForm Clock Var} (O : InputOrigins σ P α k N)
    {J : MixedJ Clock Var} {W : Set Clock} {owned : OwnedPending J N.resets W}
    {H Er : MixedJ Clock Var} (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (hLocal : ∀l,l∈owned.locals ↔l∈N.locals)
    (Q : Finset (Formula Var)) (hQ : ∀e∈T.rawLedger,e.source.formula∈Q) :
    T.rawLedger.length≤Fintype.card (BoundedLocal N)+2*Q.card := by
  classical
  have hp := list_length_le_finset (T.rawLedger.filterMap RawLedgerEntry.plainFormula) Q
    (T.plainConsumed_nodup.sublist T.plain_ledger_sublist) (by
      intro φ hφ
      obtain ⟨e,he,hφ⟩ := List.mem_filterMap.mp hφ
      have hf : e.source.formula=φ := by
        cases hs : e.source with
        | plain ψ => simpa [RawLedgerEntry.plainFormula,hs,Predicate.formula] using hφ
        | upper | bounded => simp [RawLedgerEntry.plainFormula,hs] at hφ
      exact hf ▸ hQ e he)
  have hu := list_length_le_finset (T.rawLedger.filterMap RawLedgerEntry.upperFormula) Q
    (T.upper_ledger_formulas_nodup (fun p hp q hq he=>O.eligible_unique_formula hp hq he)
      (fun c m kind I φ hm=>O.no_upper c m kind I φ ((hLocal _).1 hm))) (by
      intro φ hφ
      obtain ⟨e,he,hφ⟩ := List.mem_filterMap.mp hφ
      have hf : e.source.formula=φ := by
        cases hs : e.source with
        | upper c m kind I ψ =>
          have heq : timedFormula kind I ψ=φ := by simpa [RawLedgerEntry.upperFormula,hs] using hφ
          cases kind <;> simpa [hs,Predicate.formula,timedFormula] using heq
        | plain | bounded => simp only [RawLedgerEntry.upperFormula,hs] at hφ; cases hφ
      exact hf ▸ hQ e he)
  have hb := T.bounded_ledger_length_bound hLocal
  have hd := rawLedger_length_decomposition T.rawLedger
  omega

def RawLedgerEntry.upperSource (e : RawLedgerEntry (Clock := Clock) (Var := Var)) : Option (Predicate Clock Var) :=
  match e.source with | p@(.upper _ _ _ _ _) => some p | _ => none

private theorem upper_projection_lengths
    (L : List (RawLedgerEntry (Clock := Clock) (Var := Var))) :
    (L.filterMap RawLedgerEntry.upperSource).length=(L.filterMap RawLedgerEntry.upperFormula).length := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [RawLedgerEntry.upperSource,RawLedgerEntry.upperFormula] at ih
    cases hs : e.source <;> simpa [List.filterMap_cons,RawLedgerEntry.upperSource,RawLedgerEntry.upperFormula,hs] using ih

/-- Full labels include atomic unclocked sources as well as retained expansions. -/
theorem SelectedTree.current_locals_card_bound
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}
    {N : Section3.StateForm Clock Var} (O : InputOrigins σ P α k N)
    {J : MixedJ Clock Var} {W : Set Clock} {owned : OwnedPending J N.resets W}
    {H Er : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (hLocal : ∀l,l∈owned.locals ↔l∈N.locals) (hSafe : SafeNormalization H F)
    (Q : Finset (Formula Var))
    (hQ : ∀p,Local.predicate p∈F.current.locals→p.formula∈Q) :
    F.current.locals_finite.toFinset.card≤Fintype.card (BoundedLocal N)+2*Q.card+3 := by
  classical
  let plains : Finset (Local Clock Var) := Q.image (fun φ=>.predicate (.plain φ))
  let uppers := (T.rawLedger.filterMap RawLedgerEntry.upperSource).toFinset.image Local.predicate
  let bounds : Finset (Local Clock Var) := Finset.univ.image (fun q : BoundedLocal N=>Local.predicate q.val)
  let others : Finset (Local Clock Var) := {.terminal,.marker .open,.marker .closed}
  have hcover : F.current.locals_finite.toFinset⊆plains∪uppers∪bounds∪others := by
    intro l hl
    have hl : l∈F.current.locals := by simpa using hl
    cases l with
    | terminal => simp [others]
    | marker m => cases m <;> simp [others]
    | predicate p =>
      cases p with
      | plain φ =>
        have hm := hQ (.plain φ) hl
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨φ,hm,rfl⟩)))
      | upper c m kind I φ =>
        obtain ⟨e,he,hs⟩ := (T.normalized_retained_nonatomic_iff hSafe _ (by simp [Predicate.IsAtomic])).1 hl
        have hm : Predicate.upper c m kind I φ∈T.rawLedger.filterMap RawLedgerEntry.upperSource :=
          List.mem_filterMap.mpr ⟨e,he,by simp [RawLedgerEntry.upperSource,hs]⟩
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨_,List.mem_toFinset.mpr hm,rfl⟩)))
      | bounded c d m r kind I φ =>
        obtain ⟨e,he,hs⟩ := (T.normalized_retained_nonatomic_iff hSafe _ (by simp [Predicate.IsAtomic])).1 hl
        have hb : IsBoundedPredicate e.source := by simp [hs,IsBoundedPredicate]
        have hm := (hLocal _).1 (T.bounded_ledger_origin he hb)
        let q : BoundedLocal N := ⟨.bounded c d m r kind I φ,hs ▸ hm,trivial⟩
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩))
  have hp : plains.card≤Q.card := Finset.card_image_le
  have hb : bounds.card≤Fintype.card (BoundedLocal N) := by
    exact (Finset.card_image_le).trans_eq (Finset.card_univ)
  have hu : uppers.card≤Q.card := by
    have hnodup := T.upper_ledger_formulas_nodup
      (fun p hp q hq he=>O.eligible_unique_formula hp hq he)
      (fun c m kind I φ hm=>O.no_upper c m kind I φ ((hLocal _).1 hm))
    apply (Finset.card_image_le.trans (List.toFinset_card_le _)).trans
    rw [upper_projection_lengths]
    apply list_length_le_finset _ Q hnodup
    intro φ hφ
    obtain ⟨e,he,hφ⟩ := List.mem_filterMap.mp hφ
    cases hs : e.source with
    | plain | bounded => simp only [RawLedgerEntry.upperFormula,hs] at hφ; cases hφ
    | upper c m kind I ψ =>
      have hl : Local.predicate (.upper c m kind I ψ)∈F.current.locals :=
        (T.normalized_retained_nonatomic_iff hSafe _ (by simp [Predicate.IsAtomic])).2 ⟨e,he,hs⟩
      have heq : timedFormula kind I ψ=φ := by simpa [RawLedgerEntry.upperFormula,hs] using hφ
      have hh := hQ _ hl
      cases kind <;> simpa [Predicate.formula,timedFormula] using heq ▸ hh
  have ho : others.card≤3 := by simp [others]
  have hc := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hc1 := Finset.card_union_le (plains∪uppers) bounds
  have hc2 := Finset.card_union_le plains uppers
  omega

end STLTableau.Section4.Finiteness
