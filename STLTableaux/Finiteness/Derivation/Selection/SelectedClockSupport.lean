import STLTableaux.Finiteness.Derivation.StateInputLocals
import STLTableaux.Finiteness.Derivation.Selection.SelectedResetMap
import STLTableaux.Finiteness.Derivation.NormalizationSupport

/-! Actual full/erased selected syntax support, bounded by incoming syntax and
inherited reset names plus at most one selected fresh name per raw expansion.
This is not a formula-size, confinement, allocation or finite-pool theorem. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

def inputClockSupport (J : MixedJ Clock Var) (R : ClockResetSet Clock) : Set Clock :=
  syntaxClocks J ∪ R.clocks

private theorem local_support {J : MixedJ Clock Var} {l : Local Clock Var}
    (hl : l∈currentLocalSet J) : syntaxClocks l.toJudgement ⊆ syntaxClocks J := by
  induction J with
  | terminal | marker | predicate =>
      have he : l=_ := hl
      subst l
      exact Set.Subset.rfl
  | clock | next => cases hl
  | conj J K ih ik =>
      rcases hl with hl | hl
      · exact (ih hl).trans Set.subset_union_left
      · exact (ik hl).trans Set.subset_union_right
  | reset R J ih => exact (ih hl).trans Set.subset_union_right

private theorem guard_support {J : MixedJ Clock Var} {g : Section3.Guard Clock}
    (hg : g∈currentGuards J) : g.clock∈syntaxClocks J := by
  induction J with
  | clock c r a => have he : g=⟨c,r,a⟩ := hg; subst g; exact rfl
  | conj J K ih ik =>
      rcases hg with hg | hg
      · exact Or.inl (ih hg)
      · exact Or.inr (ik hg)
  | reset R J ih => exact Or.inr (ih hg)
  | terminal | marker | predicate | next => cases hg

private theorem payload_support {J K : MixedJ Clock Var} (hK : K∈nextPayloads J) :
    syntaxClocks K ⊆ syntaxClocks J := by
  induction J with
  | terminal | clock | marker | predicate => cases hK
  | next L => have he : K=L := hK; subst K; exact Set.Subset.rfl
  | conj J L ih ik =>
      rcases hK with hK | hK
      · exact (ih hK).trans Set.subset_union_left
      · exact (ik hK).trans Set.subset_union_right
  | reset R J ih => exact (ih hK).trans Set.subset_union_right

private theorem owned_local_support {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) {l : Local Clock Var} (hl : l∈owned.locals) :
    syntaxClocks l.toJudgement ⊆ syntaxClocks J := by
  apply local_support
  rw [owned.regroup.currentLocalSet_eq,canonical_currentLocalSet owned.shape]
  exact hl

private theorem owned_guard_support {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) {g : Section3.Guard Clock} (hg : g∈owned.guards) :
    g.clock∈syntaxClocks J := by
  apply guard_support
  rw [owned.regroup.currentGuards_eq,canonical_currentGuards owned.shape]
  exact hg

private theorem owned_payload_support {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) {K : MixedJ Clock Var} (hK : K∈owned.nextInputs) :
    syntaxClocks K ⊆ syntaxClocks J := by
  apply payload_support
  rw [owned.nextPayloads_eq]
  exact hK

private theorem fold_support (Js : List (MixedJ Clock Var)) (B : MixedJ Clock Var)
    (hf : foldCurrent Js=some B) (A : Set Clock)
    (hs : ∀K∈Js,syntaxClocks K⊆A) : syntaxClocks B⊆A := by
  induction Js generalizing B with
  | nil => cases hf
  | cons K Ks ih =>
      cases ht : foldCurrent Ks with
      | none =>
          have he : K=B := by simpa [foldCurrent,ht,optionalConj] using hf
          exact he ▸ hs K (by simp)
      | some T =>
          have he : .conj K T=B := by simpa [foldCurrent,ht,optionalConj] using hf
          subst B
          exact Set.union_subset (hs K (by simp)) (ih T ht (fun L hL => hs L (by simp [hL])))

private theorem residual_support {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) {L : List (Local Clock Var)}
    (hL : ∀l∈L,l∈owned.locals) {B : MixedJ Clock Var}
    (hf : foldCurrent (L.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next)=some B) :
    syntaxClocks B⊆syntaxClocks J := by
  apply fold_support _ B hf _
  intro K hK
  rcases List.mem_append.1 hK with hK | hK
  · obtain ⟨l,hl,rfl⟩ := List.mem_map.1 hK
    exact owned_local_support owned (hL l hl)
  · obtain ⟨L,hL,rfl⟩ := List.mem_map.1 hK
    exact owned_payload_support owned (K:=L) hL

private theorem owned_outside_support {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (K : MixedJ Clock Var) :
    syntaxClocks (outsidePending owned.guards R K) ⊆ inputClockSupport J R ∪ syntaxClocks K := by
  cases hg : foldCurrent (owned.guards.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
  | none =>
      simp only [outsidePending,hg,syntaxClocks]
      intro c hc
      rcases hc with hc | hc
      · exact Or.inl (Or.inr hc)
      · exact Or.inr hc
  | some G =>
      have hG : syntaxClocks G⊆syntaxClocks J := by
        apply fold_support _ G hg _
        intro K hK
        obtain ⟨g,hg,rfl⟩ := List.mem_map.1 hK
        exact Set.singleton_subset_iff.2 (owned_guard_support owned hg)
      simp only [outsidePending,hg,syntaxClocks]
      intro c hc
      rcases hc with hc | hc | hc
      · exact Or.inl (Or.inl (hG hc))
      · exact Or.inl (Or.inr hc)
      · exact Or.inr hc

/-- An arbitrary owned canonical presentation adds no hidden name except
its explicitly inherited current reset map. -/
theorem OwnedPending.canonical_clock_support {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) : syntaxClocks owned.canonical ⊆ inputClockSupport J R := by
  cases hb : foldCurrent (owned.locals.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next) with
  | none =>
      cases hg : foldCurrent (owned.guards.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
      | none =>
          have hs := owned.shape
          simp [canonicalSyntax,hb,hg,optionalConj] at hs
      | some G =>
          have he : G=owned.canonical := by simpa [canonicalSyntax,hb,hg,optionalConj] using owned.shape
          rw [← he]
          apply (fold_support _ G hg _ _).trans Set.subset_union_left
          intro K hK
          obtain ⟨g,hg,rfl⟩ := List.mem_map.1 hK
          exact Set.singleton_subset_iff.2 (owned_guard_support owned hg)
  | some B =>
      have he : outsidePending owned.guards R B=owned.canonical := by
        cases hg : foldCurrent (owned.guards.map (fun g => (g.toJudgement : MixedJ Clock Var))) <;>
          simpa [outsidePending,canonicalSyntax,hb,hg,optionalConj] using owned.shape
      rw [← he]
      apply (owned_outside_support owned B).trans
      exact Set.union_subset Set.Subset.rfl ((residual_support owned (fun _ h => h) hb).trans Set.subset_union_left)

private theorem reset_support (J : MixedJ Clock Var) : (currentResetMap J).clocks⊆syntaxClocks J := by
  induction J with
  | terminal | clock | marker | predicate | next =>
      rw [show currentResetMap _=ClockResetSet.empty from rfl,empty_reset_clocks]
      exact Set.empty_subset _
  | conj J K ih ik =>
      change ((currentResetMap J).union (currentResetMap K)).clocks⊆_
      rw [ClockResetSet.clocks_union]
      exact Set.union_subset_union ih ik
  | reset R J ih =>
      change ((currentResetMap J).union R).clocks⊆R.clocks∪syntaxClocks J
      rw [ClockResetSet.clocks_union]
      exact Set.union_subset (ih.trans Set.subset_union_right) Set.subset_union_left

variable [DecidableEq Clock]

private theorem ordinary_input_support
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} (choice : OrdinaryChoice E owned) :
    inputClockSupport (ordinarySelectedInput R (choice.left++choice.right) choice.B
      (foldCurrent ((choice.left++choice.right).map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next)))
      choice.childR ⊆ inputClockSupport J R ∪ {choice.x} := by
  have hp : Local.predicate choice.p∈owned.locals := by rw [choice.split]; simp
  have hsource := owned_local_support owned hp
  have hB := choice.branch.syntaxClocks_subset_source_union_singleton choice.x choice.reset_support
  have hrest : ∀l∈choice.left++choice.right,l∈owned.locals := by
    intro l hl
    rw [choice.split]
    simp only [List.mem_append,List.mem_cons] at hl ⊢
    tauto
  have hRaw : syntaxClocks (ordinarySelectedInput R (choice.left++choice.right) choice.B
      (foldCurrent ((choice.left++choice.right).map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next))) ⊆
      inputClockSupport J R ∪ {choice.x} := by
    cases hf : foldCurrent ((choice.left++choice.right).map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next) with
    | none =>
        intro c hc
        rcases hB hc with hc | hc
        · exact Or.inl (Or.inl (hsource hc))
        · exact Or.inr hc
    | some Γ =>
        have hΓ := residual_support owned hrest hf
        intro c hc
        change c∈syntaxClocks choice.B ∪ ((copyActiveResets R (choice.left++choice.right)).clocks ∪ syntaxClocks Γ) at hc
        rcases hc with hc | hc | hc
        · rcases hB hc with hc | hc
          · exact Or.inl (Or.inl (hsource hc))
          · exact Or.inr hc
        · rw [copyActiveResets_clocks] at hc
          exact Or.inl (Or.inr hc.1)
        · exact Or.inl (Or.inl (hΓ hc))
  apply Set.union_subset hRaw
  rw [choice.reset_origin]
  exact (reset_support _).trans hRaw

private theorem boundary_input_support
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {required : Bool} (choice : BoundaryChoice E owned required) :
    inputClockSupport (boundaryReplacementChild choice.c choice.m choice.ell choice.kind choice.I choice.phi
      (.reset (copyActiveResets R (choice.left++choice.right)) choice.Gamma))
      (copyActiveResets R (choice.left++choice.right)) ⊆ inputClockSupport J R := by
  have hp : Local.predicate (.bounded choice.c choice.d choice.m (Marker.complement choice.ell)
      choice.kind choice.I choice.phi)∈owned.locals := by rw [choice.split]; simp
  have hc : choice.c∈syntaxClocks J := owned_local_support owned hp (Or.inl rfl)
  have hL : ∀l∈Local.marker choice.ell::choice.rest,l∈owned.locals := by
    intro l hl
    have hremaining : l∈choice.left++choice.right := by
      apply choice.selection.mem_iff.2
      cases required <;> simp only [Bool.false_eq_true,eq_self,ite_false,ite_true] <;>
        first | exact hl | exact List.mem_cons_of_mem _ hl
    rw [choice.split]
    simp only [List.mem_append,List.mem_cons] at hremaining ⊢
    tauto
  have hf : foldCurrent ((Local.marker choice.ell::choice.rest).map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next)=some choice.Gamma := by
    simp only [List.map_cons,List.cons_append,Local.toJudgement,foldCurrent_cons]
    rw [← choice.residual]
  have hΓ := residual_support owned hL hf
  have hS : (copyActiveResets R (choice.left++choice.right)).clocks⊆R.clocks := by
    rw [copyActiveResets_clocks]; exact Set.inter_subset_left
  intro c h
  rcases h with h | h
  · cases hb : Marker.imp choice.ell choice.m <;>
      simp only [boundaryReplacementChild,withBoundaryGuard,hb,syntaxClocks,Set.mem_union,
        Set.mem_singleton_iff,Set.mem_empty_iff_false,false_or] at h
    · rcases h with h | h | h | h
      · exact Or.inl (h ▸ hc)
      · exact Or.inl (h ▸ hc)
      · exact Or.inr (hS h)
      · exact Or.inl (hΓ h)
    · rcases h with h | h | h
      · exact Or.inl (h ▸ hc)
      · exact Or.inr (hS h)
      · exact Or.inl (hΓ h)
  · exact Or.inr (hS h)


/-- One name is budgeted for each actual raw expansion, even when its chosen
branch does not use that name. Boundary replacement itself adds no name. -/
noncomputable def SelectedTree.freshClocks
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) : List Clock :=
  match T with
  | .zero _ _ => []
  | .ordinary _ choice tail => choice.x :: tail.freshClocks
  | .required _ _ tail => tail.freshClocks
  | .optional _ _ upper _ tail => upper.x :: tail.freshClocks

theorem SelectedTree.freshClocks_length
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) : T.freshClocks.length=T.rawLedger.length := by
  induction T with
  | zero => rfl
  | ordinary owned choice tail ih => exact congrArg Nat.succ ih
  | required owned choice tail ih => exact ih
  | optional owned choice upper forced tail ih => exact congrArg Nat.succ ih

omit [DecidableEq Clock] in
private theorem cons_lift {A B : Set Clock} {x : Clock} {xs : List Clock}
    (h : B⊆A∪{x}) : B∪{c | c∈xs} ⊆ A∪{c | c∈x::xs} := by
  intro c hc
  rcases hc with hc | hc
  · rcases h hc with hc | hc
    · exact Or.inl hc
    · exact Or.inr (List.mem_cons.2 (Or.inl hc))
  · exact Or.inr (List.mem_cons_of_mem _ hc)

omit [DecidableEq Clock] in
private theorem outside_bound
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (K : MixedJ Clock Var) {A : Set Clock}
    (hInput : inputClockSupport J R⊆A) (hK : syntaxClocks K⊆A) :
    syntaxClocks (outsidePending owned.guards R K)⊆A :=
  (owned_outside_support owned K).trans (Set.union_subset hInput hK)

/-- Both literal outputs of THIS tree have bounded full syntax support,
including current/next guards, reset bindings and retained annotations. -/
theorem SelectedTree.syntax_clock_support
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) :
    syntaxClocks H ⊆ inputClockSupport J R ∪ {c | c∈T.freshClocks} ∧
      syntaxClocks Er ⊆ inputClockSupport J R ∪ {c | c∈T.freshClocks} := by
  induction T with
  | zero owned hz =>
      simp only [SelectedTree.freshClocks,List.not_mem_nil,Set.setOf_false,Set.union_empty]
      exact ⟨owned.canonical_clock_support,owned.canonical_clock_support⟩
  | ordinary owned choice tail ih =>
      simp only [SelectedTree.freshClocks]
      have hLift := cons_lift (xs:=tail.freshClocks) (ordinary_input_support choice)
      have hp : Local.predicate choice.p∈owned.locals := by rw [choice.split]; simp
      constructor
      · apply outside_bound owned _ Set.subset_union_left
        exact Set.union_subset ((owned_local_support owned hp).trans (fun c hc => Or.inl (Or.inl hc))) (ih.1.trans hLift)
      · exact outside_bound owned _ Set.subset_union_left (ih.2.trans hLift)
  | required owned choice tail ih =>
      simp only [SelectedTree.freshClocks]
      have hLift := Set.union_subset_union (boundary_input_support choice)
        (Set.Subset.rfl (s:={c | c∈tail.freshClocks}))
      exact ⟨outside_bound owned _ Set.subset_union_left (ih.1.trans hLift),
        outside_bound owned _ Set.subset_union_left (ih.2.trans hLift)⟩
  | optional owned choice upper forced tail ih =>
      simp only [SelectedTree.freshClocks]
      have hb := boundary_input_support choice
      have hu := (ordinary_input_support upper).trans
        (Set.union_subset_union hb (Set.Subset.rfl (s:={upper.x})))
      have hLift := cons_lift (xs:=tail.freshClocks) hu
      have hInput := hb.trans (Set.subset_union_left (t:={c | c∈upper.x::tail.freshClocks}))
      have hp : Local.predicate upper.p∈choice.child.locals := by rw [upper.split]; simp
      have hSource := (owned_local_support choice.child hp).trans
        (Set.subset_union_left.trans hInput)
      constructor
      · apply outside_bound owned _ Set.subset_union_left
        apply outside_bound choice.child _ hInput
        exact Set.union_subset hSource (ih.1.trans hLift)
      · apply outside_bound owned _ Set.subset_union_left
        exact outside_bound choice.child _ hInput (ih.2.trans hLift)

/-- Actual normalized whole-form support follows from the same raw output. -/
theorem SelectedTree.normalized_clock_support
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) {F : Section3.TransitionForm Clock Var}
    (hSafe : SafeNormalization H F) :
    F.allClocks⊆inputClockSupport J R∪{c | c∈T.freshClocks} :=
  hSafe.allClocks_subset_syntax.trans T.syntax_clock_support.1

omit [DecidableEq Clock] in
theorem SafeNormalization.allClocks_eq_syntax
    {J : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var} (h : SafeNormalization J F) :
    F.allClocks = syntaxClocks J := by
  induction h with
  | terminal => simp [Section3.TransitionForm.allClocks,Section3.TransitionForm.freeClocks,
      Section3.TransitionForm.boundClocks,Section3.TransitionForm.bodyFreeClocks,
      Section3.TransitionForm.ofState,Section3.StateForm.ofLocal,
      Section3.StateForm.guardClocks,Section3.StateForm.localClocks,Section3.Local.freeClocks,
      Section3.Local.toJudgement,Section3.Judgement.freeClocks,empty_reset_clocks,syntaxClocks]
  | clock c r a => simp [Section3.TransitionForm.allClocks,Section3.TransitionForm.freeClocks,
      Section3.TransitionForm.boundClocks,Section3.TransitionForm.bodyFreeClocks,
      Section3.TransitionForm.ofState,Section3.StateForm.ofGuard,
      Section3.StateForm.guardClocks,Section3.StateForm.localClocks,Section3.Local.freeClocks,
      Section3.Local.toJudgement,empty_reset_clocks,syntaxClocks]
  | marker m => simp [Section3.TransitionForm.allClocks,Section3.TransitionForm.freeClocks,
      Section3.TransitionForm.boundClocks,Section3.TransitionForm.bodyFreeClocks,
      Section3.TransitionForm.ofState,Section3.StateForm.ofLocal,
      Section3.StateForm.guardClocks,Section3.StateForm.localClocks,Section3.Local.freeClocks,
      Section3.Local.toJudgement,Section3.Judgement.freeClocks,empty_reset_clocks,syntaxClocks]
  | predicate p =>
      cases p <;> simp [Section3.TransitionForm.allClocks,Section3.TransitionForm.freeClocks,
      Section3.TransitionForm.boundClocks,Section3.TransitionForm.bodyFreeClocks,
      Section3.TransitionForm.ofState,Section3.StateForm.ofLocal,
      Section3.StateForm.guardClocks,Section3.StateForm.localClocks,Section3.Local.freeClocks,
      Section3.Local.toJudgement,Section3.Judgement.freeClocks,empty_reset_clocks,syntaxClocks]
      ext c; simp [Set.mem_insert_iff,Set.mem_singleton_iff]
  | conj h g hc ih ig =>
    rw [NormalizationSupport.allClocks_union]
    exact congrArg₂ Set.union ih ig
  | reset R h hd ih =>
    rw [NormalizationSupport.allClocks_underReset]
    rw [ih]
    exact Set.union_comm _ _
  | next h hn ih =>
    rw [NormalizationSupport.allClocks_ofNext _ hn]
    exact ih

omit [DecidableEq Clock] in
/-- Actual safe input normalization fixes its exact syntax support; arbitrary
structural or semantic equivalence would not justify this inverse statement. -/
theorem input_clock_support_of_safe {J : MixedJ Clock Var} {N : Section3.StateForm Clock Var}
    (h : SafeNormalization J (.ofState N)) :
    inputClockSupport J N.resets = (Section3.TransitionForm.ofState N).allClocks := by
  rw [inputClockSupport,← h.allClocks_eq_syntax]
  apply Set.union_eq_left.mpr
  intro c hc
  exact Or.inr (Or.inl hc)

/-- The normalized WHOLE form counts all current/next guards and reset names,
with at most one budgeted fresh name per actual raw expansion. -/
theorem SelectedTree.normalized_clock_card
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) {F : Section3.TransitionForm Clock Var}
    (hSafe : SafeNormalization H F) :
    F.allClocks_finite.toFinset.card ≤
      ((syntaxClocks_finite J).union R.finite_domain).toFinset.card + T.rawLedger.length := by
  classical
  let A : Finset Clock := ((syntaxClocks_finite J).union R.finite_domain).toFinset
  have hsub : F.allClocks_finite.toFinset ⊆ A ∪ T.freshClocks.toFinset := by
    intro c hc
    have hm := T.normalized_clock_support hSafe ((Set.Finite.mem_toFinset _).1 hc)
    apply Finset.mem_union.2
    rcases hm with hc | hc
    · exact Or.inl ((Set.Finite.mem_toFinset _).2 hc)
    · exact Or.inr (List.mem_toFinset.2 hc)
  calc
    F.allClocks_finite.toFinset.card ≤ (A∪T.freshClocks.toFinset).card := Finset.card_le_card hsub
    _ ≤ A.card+T.freshClocks.toFinset.card := Finset.card_union_le _ _
    _ ≤ A.card+T.freshClocks.length := Nat.add_le_add_left (List.toFinset_card_le _) _
    _ = A.card+T.rawLedger.length := congrArg (fun n => A.card+n) T.freshClocks_length

/-- Input support is the actual normalized state support, not an arbitrary
history budget or an assumed formula-specific inventory. -/
theorem SelectedTree.normalized_clock_card_of_input
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {N : Section3.StateForm Clock Var} {W : Set Clock}
    {owned : OwnedPending J N.resets W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) (hInput : SafeNormalization J (.ofState N))
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization H F) :
    F.allClocks_finite.toFinset.card ≤
      (Section3.TransitionForm.ofState N).allClocks_finite.toFinset.card+T.rawLedger.length := by
  have he : ((syntaxClocks_finite J).union N.resets.finite_domain).toFinset =
      (Section3.TransitionForm.ofState N).allClocks_finite.toFinset := by
    ext c
    simp only [Set.Finite.mem_toFinset]
    change c∈inputClockSupport J N.resets ↔ c∈(Section3.TransitionForm.ofState N).allClocks
    rw [input_clock_support_of_safe hInput]
  have hh := T.normalized_clock_card hSafe
  rw [he] at hh
  exact hh

omit [DecidableEq Clock] in
/-- Public actual local support interface for subsequent allocation proofs. -/
theorem OwnedPending.local_clock_support
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) {l : Local Clock Var} (hl : l∈owned.locals) :
    syntaxClocks l.toJudgement⊆syntaxClocks J := owned_local_support owned hl

omit [DecidableEq Clock] in
theorem OwnedPending.outside_clock_support
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (K : MixedJ Clock Var) {A : Set Clock}
    (hInput : inputClockSupport J R⊆A) (hK : syntaxClocks K⊆A) :
    syntaxClocks (outsidePending owned.guards R K)⊆A := outside_bound owned K hInput hK

theorem BoundaryChoice.input_clock_support
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {required : Bool} (choice : BoundaryChoice E owned required) :
    inputClockSupport
      (boundaryReplacementChild choice.c choice.m choice.ell choice.kind choice.I choice.phi
        (.reset (copyActiveResets R (choice.left++choice.right)) choice.Gamma))
      (copyActiveResets R (choice.left++choice.right)) ⊆ inputClockSupport J R :=
  boundary_input_support choice

/-- No unused witness name is charged: only the actual raw branch syntax is
 added to the inherited input support. Exact reset_origin prevents hidden names. -/
theorem OrdinaryChoice.input_clock_support_branch
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} (choice : OrdinaryChoice E owned) :
    inputClockSupport (ordinarySelectedInput R (choice.left++choice.right) choice.B
      (foldCurrent ((choice.left++choice.right).map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next)))
      choice.childR ⊆ inputClockSupport J R ∪ syntaxClocks choice.B := by
  have hrest : ∀l∈choice.left++choice.right,l∈owned.locals := by
    intro l hl
    rw [choice.split]
    simp only [List.mem_append,List.mem_cons] at hl ⊢
    tauto
  have hRaw : syntaxClocks (ordinarySelectedInput R (choice.left++choice.right) choice.B
      (foldCurrent ((choice.left++choice.right).map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next))) ⊆
      inputClockSupport J R ∪ syntaxClocks choice.B := by
    cases hf : foldCurrent ((choice.left++choice.right).map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next) with
    | none => exact Set.subset_union_right
    | some Γ =>
        have hΓ := residual_support owned hrest hf
        intro c hc
        rcases hc with hc | hc | hc
        · exact Or.inr hc
        · rw [copyActiveResets_clocks] at hc
          exact Or.inl (Or.inr hc.1)
        · exact Or.inl (Or.inl (hΓ hc))
  apply Set.union_subset hRaw
  rw [choice.reset_origin]
  exact (STLTableau.Section4.Finiteness.reset_support _).trans hRaw

end STLTableau.Section4.Finiteness
