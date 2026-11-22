import STLTableaux.Finiteness.Derivation.Pending.PendingBoundaryExposure
import STLTableaux.Finiteness.Derivation.BoundaryReplacementSupport
import STLTableaux.Finiteness.Derivation.CanonicalSafety
import STLTableaux.Finiteness.Derivation.Pending.PendingCollection
import STLTableaux.Finiteness.Derivation.Pending.PendingNextPrivacy

/-! Construct the actual canonical boundary child. Old outside guards retain
their scope; only the new strict guard needs inherited-reset noncapture. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*}

def boundaryChildGuards (c : Clock) (b : Marker) (G : List (Section3.Guard Clock)) : List (Section3.Guard Clock) :=
  match b with
  | .closed => G
  | .open => ⟨c,.gt,0⟩ :: G

def outsidePending (G : List (Section3.Guard Clock)) (R : ClockResetSet Clock)
    (K : MixedJ Clock Var) : MixedJ Clock Var :=
  match foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
  | none => .reset R K
  | some A => .conj A (.reset R K)

private theorem swap_front (A B C : MixedJ Clock Var) :
    StructuralEq (.conj A (.conj B C)) (.conj B (.conj A C)) :=
  (ACIdem.symm (.assoc A B C)).trans ((ACIdem.conj (.comm A B) (.refl C)).trans (.assoc B A C))

private theorem child_guard_expose (c : Clock) (m ℓ : Marker) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var) (Γ : MixedJ Clock Var) :
    StructuralEq (boundaryReplacementChild c m ℓ kind I φ Γ)
      (withBoundaryGuard c (Marker.imp ℓ m)
        (.conj (.predicate (.upper c m kind I φ)) (.conj (.marker ℓ) Γ))) := by
  cases hg : Marker.imp ℓ m with
  | closed => simp only [boundaryReplacementChild,hg,withBoundaryGuard]; exact .refl _
  | «open» =>
      simp only [boundaryReplacementChild,hg,withBoundaryGuard]
      exact (ACIdem.conj (.refl _) (swap_front _ _ _)).trans (swap_front _ _ _)

private theorem guards_weight_zero (G : List (Section3.Guard Clock))
    (A : MixedJ Clock Var) (hf : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) = some A) :
    pendingWeight A = 0 := by
  induction G generalizing A with
  | nil => cases hf
  | cons g G ih =>
      rw [List.map_cons,foldCurrent_cons] at hf
      have he := Option.some.inj hf
      subst A
      cases ht : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
      | none => cases g; rfl
      | some T =>
          have hz := ih T ht
          cases g
          simpa only [prependCurrent,pendingWeight,Section3.Guard.toJudgement,Nat.zero_add] using hz

private theorem canonical_weight
    {R : ClockResetSet Clock} {G : List (Section3.Guard Clock)} {L : List (Local Clock Var)}
    {Ns : List (MixedJ Clock Var)} {C B : MixedJ Clock Var}
    (hs : canonicalSyntax R G L Ns = some C)
    (hb : foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next) = some B) :
    pendingWeight C = pendingWeight B := by
  cases hg : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
  | none =>
      have he : .reset R B = C := by simpa [canonicalSyntax,hg,hb,optionalConj] using hs
      subst C; rfl
  | some A =>
      have he : .conj A (.reset R B) = C := by simpa [canonicalSyntax,hg,hb,optionalConj] using hs
      subst C
      simp only [pendingWeight,guards_weight_zero G A hg,Nat.zero_add]

/-- Directed construction: no post-child shape, regrouping, or ownership
witness is supplied as a premise. Literal next inputs are retained. -/
theorem assemble_boundary_child
    (R : ClockResetSet Clock) (G : List (Section3.Guard Clock))
    (c : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (rest : List (Local Clock Var)) (Ns : List (MixedJ Clock Var)) (Γ : MixedJ Clock Var)
    (hΓ : Γ = prependCurrent (.marker ℓ)
      (foldCurrent (rest.map Local.toJudgement ++ Ns.map Section3.Judgement.next)))
    (hc : Marker.imp ℓ m = Marker.open → c ∉ R.clocks) :
    ∃ C, canonicalSyntax R (boundaryChildGuards c (Marker.imp ℓ m) G)
        (PendingCollection.collect (.predicate (.upper c m kind I φ) :: .marker ℓ :: .marker ℓ :: rest)) Ns = some C ∧
      StructuralEq (outsidePending G R (boundaryReplacementChild c m ℓ kind I φ Γ)) C ∧
      pendingWeight C ≤ pendingWeight (outsidePending G R (boundaryReplacementChild c m ℓ kind I φ Γ)) := by
  let L : List (Local Clock Var) := .predicate (.upper c m kind I φ) :: .marker ℓ :: .marker ℓ :: rest
  let Body : MixedJ Clock Var := .conj (.predicate (.upper c m kind I φ)) (.conj (.marker ℓ) Γ)
  have hb : foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next) = some Body := by
    simp only [L,List.map_cons,List.cons_append,Local.toJudgement,foldCurrent_cons]
    rw [← hΓ]
    rfl
  obtain ⟨K,hK,hcollect,hw,_,_⟩ := PendingCollection.collect_locals L Ns Body hb
  dsimp only [L] at hK
  have he : StructuralEq (.reset R (boundaryReplacementChild c m ℓ kind I φ Γ))
      (withBoundaryGuard c (Marker.imp ℓ m) (.reset R K)) :=
    ((ACIdem.reset R (child_guard_expose c m ℓ kind I φ Γ)).trans
      (BoundaryGuardScope.extract_boundary_guard R c (Marker.imp ℓ m) Body hc)).trans (by
        cases hg : Marker.imp ℓ m
        · exact .conj (.refl _) (.reset R hcollect)
        · exact .reset R hcollect)
  have hrawWeight : pendingWeight (outsidePending G R (boundaryReplacementChild c m ℓ kind I φ Γ)) = pendingWeight Body := by
    cases hg : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
    | none => simp only [outsidePending,hg,pendingWeight,boundaryReplacementChild,pendingWeight_boundaryGuard,Body]
    | some A => simp only [outsidePending,hg,pendingWeight,guards_weight_zero G A hg,
        Nat.zero_add,boundaryReplacementChild,pendingWeight_boundaryGuard,Body]
  cases hg : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
  | none =>
    cases hm : Marker.imp ℓ m with
    | closed =>
      refine ⟨.reset R K,?_,?_,?_⟩
      · simp only [canonicalSyntax,boundaryChildGuards,hg,hK,Option.map_some,optionalConj]
      · simpa only [outsidePending,hg,hm,withBoundaryGuard] using he
      · simpa only [pendingWeight,hrawWeight] using hw
    | «open» =>
      refine ⟨.conj (.clock c .gt 0) (.reset R K),?_,?_,?_⟩
      · simp only [canonicalSyntax,boundaryChildGuards,List.map_cons,foldCurrent_cons,hg,prependCurrent,hK,Option.map_some,optionalConj]
        rfl
      · simpa only [outsidePending,hg,hm,withBoundaryGuard] using he
      · simpa only [pendingWeight,Nat.zero_add,hrawWeight] using hw
  | some A =>
    cases hm : Marker.imp ℓ m with
    | closed =>
      refine ⟨.conj A (.reset R K),?_,?_,?_⟩
      · simp only [canonicalSyntax,boundaryChildGuards,hg,hK,Option.map_some,optionalConj]
      · simp only [outsidePending,hg]
        exact .conj (.refl _) (by simpa only [hm,withBoundaryGuard] using he)
      · simpa only [pendingWeight,guards_weight_zero G A hg,Nat.zero_add,hrawWeight] using hw
    | «open» =>
      refine ⟨.conj (.conj (.clock c .gt 0) A) (.reset R K),?_,?_,?_⟩
      · simp only [canonicalSyntax,boundaryChildGuards,List.map_cons,foldCurrent_cons,hg,prependCurrent,hK,Option.map_some,optionalConj]
        rfl
      · simp only [outsidePending,hg]
        exact (ACIdem.conj (.refl A) (by simpa only [hm,withBoundaryGuard] using he)).trans
          ((ACIdem.symm (.assoc _ _ _)).trans (.conj (.comm _ _) (.refl _)))
      · simpa only [pendingWeight,guards_weight_zero G A hg,Nat.zero_add,hrawWeight] using hw


private theorem canonical_support
    {R : ClockResetSet Clock} {G : List (Section3.Guard Clock)} {L : List (Local Clock Var)}
    {Ns : List (MixedJ Clock Var)} {C : MixedJ Clock Var} {W : Set Clock}
    (hshape : canonicalSyntax R G L Ns = some C) (hR : R.clocks ⊆ W)
    (hG : ∀g∈G,g.clock ∈ W) (hL : ∀l∈L,syntaxClocks l.toJudgement ⊆ W)
    (hN : ∀K∈Ns,syntaxClocks K ⊆ W) : syntaxClocks C ⊆ W := by
  have hguards : ∀A, foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) = some A → syntaxClocks A ⊆ W := by
    intro A ha
    apply syntaxClocks_foldCurrent_subset ha
    intro K hK
    obtain ⟨g,hg,rfl⟩ := List.mem_map.1 hK
    change {g.clock} ⊆ W
    exact Set.singleton_subset_iff.2 (hG g hg)
  have hbody : ∀B, foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next) = some B → syntaxClocks B ⊆ W := by
    intro B hb
    apply syntaxClocks_foldCurrent_subset hb
    intro K hK
    rcases List.mem_append.1 hK with hK | hK
    · obtain ⟨l,hl,rfl⟩ := List.mem_map.1 hK; exact hL l hl
    · obtain ⟨T,ht,rfl⟩ := List.mem_map.1 hK; exact hN T ht
  cases hg : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) <;>
    cases hb : foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next)
  · simp [canonicalSyntax,hg,hb,optionalConj] at hshape
  · rename_i B
    have he : .reset R B = C := by simpa [canonicalSyntax,hg,hb,optionalConj] using hshape
    subst C
    exact Set.union_subset hR (hbody B hb)
  · rename_i A
    have he : A = C := by simpa [canonicalSyntax,hg,hb,optionalConj] using hshape
    exact he ▸ hguards A hg
  · rename_i A B
    have he : .conj A (.reset R B) = C := by simpa [canonicalSyntax,hg,hb,optionalConj] using hshape
    subst C
    exact Set.union_subset (hguards A hg) (Set.union_subset hR (hbody B hb))

private theorem guard_support {J : MixedJ Clock Var} {g : Section3.Guard Clock}
    (hg : g ∈ currentGuards J) : g.clock ∈ syntaxClocks J := by
  induction J with
  | clock c r a => have he : g = ⟨c,r,a⟩ := hg; subst g; exact rfl
  | conj J K ih ik =>
      rcases hg with hg | hg
      · exact Or.inl (ih hg)
      · exact Or.inr (ik hg)
  | reset R J ih => exact Or.inr (ih hg)
  | terminal | marker | predicate | next => cases hg

private theorem not_mem_removed {α : Type*} (left right : List α) (a : α)
    (h : (left ++ a :: right).Nodup) : a ∉ left ++ right := by
  induction left with
  | nil => exact (List.nodup_cons.mp h).1
  | cons b bs ih =>
      obtain ⟨hb,ht⟩ := List.nodup_cons.mp h
      intro hm
      rcases List.mem_cons.mp hm with he | hm
      · subst b; exact hb (List.mem_append_right _ List.mem_cons_self)
      · exact ih ht hm

/-- Actual ownership after boundary replacement. The exact old future list is
retained; the new guard is outside R, without a disjointness demand on old guards. -/
theorem construct_boundary_child_owned_core
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (hNext : NextPrivate J) (required : Bool)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (left right rest : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate (.bounded c d m (¬ₘ ℓ) kind I φ) :: right)
    (hselection : (left ++ right).Perm (if required then
      .predicate (.plain (timedFormula kind I φ)) :: .marker ℓ :: rest else .marker ℓ :: rest))
    (Γ : MixedJ Clock Var) (hΓ : Γ = prependCurrent (.marker ℓ)
      (foldCurrent (rest.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next)))
    (Rc : ClockResetSet Clock) (Gbase : List (Section3.Guard Clock))
    (hRcBudget : Rc.clocks ⊆ W) (hGbaseBudget : ∀g∈Gbase,g.clock ∈ W)
    (hc : Marker.imp ℓ m = Marker.open → c ∉ Rc.clocks) :
    ∃ child : OwnedPending (outsidePending Gbase Rc (boundaryReplacementChild c m ℓ kind I φ Γ)) Rc W,
      child.guards = boundaryChildGuards c (Marker.imp ℓ m) Gbase ∧
      child.locals = PendingCollection.collect (.predicate (.upper c m kind I φ) :: .marker ℓ :: .marker ℓ :: rest) ∧
      child.nextInputs = owned.nextInputs ∧
      currentGuards child.canonical = {g | g ∈ boundaryChildGuards c (Marker.imp ℓ m) Gbase} ∧
      NextPrivate (outsidePending Gbase Rc (boundaryReplacementChild c m ℓ kind I φ Γ)) := by
  let L : List (Local Clock Var) := .predicate (.upper c m kind I φ) :: .marker ℓ :: .marker ℓ :: rest
  let G := boundaryChildGuards c (Marker.imp ℓ m) Gbase
  let Raw := outsidePending Gbase Rc (boundaryReplacementChild c m ℓ kind I φ Γ)
  obtain ⟨C,hC,hstruct,hweight⟩ := assemble_boundary_child Rc Gbase c m ℓ kind I φ rest owned.nextInputs Γ hΓ hc
  have hp : Local.predicate (.bounded c d m (¬ₘ ℓ) kind I φ) ∈ owned.locals := by rw [hsplit]; simp
  have hsubremoved : ∀l∈left ++ right,l ∈ owned.locals := by
    intro l hl
    rw [hsplit]
    simp only [List.mem_append,List.mem_cons] at hl ⊢
    tauto
  have hrest : ∀l∈rest,l ∈ left ++ right := by
    intro l hl
    apply hselection.mem_iff.2
    cases required <;> simp [hl]
  have hnot := not_mem_removed left right (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ)) (hsplit ▸ owned.locals_nodup)
  have hboundSupport : syntaxClocks (.predicate (.upper c m kind I φ)) ⊆
      syntaxClocks (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ)) := Set.singleton_subset_iff.2 (Or.inl rfl)
  have hnew : ∀p, Local.predicate p ∈ PendingCollection.collect L ↔ p = .upper c m kind I φ ∨ Local.predicate p ∈ rest := by
    intro p
    simp [L,PendingCollection.mem_collect]
  have hprivate : privateCurrent (PendingCollection.collect L) := by
    intro p q hp' hq' hpq
    rcases (hnew p).1 hp' with rfl | hp' <;> rcases (hnew q).1 hq' with rfl | hq'
    · exact False.elim (hpq rfl)
    · exact (owned.private_sources _ q hp (hsubremoved _ (hrest _ hq'))
        (fun he => hnot (he ▸ hrest _ hq'))).mono_left hboundSupport
    · exact ((owned.private_sources _ p hp (hsubremoved _ (hrest _ hp'))
        (fun he => hnot (he ▸ hrest _ hp'))).mono_left hboundSupport).symm
    · exact owned.private_sources p q (hsubremoved _ (hrest _ hp')) (hsubremoved _ (hrest _ hq')) hpq
  have hsourceNext : currentNextSeparate (PendingCollection.collect L) owned.nextInputs := by
    intro p K hpl hK
    rcases (hnew p).1 hpl with rfl | hpl
    · exact (owned.source_next _ K hp hK).mono_left hboundSupport
    · exact owned.source_next p K (hsubremoved _ (hrest _ hpl)) hK
  have hnextSafe : ∀K∈owned.nextInputs,∃N,SafeNormalization K (Section3.TransitionForm.ofState N) := by
    intro K hK
    obtain ⟨F,hF⟩ := owned.input_safe
    exact canonical_payload_safe owned.shape hF hK
  obtain ⟨F,hF⟩ := CanonicalSafety.exists_safe_canonical Rc G (PendingCollection.collect L) owned.nextInputs C hC hnextSafe owned.next_private
  have hR : Rc.clocks ⊆ W := hRcBudget
  have hlocal : ∀l∈owned.locals,syntaxClocks l.toJudgement ⊆ W := by
    intro l hl
    exact (canonical_local_support owned.shape hl).trans (fun _ hx => owned.covers_input (Or.inl (Or.inr hx)))
  have hcW : c ∈ W := hlocal _ hp (by exact Or.inl rfl)
  have hguards : ∀g∈Gbase,g.clock ∈ W := hGbaseBudget
  have hnewguards : ∀g∈G,g.clock ∈ W := by
    intro g hg
    cases hm : Marker.imp ℓ m <;> simp only [G,boundaryChildGuards,hm,List.mem_cons] at hg
    · rcases hg with rfl | hg
      · exact hcW
      · exact hguards g hg
    · exact hguards g hg
  have hnewlocals : ∀l∈PendingCollection.collect L,syntaxClocks l.toJudgement ⊆ W := by
    intro l hl
    have hm := (PendingCollection.mem_collect L l).1 hl
    simp only [L,List.mem_cons] at hm
    rcases hm with rfl | rfl | rfl | hm
    · exact hboundSupport.trans (hlocal _ hp)
    · exact Set.empty_subset _
    · exact Set.empty_subset _
    · exact hlocal l (hsubremoved _ (hrest _ hm))
  have hnextBudget : ∀K∈owned.nextInputs,syntaxClocks K ⊆ W := by
    intro K hK
    exact (canonical_payload_support owned.shape hK).trans (fun _ hx => owned.covers_input (Or.inl (Or.inr hx)))
  have hCBudget := canonical_support hC hR hnewguards hnewlocals hnextBudget
  have hΓBudget : syntaxClocks Γ ⊆ W := by
    rw [hΓ]
    cases ht : foldCurrent (rest.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next) with
    | none => exact Set.empty_subset _
    | some T =>
      change ∅ ∪ syntaxClocks T ⊆ W
      apply Set.union_subset (Set.empty_subset _)
      apply syntaxClocks_foldCurrent_subset ht
      intro K hK
      rcases List.mem_append.1 hK with hK | hK
      · obtain ⟨l,hl,rfl⟩ := List.mem_map.1 hK; exact hlocal l (hsubremoved _ (hrest _ hl))
      · obtain ⟨K0,hK0,rfl⟩ := List.mem_map.1 hK; exact hnextBudget K0 hK0
  have hChildBudget : syntaxClocks (boundaryReplacementChild c m ℓ kind I φ Γ) ⊆ W := by
    cases hm : Marker.imp ℓ m <;>
      simp only [boundaryReplacementChild,withBoundaryGuard,hm,syntaxClocks,Set.empty_union] <;>
      exact Set.union_subset (Set.singleton_subset_iff.2 hcW)
        (by first | exact hΓBudget | exact Set.union_subset (Set.singleton_subset_iff.2 hcW) hΓBudget)
  have hRawBudget : syntaxClocks Raw ⊆ W := by
    dsimp only [Raw,outsidePending]
    cases hg : foldCurrent (Gbase.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
    | none => exact Set.union_subset hR hChildBudget
    | some A =>
      change syntaxClocks A ∪ (Rc.clocks ∪ syntaxClocks _) ⊆ W
      apply Set.union_subset _ (Set.union_subset hR hChildBudget)
      apply syntaxClocks_foldCurrent_subset hg
      intro K hK
      obtain ⟨g,hg,rfl⟩ := List.mem_map.1 hK
      exact Set.singleton_subset_iff.2 (hguards g hg)
  let child : OwnedPending Raw Rc W := {
    guards := G, locals := PendingCollection.collect L, nextInputs := owned.nextInputs,
    canonical := C, shape := hC, regroup := hstruct, regroup_nonincrease := hweight,
    locals_nodup := PendingCollection.collect_nodup L, private_sources := hprivate,
    source_next := hsourceNext, next_private := owned.next_private, next_flat := owned.next_flat,
    absent_body_reset := by
      intro he
      have hm : Local.predicate (.upper c m kind I φ) ∈ PendingCollection.collect L :=
        (hnew _).2 (Or.inl rfl)
      rw [he] at hm
      cases hm
    input_safe := ⟨F,hF⟩, finite_budget := owned.finite_budget,
    covers_input := Set.union_subset (Set.union_subset hRawBudget hCBudget) hR }
  refine ⟨child,rfl,rfl,rfl,canonical_currentGuards hC,?_⟩
  apply hstruct.nextPrivate_iff.2
  rw [canonical_nextPrivate_iff hC]
  exact (canonical_nextPrivate_iff owned.shape).1 (owned.regroup.nextPrivate_iff.1 hNext)


theorem construct_boundary_child_owned
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (hNext : NextPrivate J) (required : Bool)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (left right rest : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate (.bounded c d m (¬ₘ ℓ) kind I φ) :: right)
    (hselection : (left ++ right).Perm (if required then
      .predicate (.plain (timedFormula kind I φ)) :: .marker ℓ :: rest else .marker ℓ :: rest))
    (Γ : MixedJ Clock Var) (hΓ : Γ = prependCurrent (.marker ℓ)
      (foldCurrent (rest.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next)))
    (hc : Marker.imp ℓ m = Marker.open → c ∉ R.clocks) :
    ∃ child : OwnedPending (outsidePending owned.guards R (boundaryReplacementChild c m ℓ kind I φ Γ)) R W,
      child.guards = boundaryChildGuards c (Marker.imp ℓ m) owned.guards ∧
      child.locals = PendingCollection.collect (.predicate (.upper c m kind I φ) :: .marker ℓ :: .marker ℓ :: rest) ∧
      child.nextInputs = owned.nextInputs ∧
      currentGuards child.canonical = {g | g ∈ boundaryChildGuards c (Marker.imp ℓ m) owned.guards} ∧
      NextPrivate (outsidePending owned.guards R (boundaryReplacementChild c m ℓ kind I φ Γ)) := by
  apply construct_boundary_child_owned_core owned hNext required c d m ℓ kind I φ left right rest hsplit hselection Γ hΓ R owned.guards
  · exact fun _ hx => owned.covers_input (Or.inr hx)
  · intro g hg
    have hm : g ∈ currentGuards owned.canonical := by rw [canonical_currentGuards owned.shape]; exact hg
    exact owned.covers_input (Or.inl (Or.inr (guard_support hm)))
  · exact hc

private theorem fold_weight_sum (Js : List (MixedJ Clock Var)) :
    optionalWeight (foldCurrent Js) = (Js.map pendingWeight).sum := by
  induction Js with
  | nil => rfl
  | cons K Ks ih =>
      cases ht : foldCurrent Ks with
      | none =>
          have hz : (Ks.map pendingWeight).sum = 0 := by simpa only [ht,optionalWeight] using ih.symm
          simp [foldCurrent,ht,optionalConj,optionalWeight,hz]
      | some T =>
          have he : pendingWeight T = (Ks.map pendingWeight).sum := by simpa only [ht,optionalWeight] using ih
          simp [foldCurrent,ht,optionalConj,optionalWeight,pendingWeight,he]

private theorem canonical_local_weight
    {R : ClockResetSet Clock} {G : List (Section3.Guard Clock)} {L : List (Local Clock Var)}
    {Ns : List (MixedJ Clock Var)} {C B : MixedJ Clock Var}
    (hs : canonicalSyntax R G L Ns = some C)
    (hb : foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next) = some B) :
    pendingWeight C = (L.map (fun l => pendingWeight l.toJudgement)).sum := by
  rw [canonical_weight hs hb]
  have he := fold_weight_sum (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next)
  rw [hb] at he
  simpa [optionalWeight,List.map_append,List.map_map,Function.comp_def,pendingWeight] using he

/-- Exposing the inputs to a boundary replacement preserves pending weight.
Duplicating the marker adds no weight. -/
theorem boundary_exposure_weight [DecidableEq Clock]
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (required : Bool)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (left right rest : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate (.bounded c d m (¬ₘ ℓ) kind I φ) :: right)
    (hselection : (left ++ right).Perm (if required then
      .predicate (.plain (timedFormula kind I φ)) :: .marker ℓ :: rest else .marker ℓ :: rest))
    (Γ : MixedJ Clock Var) (hΓ : Γ = prependCurrent (.marker ℓ)
      (foldCurrent (rest.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next))) :
    pendingWeight owned.canonical = pendingWeight (boundaryReplacementInput required c d m ℓ kind I φ Γ) := by
  obtain ⟨Body,hBody,_⟩ := owned_selected_exposure owned _ left right hsplit
  have hOld := canonical_local_weight owned.shape hBody
  have hperm := (hselection.map (fun l => pendingWeight l.toJudgement)).sum_eq
  have hΓWeight : pendingWeight Γ = (rest.map (fun l => pendingWeight l.toJudgement)).sum := by
    have he := fold_weight_sum (rest.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next)
    have hs : optionalWeight (foldCurrent (rest.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next)) =
        (rest.map (fun l => pendingWeight l.toJudgement)).sum := by
      simpa [List.map_append,List.map_map,Function.comp_def,pendingWeight] using he
    rw [hΓ]
    cases ht : foldCurrent (rest.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next) <;>
      simpa only [ht,prependCurrent,pendingWeight,optionalWeight,Nat.zero_add] using hs
  rw [hOld,hsplit]
  simp only [List.map_append,List.map_cons,List.sum_append,List.sum_cons] at hperm ⊢
  cases required <;>
    simp only [Bool.false_eq_true,eq_self,ite_false,ite_true,List.map_cons,List.sum_cons,
      Local.toJudgement,pendingWeight,Nat.zero_add] at hperm <;>
    simp only [boundaryReplacementInput,Bool.false_eq_true,eq_self,ite_false,ite_true,pendingWeight,hΓWeight,Local.toJudgement,Nat.zero_add] <;>
    omega

theorem outsidePending_weight (G : List (Section3.Guard Clock)) (R : ClockResetSet Clock)
    (K : MixedJ Clock Var) : pendingWeight (outsidePending G R K) = pendingWeight K := by
  cases hg : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
  | none => simp only [outsidePending,hg,pendingWeight]
  | some A => simp only [outsidePending,hg,pendingWeight,guards_weight_zero G A hg,Nat.zero_add]

/-- Optional replacement is potential-preserving before collection. -/
theorem optional_boundary_child_weight [DecidableEq Clock]
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (left right rest : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate (.bounded c d m (¬ₘ ℓ) kind I φ) :: right)
    (hselection : (left ++ right).Perm (.marker ℓ :: rest))
    (Γ : MixedJ Clock Var) (hΓ : Γ = prependCurrent (.marker ℓ)
      (foldCurrent (rest.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next))) :
    pendingWeight (outsidePending owned.guards R (boundaryReplacementChild c m ℓ kind I φ Γ)) =
      pendingWeight owned.canonical := by
  rw [outsidePending_weight,boundary_exposure_weight owned false c d m ℓ kind I φ left right rest hsplit hselection Γ hΓ]
  exact optional_boundary_weight_eq R c d m ℓ kind I φ Γ

/-- Required replacement strictly decreases potential before collection. -/
theorem required_boundary_child_weight [DecidableEq Clock]
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (left right rest : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate (.bounded c d m (¬ₘ ℓ) kind I φ) :: right)
    (hselection : (left ++ right).Perm (.predicate (.plain (timedFormula kind I φ)) :: .marker ℓ :: rest))
    (Γ : MixedJ Clock Var) (hΓ : Γ = prependCurrent (.marker ℓ)
      (foldCurrent (rest.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next))) :
    pendingWeight (outsidePending owned.guards R (boundaryReplacementChild c m ℓ kind I φ Γ)) <
      pendingWeight owned.canonical := by
  rw [outsidePending_weight,boundary_exposure_weight owned true c d m ℓ kind I φ left right rest hsplit hselection Γ hΓ]
  exact required_boundary_weight_lt R c d m ℓ kind I φ Γ


@[simp] theorem boundaryChildGuards_set (c : Clock) (b : Marker) (G : List (Section3.Guard Clock)) :
    {g | g ∈ boundaryChildGuards c b G} =
      (if b = Marker.open then {⟨c,.gt,0⟩} else ∅) ∪ {g | g ∈ G} := by
  cases b <;> ext g <;> simp [boundaryChildGuards]

/-- Replacing the selected bounded owner by its upper subset does not enlarge
active support. This concerns active protection, not fixed guard support. -/
theorem boundary_child_activeSupport_subset
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (required : Bool)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (left right rest : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate (.bounded c d m (¬ₘ ℓ) kind I φ) :: right)
    (hselection : (left ++ right).Perm (if required then
      .predicate (.plain (timedFormula kind I φ)) :: .marker ℓ :: rest else .marker ℓ :: rest)) :
    activeSupport (PendingCollection.collect (.predicate (.upper c m kind I φ) :: .marker ℓ :: .marker ℓ :: rest)) ⊆
      activeSupport owned.locals := by
  intro x hx
  obtain ⟨p,hp,hx⟩ := hx
  have hm := (PendingCollection.mem_collect _ _).1 hp
  simp only [List.mem_cons,Local.predicate.injEq,reduceCtorEq,false_or] at hm
  rcases hm with rfl | hp
  · refine ⟨.bounded c d m (¬ₘ ℓ) kind I φ,?_,?_⟩
    · rw [hsplit]; simp
    · exact Or.inl hx
  · have hrest : Local.predicate p ∈ left ++ right := by
      apply hselection.mem_iff.2
      cases required <;> simp [hp]
    refine ⟨p,?_,hx⟩
    rw [hsplit]
    simp only [List.mem_append,List.mem_cons] at hrest ⊢
    tauto

theorem boundary_child_protected
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (A : Set Clock) (hprotected : protectedActive owned A)
    (required : Bool) (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (left right rest : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate (.bounded c d m (¬ₘ ℓ) kind I φ) :: right)
    (hselection : (left ++ right).Perm (if required then
      .predicate (.plain (timedFormula kind I φ)) :: .marker ℓ :: rest else .marker ℓ :: rest))
    {Jc : MixedJ Clock Var} {Rc : ClockResetSet Clock} {Wc : Set Clock}
    (child : OwnedPending Jc Rc Wc)
    (hlocal : child.locals = PendingCollection.collect (.predicate (.upper c m kind I φ) :: .marker ℓ :: .marker ℓ :: rest)) :
    protectedActive child A := by
  change Disjoint (activeSupport child.locals) A
  rw [hlocal]
  exact hprotected.mono_left (boundary_child_activeSupport_subset owned required c d m ℓ kind I φ left right rest hsplit hselection)


/-- Collected canonical children never increase old potential; required
replacement strictly decreases it. Optional replacement alone need not. -/
theorem boundary_child_weight_compare [DecidableEq Clock]
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (required : Bool)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (left right rest : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate (.bounded c d m (¬ₘ ℓ) kind I φ) :: right)
    (hselection : (left ++ right).Perm (if required then
      .predicate (.plain (timedFormula kind I φ)) :: .marker ℓ :: rest else .marker ℓ :: rest))
    (Γ : MixedJ Clock Var) (hΓ : Γ = prependCurrent (.marker ℓ)
      (foldCurrent (rest.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next)))
    (child : OwnedPending (outsidePending owned.guards R (boundaryReplacementChild c m ℓ kind I φ Γ)) R W) :
    pendingWeight child.canonical ≤ pendingWeight owned.canonical ∧
      (required = true → pendingWeight child.canonical < pendingWeight owned.canonical) := by
  cases required with
  | false =>
      have he := optional_boundary_child_weight owned c d m ℓ kind I φ left right rest hsplit hselection Γ hΓ
      exact ⟨child.regroup_nonincrease.trans_eq he,by intro h; cases h⟩
  | true =>
      have he := required_boundary_child_weight owned c d m ℓ kind I φ left right rest hsplit hselection Γ hΓ
      have hlt := lt_of_le_of_lt child.regroup_nonincrease he
      exact ⟨hlt.le,fun _ => hlt⟩

end STLTableau.Section4.Finiteness
