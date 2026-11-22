import STLTableaux.Finiteness.Derivation.DerivationNormalizationSoundness
import STLTableaux.Closure.Support.BranchFreeClocks
import STLTableaux.Closure.Subsumption.FaithfulClosureOrder

/-! Free-clock bounds for selected finite resolutions and safe normalization.
Arbitrary Derives.original closures are deliberately not covered. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*}

 theorem ACIdem.freeClocks_eq {J K : MixedJ Clock Var} (h : StructuralEq J K) :
    J.freeClocks = K.freeClocks := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig
  | assoc => exact Set.union_assoc _ _ _
  | comm => exact Set.union_comm _ _
  | idem => exact Set.union_self _
  | conj h g ih ig => exact congrArg₂ Set.union ih ig
  | reset R h ih => exact congrArg (fun A => A \ R.clocks) ih
  | resetDistrib R J K =>
    ext c
    simp only [Section3.Judgement.freeClocks,Set.mem_sdiff,Set.mem_union]
    tauto
  | resetUnused R J hd =>
    ext c
    constructor
    · exact fun hc => hc.1
    · exact fun hc => ⟨hc,fun hr => Set.disjoint_left.1 hd hr hc⟩
  | resetNested R S J =>
    ext c
    simp only [Section3.Judgement.freeClocks,ClockResetSet.clocks_union,Set.mem_sdiff,Set.mem_union]
    tauto

set_option maxHeartbeats 12000000 in
set_option linter.unusedSimpArgs false in
 theorem RawBranch.freeClocks_subset [DecidableEq Clock] {p : Predicate Clock Var}
    {B : MixedJ Clock Var} (h : RawBranch p B) : B.freeClocks ⊆ (.predicate p : MixedJ Clock Var).freeClocks := by
  cases h with
  | finite hr hb =>
    (cases hr <;>
      simp only [ExpansionRule.plainAnd,ExpansionRule.plainOr,ExpansionRule.plainUntil,
        ExpansionRule.plainRelease,ExpansionRule.openEventually,ExpansionRule.openAlways,
        ExpansionRule.upperAlways,ExpansionRule.boundedAlways,ExpansionRule.upperEventually,
        ExpansionRule.boundedEventually,List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hb <;>
      (try split_ifs at hb) <;>
      (try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hb) <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      (try simp only [ExpansionRule.upperAlways_defer,ExpansionRule.upperAlways_check,
        ExpansionRule.boundedAlways_defer,ExpansionRule.boundedAlways_check,ExpansionRule.boundedAlways_finish,
        ExpansionRule.upperEventually_defer,ExpansionRule.upperEventually_check,
        ExpansionRule.boundedEventually_defer,ExpansionRule.boundedEventually_check,
        ExpansionRule.boundedEventually_finish])
    all_goals simp [STLTableau.Judgement.markedLT_eq_clock,STLTableau.Judgement.markedGT_eq_clock,
      Section3.Judgement.ofFinite,Section3.Predicate.ofFinite,Section3.Judgement.freeClocks,
      ClockResetSet.clocks_singleton,ClockResetSet.clocks_union,Set.subset_def]
  | infinite hr hb =>
    (cases hr <;>
      simp only [UnboundedClocked.upperAlwaysBranches,UnboundedClocked.boundedAlwaysBranches,
        UnboundedClocked.upperEventuallyBranches,UnboundedClocked.boundedEventuallyBranches,
        List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hb <;>
      (try split_ifs at hb) <;>
      (try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hb) <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl) <;>
      (try simp only [UnboundedClocked.upperAlwaysDefer,UnboundedClocked.upperAlwaysCheck,
        UnboundedClocked.boundedAlwaysDefer,UnboundedClocked.boundedAlwaysCheck,
        UnboundedClocked.alwaysWait,UnboundedClocked.alwaysLast,
        UnboundedClocked.upperEventuallyDefer,UnboundedClocked.upperEventuallyCheck,
        UnboundedClocked.boundedEventuallyDefer,UnboundedClocked.boundedEventuallyCheck,
        UnboundedClocked.boundedEventuallyFinish,UnboundedClocked.Node.lt,UnboundedClocked.Node.gt])
    all_goals simp [Section3.Judgement.ofUnbounded,Section3.Predicate.ofUnbounded,
      Section3.Judgement.freeClocks,ClockResetSet.clocks_singleton,ClockResetSet.clocks_union,
      Set.subset_def]
  | opening c m kind a φ =>
    simp [UnboundedClocked.opening,Section3.Judgement.ofUnbounded,Section3.Predicate.ofUnbounded,
      Section3.Judgement.freeClocks,ClockResetSet.clocks_singleton]

private theorem boundary_free [DecidableEq Clock] (c d : Clock) (m ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) (Γ : MixedJ Clock Var)
    (hcd : c ≠ d) (hdΓ : d ∉ Γ.freeClocks) :
    (.conj (.predicate (.upper c m kind I φ))
      (.conj (.marker ℓ) (withBoundaryGuard c (Marker.imp ℓ m) Γ)) : MixedJ Clock Var).freeClocks ⊆
    (.reset (ClockResetSet.singleton d 0) (.conj (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ))
      (.conj (.marker ℓ) Γ)) : MixedJ Clock Var).freeClocks := by
  cases hb : Marker.imp ℓ m <;>
    simp [withBoundaryGuard,Section3.Judgement.freeClocks,ClockResetSet.clocks_singleton,
      Set.subset_def] <;> aesop

/-- Both retained full output and erased leaves introduce no free input name. -/
theorem Resolve.freeClocks_outputs [DecidableEq Clock] {J H A : MixedJ Clock Var}
    (D : Resolve J H A) : H.freeClocks ⊆ J.freeClocks ∧ A.freeClocks ⊆ J.freeClocks := by
  induction D with
  | leaf => exact ⟨Set.Subset.refl _,Set.Subset.refl _⟩
  | conj D E ih ig => exact ⟨Set.union_subset_union ih.1 ig.1,Set.union_subset_union ih.2 ig.2⟩
  | reset R D ih =>
    exact ⟨fun c hc => ⟨ih.1 hc.1,hc.2⟩,fun c hc => ⟨ih.2 hc.1,hc.2⟩⟩
  | structural h D ih => rw [h.freeClocks_eq]; exact ih
  | @expandCtx p B Γ H A raw hp fresh D ih =>
    have hs := Set.union_subset_union raw.freeClocks_subset (Set.Subset.refl Γ.freeClocks)
    exact ⟨Set.union_subset Set.subset_union_left (ih.1.trans hs),ih.2.trans hs⟩
  | expandSolo raw hp fresh D ih =>
    exact ⟨Set.union_subset (Set.Subset.refl _) (ih.1.trans raw.freeClocks_subset),
      ih.2.trans raw.freeClocks_subset⟩
  | @boundaryRequired c d m ℓ kind I φ Γ H A frozen hdΓ D ih =>
    have hs := boundary_free c d m ℓ kind I φ Γ frozen.distinct hdΓ
    have hfull : _ := ih.1.trans hs
    have hat : _ := ih.2.trans hs
    simpa only [Section3.Judgement.freeClocks,Set.union_empty] using And.intro hfull hat
  | @boundaryOptional c d m ℓ kind I φ Γ H A frozen hdΓ D ih =>
    have hs := boundary_free c d m ℓ kind I φ Γ frozen.distinct hdΓ
    exact ⟨ih.1.trans hs,ih.2.trans hs⟩
  | @unusedReset J H A d v hdJ hdH D ih =>
    have hd : Disjoint (ClockResetSet.singleton d v).clocks J.freeClocks := by
      rw [ClockResetSet.clocks_singleton]
      apply Set.disjoint_left.mpr
      intro c hc hJ
      have he : c = d := hc
      exact hdJ (he ▸ hJ)
    rw [(ACIdem.resetUnused (ClockResetSet.singleton d v) J hd).freeClocks_eq]
    exact ih

 theorem Resolve.freeClocks_subset [DecidableEq Clock] {J H A : MixedJ Clock Var}
    (D : Resolve J H A) : H.freeClocks ⊆ J.freeClocks := D.freeClocks_outputs.1

 theorem Resolve.erased_freeClocks_subset [DecidableEq Clock] {J H A : MixedJ Clock Var}
    (D : Resolve J H A) : A.freeClocks ⊆ J.freeClocks := D.freeClocks_outputs.2

private theorem empty_clocks : (ClockResetSet.empty : ClockResetSet Clock).clocks = ∅ := by
  ext c
  constructor
  · rintro ⟨a,h⟩; cases h
  · intro h; cases h

private theorem reset_free_subset (F : Section3.TransitionForm Clock Var) (R : ClockResetSet Clock)
    (hd : Disjoint R.clocks F.current.guardClocks) :
    (F.underReset R).freeClocks ⊆ F.freeClocks \ R.clocks := by
  intro c hc
  have he : (F.underReset R).freeClocks = F.current.guardClocks ∪
      (F.bodyFreeClocks \ (F.current.resets.clocks ∪ R.clocks)) := by
    simp only [Section3.TransitionForm.freeClocks,Section3.TransitionForm.underReset,
      Section3.TransitionForm.bodyFreeClocks,ClockResetSet.clocks_union,
      Section3.StateForm.guardClocks,Section3.StateForm.localClocks]
  rw [he] at hc
  rcases hc with hg | ⟨hb,hr⟩
  · exact ⟨Or.inl hg,fun hcR => Set.disjoint_left.1 hd hcR hg⟩
  · exact ⟨Or.inr ⟨hb,fun h => hr (Or.inl h)⟩,fun h => hr (Or.inr h)⟩

private theorem local_form_free (l : Local Clock Var) :
    (Section3.TransitionForm.ofState (Section3.StateForm.ofLocal l)).freeClocks = l.freeClocks := by
  simp [Section3.TransitionForm.ofState,Section3.TransitionForm.freeClocks,
    Section3.TransitionForm.bodyFreeClocks,Section3.StateForm.ofLocal,
    Section3.StateForm.guardClocks,Section3.StateForm.localClocks,empty_clocks]

 theorem SafeNormalization.freeClocks_subset {J : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : SafeNormalization J F) : F.freeClocks ⊆ J.freeClocks := by
  induction h with
  | terminal => rw [local_form_free]; exact Set.Subset.refl _
  | clock => simp [Section3.TransitionForm.ofState,Section3.TransitionForm.freeClocks,
      Section3.TransitionForm.bodyFreeClocks,Section3.StateForm.ofGuard,
      Section3.StateForm.guardClocks,Section3.StateForm.localClocks,Section3.Judgement.freeClocks,empty_clocks]
  | marker => rw [local_form_free]; exact Set.Subset.refl _
  | predicate => rw [local_form_free]; exact Set.Subset.refl _
  | conj h g hc ih ig =>
    exact (Section3.TransitionForm.freeClocks_union_subset _ _).trans (Set.union_subset_union ih ig)
  | reset R h hd ih =>
    exact (reset_free_subset _ R hd).trans (fun c hc => ⟨ih hc.1,hc.2⟩)
  | @next J F h hn ih =>
    have he : (Section3.TransitionForm.ofNextState F.current).freeClocks = F.freeClocks := by
      simp [Section3.TransitionForm.ofNextState,Section3.TransitionForm.freeClocks,
        Section3.TransitionForm.bodyFreeClocks,Section3.StateForm.empty,
        Section3.StateForm.freeClocks,Section3.StateForm.guardClocks,Section3.StateForm.localClocks,
        hn,empty_clocks]
    rw [he]
    exact ih

private theorem subsumed_free_subset {F G : Section3.TransitionForm Clock Var}
    (h : Section3.SyntacticallySubsumed F G) : F.freeClocks ⊆ G.freeClocks := by
  intro c hc
  rcases hc with ⟨g,hg,he⟩ | hb
  · exact Or.inl ⟨g,h.current.guards hg,he⟩
  · exact Or.inr (h.unboundBody_mono hb)

private theorem union_free_eq {F G : Section3.TransitionForm Clock Var}
    (h : F.UnionCompatible G) : (F.union G).freeClocks = F.freeClocks ∪ G.freeClocks :=
  Set.Subset.antisymm (Section3.TransitionForm.freeClocks_union_subset F G)
    (Set.union_subset (subsumed_free_subset h.left) (subsumed_free_subset h.right))

private theorem reset_free_eq (F : Section3.TransitionForm Clock Var) (R : ClockResetSet Clock)
    (hd : Disjoint R.clocks F.current.guardClocks) :
    (F.underReset R).freeClocks = F.freeClocks \ R.clocks := by
  apply Set.Subset.antisymm (reset_free_subset F R hd)
  intro c hc
  change c ∈ F.current.guardClocks ∪ (F.bodyFreeClocks \ (F.current.resets.union R).clocks)
  rcases hc.1 with hg | ⟨hb,hn⟩
  · exact Or.inl hg
  · refine Or.inr ⟨hb,?_⟩
    rw [ClockResetSet.clocks_union]
    exact fun hr => hr.elim hn hc.2

/-- Safety reflects free support as well as preserving it. In conjunctions,
actual no-capture compatibility is essential for the reverse inclusion. -/
theorem SafeNormalization.freeClocks_eq {J : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : SafeNormalization J F) : F.freeClocks = J.freeClocks := by
  induction h with
  | terminal => exact local_form_free _
  | clock => simp [Section3.TransitionForm.ofState,Section3.TransitionForm.freeClocks,
      Section3.TransitionForm.bodyFreeClocks,Section3.StateForm.ofGuard,
      Section3.StateForm.guardClocks,Section3.StateForm.localClocks,Section3.Judgement.freeClocks,empty_clocks]
  | marker => exact local_form_free _
  | predicate => exact local_form_free _
  | conj h g hc ih ig => exact (union_free_eq hc).trans (congrArg₂ Set.union ih ig)
  | reset R h hd ih => exact (reset_free_eq _ R hd).trans (congrArg (fun A => A \ R.clocks) ih)
  | @next J F h hn ih =>
    have he : (Section3.TransitionForm.ofNextState F.current).freeClocks = F.freeClocks := by
      simp [Section3.TransitionForm.ofNextState,Section3.TransitionForm.freeClocks,
        Section3.TransitionForm.bodyFreeClocks,Section3.StateForm.empty,
        Section3.StateForm.freeClocks,Section3.StateForm.guardClocks,Section3.StateForm.localClocks,
        hn,empty_clocks]
    exact he.trans ih

/-- The selected resolved output has no free names beyond its normalized input.
This does not assert a bound for arbitrary original-closure graph admission. -/
theorem selected_resolution_free_subset [DecidableEq Clock]
    {J H A : MixedJ Clock Var} {N : Section3.StateForm Clock Var}
    {F : Section3.TransitionForm Clock Var} (D : Resolve J H A)
    (hInput : SafeNormalization J (.ofState N)) (hFull : SafeNormalization H F) :
    F.freeClocks ⊆ N.freeClocks := by
  have hs := hFull.freeClocks_subset.trans D.freeClocks_subset
  rw [← hInput.freeClocks_eq] at hs
  simpa only [Section3.TransitionForm.ofState,Section3.TransitionForm.freeClocks,
    Section3.TransitionForm.bodyFreeClocks,Set.union_empty,Section3.StateForm.freeClocks] using hs

end STLTableau.Section4.Finiteness
