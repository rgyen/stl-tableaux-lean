import STLTableaux.Closure.Subsumption.FaithfulClosureOrder

/-! A proof-only restriction removing components that read clocks outside a
given support. Resets are retained. This does not modify the tableau graph. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}

def StateForm.restrictFree (S : StateForm Clock Var) (A : Set Clock) : StateForm Clock Var where
  guards := {g ∈ S.guards | g.clock ∈ A}
  guards_finite := S.guards_finite.subset (fun _ h => h.1)
  resets := S.resets
  locals := {l ∈ S.locals | l.freeClocks ⊆ A ∪ S.resets.clocks}
  locals_finite := S.locals_finite.subset (fun _ h => h.1)

theorem StateForm.restrictFree_freeClocks_subset (S : StateForm Clock Var) (A : Set Clock) :
    (S.restrictFree A).freeClocks ⊆ A := by
  rintro c (⟨g, hg, rfl⟩ | ⟨⟨l, hl, hc⟩, hn⟩)
  · exact hg.2
  · exact (hl.2 hc).resolve_right hn

theorem StateForm.restrictFree_components (S : StateForm Clock Var) (A : Set Clock) :
    ComponentsIncluded (S.restrictFree A) S :=
  ⟨fun _ h => h.1, fun _ _ h => h, fun _ h => h.1⟩

/-- Current locals may read outer-reset clocks, while next-state guards also
see those outer-reset clocks. Next-state resets bind only their own locals. -/
def TransitionForm.restrictFree (F : TransitionForm Clock Var) (A : Set Clock) :
    TransitionForm Clock Var where
  current := F.current.restrictFree A
  nextPart := F.nextPart.map (fun N => N.restrictFree (A ∪ F.current.resets.clocks))

theorem TransitionForm.restrictFree_freeClocks_subset
    (F : TransitionForm Clock Var) (A : Set Clock) :
    (F.restrictFree A).freeClocks ⊆ A := by
  intro c hc
  rcases hc with ⟨g, hg, he⟩ | ⟨hc, hn⟩
  · exact he ▸ hg.2
  · rcases hc with ⟨l, hl, hc⟩ | hc
    · exact (hl.2 hc).resolve_right hn
    · cases hnext : F.nextPart with
      | none =>
        simp only [restrictFree, hnext, Option.map_none, Set.mem_empty_iff_false] at hc
      | some N =>
        change c ∈ (match (F.restrictFree A).nextPart with
          | none => ∅ | some M => M.freeClocks) at hc
        simp only [restrictFree, hnext, Option.map_some] at hc
        exact (N.restrictFree_freeClocks_subset _ hc).resolve_right hn

theorem TransitionForm.restrictFree_subsumed
    (F : TransitionForm Clock Var) (A : Set Clock) :
    SyntacticallySubsumed (F.restrictFree A) F := by
  refine ⟨F.current.restrictFree_components A, ?_, ?_⟩
  · exact Set.disjoint_left.mpr (fun _ hr hc => hc.2 hr)
  · intro N hn
    cases he : F.nextPart with
    | none => simp [restrictFree, he] at hn
    | some M =>
      have hN : M.restrictFree (A ∪ F.current.resets.clocks) = N := by
        simpa only [restrictFree, he, Option.map_some, Option.some.injEq] using hn
      subst N
      exact ⟨M, rfl, M.restrictFree_components _,
        Set.disjoint_left.mpr (fun _ hr hc => hc.2 hr)⟩

theorem ComponentsIncluded.restrictFree_target
    {S U : StateForm Clock Var} (h : ComponentsIncluded S U) (A : Set Clock)
    (hf : S.freeClocks ⊆ A) : ComponentsIncluded S (U.restrictFree A) := by
  refine ⟨?_, h.resets, ?_⟩
  · intro g hg
    exact ⟨h.guards hg, hf (Or.inl ⟨g, hg, rfl⟩)⟩
  · intro l hl
    refine ⟨h.locals hl, ?_⟩
    intro c hc
    by_cases hr : c ∈ S.resets.clocks
    · obtain ⟨a, ha⟩ := hr
      exact Or.inr ⟨a, h.resets c a ha⟩
    · exact Or.inl (hf (Or.inr ⟨⟨l, hl, hc⟩, hr⟩))

theorem SyntacticallySubsumed.restrictFree_target
    {F U : TransitionForm Clock Var} (h : SyntacticallySubsumed F U)
    (A : Set Clock) (hf : F.freeClocks ⊆ A) :
    SyntacticallySubsumed F (U.restrictFree A) := by
  refine ⟨h.current.restrictFree_target A ?_, h.outerFresh, ?_⟩
  · intro c hc
    apply hf
    rcases hc with hg | ⟨hl, hn⟩
    · exact Or.inl hg
    · exact Or.inr ⟨Or.inl hl, hn⟩
  · intro N hn
    obtain ⟨M, hm, hi, hno⟩ := h.next N hn
    refine ⟨M.restrictFree (A ∪ U.current.resets.clocks), ?_,
      hi.restrictFree_target _ ?_, hno⟩
    · simp only [TransitionForm.restrictFree, hm, Option.map_some]
    · intro c hc
      by_cases hr : c ∈ F.current.resets.clocks
      · obtain ⟨a, ha⟩ := hr
        exact Or.inr ⟨a, h.current.resets c a ha⟩
      · apply Or.inl
        apply hf
        refine Or.inr ⟨Or.inr ?_, hr⟩
        change c ∈ (match F.nextPart with | none => ∅ | some S => S.freeClocks)
        rwa [hn]

end STLTableau.Section3
