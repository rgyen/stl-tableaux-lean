import STLTableaux.Closure.Expansion.BranchwiseExpansion
import STLTableaux.Closure.Support.BranchFreeClocks

/-! Literal unions below a common upper bound preserve both no-capture clauses. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}

namespace TransitionForm

private theorem components_union_below {S T U : StateForm Clock Var}
    (hS : ComponentsIncluded S U) (hT : ComponentsIncluded T U) :
    ComponentsIncluded S (S.union T) ∧ ComponentsIncluded T (S.union T) ∧
      ComponentsIncluded (S.union T) U := by
  have hcon : S.resets.Consistent T.resets := by
    intro c a b ha hb
    exact Option.some.inj ((hS.resets c a ha).symm.trans (hT.resets c b hb))
  refine ⟨⟨Set.subset_union_left, ClockResetSet.subset_union_left _ _, Set.subset_union_left⟩,
    ⟨Set.subset_union_right, ClockResetSet.subset_union_right _ _ hcon,
      Set.subset_union_right⟩,
    ⟨Set.union_subset hS.guards hT.guards, ?_, Set.union_subset hS.locals hT.locals⟩⟩
  intro c a ha
  change (match S.resets.value c with | some b => some b | none => T.resets.value c) =
    some a at ha
  split at ha
  · rename_i b hb
    exact hS.resets c a (hb.trans ha)
  · exact hT.resets c a ha

private theorem state_localClocks_union (S T : StateForm Clock Var) :
    (S.union T).localClocks = S.localClocks ∪ T.localClocks := by
  ext c
  simp only [StateForm.localClocks, StateForm.union, Set.mem_setOf_eq, Set.mem_union]
  aesop

private theorem state_unbound_union_subset (S T : StateForm Clock Var) :
    (S.union T).localClocks \ (S.union T).resets.clocks ⊆
      (S.localClocks \ S.resets.clocks) ∪ (T.localClocks \ T.resets.clocks) := by
  rw [state_localClocks_union]
  simp only [StateForm.union, ClockResetSet.clocks_union]
  intro c hc
  simp only [Set.mem_sdiff, Set.mem_union] at hc ⊢
  tauto

theorem unboundBody_union_subset (F B : TransitionForm Clock Var) :
    (F.union B).bodyFreeClocks \ (F.union B).current.resets.clocks ⊆
      (F.bodyFreeClocks \ F.current.resets.clocks) ∪
        (B.bodyFreeClocks \ B.current.resets.clocks) := by
  have hg (S T : StateForm Clock Var) :
      (S.union T).guardClocks = S.guardClocks ∪ T.guardClocks := by
    ext c
    simp only [StateForm.guardClocks, StateForm.union, Set.mem_setOf_eq, Set.mem_union]
    aesop
  have hr (S T : StateForm Clock Var) :
      (S.union T).resets.clocks = S.resets.clocks ∪ T.resets.clocks :=
    ClockResetSet.clocks_union _ _
  cases hF : F.nextPart <;> cases hB : B.nextPart <;>
    simp only [bodyFreeClocks, union, unionNext, hF, hB, StateForm.freeClocks,
      hg, state_localClocks_union, hr] <;>
    intro c hc <;> simp only [Set.mem_union, Set.mem_sdiff] at * <;> tauto

private def NextIncluded (X Y : Option (StateForm Clock Var)) : Prop :=
  ∀ N, X = some N → ∃ M, Y = some M ∧ ComponentsIncluded N M ∧
    Disjoint M.resets.clocks (N.localClocks \ N.resets.clocks)

private theorem nextIncluded_refl (X : Option (StateForm Clock Var)) :
    NextIncluded X X := by
  intro N hn
  exact ⟨N, hn, ⟨fun _ h => h, fun _ _ h => h, fun _ h => h⟩,
    Set.disjoint_left.2 (fun _ hc h => h.2 hc)⟩

private theorem nextIncluded_union_below {X Y Z : Option (StateForm Clock Var)}
    (hX : NextIncluded X Z) (hY : NextIncluded Y Z) :
    NextIncluded X (unionNext X Y) ∧ NextIncluded Y (unionNext X Y) ∧
      NextIncluded (unionNext X Y) Z := by
  cases X with
  | none =>
    refine ⟨?_, nextIncluded_refl _, hY⟩
    intro N hn
    cases hn
  | some S =>
    cases Y with
    | none =>
      refine ⟨nextIncluded_refl _, ?_, hX⟩
      intro N hn
      cases hn
    | some T =>
      obtain ⟨U, hU, hS, hfS⟩ := hX S rfl
      obtain ⟨V, hV, hT, hfT⟩ := hY T rfl
      have he : U = V := Option.some.inj (hU.symm.trans hV)
      subst V
      obtain ⟨hL, hR, hI⟩ := components_union_below hS hT
      have hr := ClockResetSet.clocks_mono hI.resets
      refine ⟨?_, ?_, ?_⟩
      · intro N hn
        cases hn
        exact ⟨S.union T, rfl, hL, hfS.mono_left hr⟩
      · intro N hn
        cases hn
        exact ⟨S.union T, rfl, hR, hfT.mono_left hr⟩
      · intro N hn
        change some (S.union T) = some N at hn
        cases hn
        exact ⟨U, hU, hI, (Disjoint.union_right hfS hfT).mono_right
          (state_unbound_union_subset S T)⟩

/-- A literal common upper bound certifies that the literal union is the join. -/
theorem union_is_lub_below {F B U : TransitionForm Clock Var}
    (hFU : SyntacticallySubsumed F U) (hBU : SyntacticallySubsumed B U) :
    F.UnionCompatible B ∧ SyntacticallySubsumed (F.union B) U := by
  obtain ⟨hL, hR, hI⟩ := components_union_below hFU.current hBU.current
  obtain ⟨hNL, hNR, hNI⟩ := nextIncluded_union_below hFU.next hBU.next
  have hr := ClockResetSet.clocks_mono hI.resets
  exact ⟨⟨⟨hL, hFU.outerFresh.mono_left hr, hNL⟩,
    ⟨hR, hBU.outerFresh.mono_left hr, hNR⟩⟩,
    ⟨hI, (Disjoint.union_right hFU.outerFresh hBU.outerFresh).mono_right
      (unboundBody_union_subset F B), hNI⟩⟩

end TransitionForm

namespace ClosureCatalogue

theorem BranchwisePExpansion.eq_union_or_identity {E : ClosureCatalogue Clock Var}
    {p : Predicate Clock Var} {F G : TransitionForm Clock Var}
    (h : E.BranchwisePExpansion p F G) :
    (E.RuleClosedFor F p ∧ G = F) ∨
      ∃ B, E.Branch p F.current.resets B ∧ F.UnionCompatible B ∧ G = F.union B := by
  rcases h with hi | ⟨B, hb, hF, hB, hmin⟩
  · exact Or.inl hi
  · obtain ⟨hu, hle⟩ := TransitionForm.union_is_lub_below hF hB
    exact Or.inr ⟨B, hb, hu, (hmin _ hu.left hu.right hle).antisymm hle⟩

theorem BranchwisePExpansion.of_compatible_union {E : ClosureCatalogue Clock Var}
    {p : Predicate Clock Var} {F B : TransitionForm Clock Var}
    (hb : E.Branch p F.current.resets B) (hu : F.UnionCompatible B) :
    E.BranchwisePExpansion p F (F.union B) :=
  Or.inr ⟨B, hb, hu.left, hu.right, fun _ hF hB _ =>
    (TransitionForm.union_is_lub_below hF hB).2⟩

end ClosureCatalogue

namespace ConcreteContextual

theorem branchwise_free_under_current_subset [DecidableEq Clock]
    {p : Predicate Clock Var} {F G : TransitionForm Clock Var}
    (hp : Local.predicate p ∈ F.current.locals)
    (h : catalogue.BranchwisePExpansion p F G) :
    G.bodyFreeClocks \ G.current.resets.clocks ⊆
      F.bodyFreeClocks \ F.current.resets.clocks := by
  rcases h.eq_union_or_identity with ⟨_, rfl⟩ | ⟨B, hb, _, rfl⟩
  · exact Set.Subset.rfl
  obtain ⟨R, A, hR, ha, rfl⟩ := hb
  have hg : A.current.guards = ∅ :=
    ha.current_guards.trans (FaithfulClosure.mixed_branch_currentGuards_empty hR)
  intro c hc
  rcases TransitionForm.unboundBody_union_subset _ _ hc with hf | hb
  · exact hf
  · have haFree := TransitionForm.freeClocks_underReset_subset A F.current.resets hg
      (Or.inr hb)
    have hcp : c ∈ (Judgement.predicate p).freeClocks :=
      ConcreteMixed.branch_freeClocks hR (ha.freeClocks ▸ haFree.1)
    exact ⟨Or.inl ⟨.predicate p, hp, hcp⟩, haFree.2⟩

end ConcreteContextual
end STLTableau.Section3
