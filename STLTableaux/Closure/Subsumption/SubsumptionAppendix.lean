import STLTableaux.Closure.Subsumption.FaithfulClosureRestriction

/-! The two standalone subsumption lemmas in app-closure. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}

theorem SyntacticallySubsumed.bodyFreeClocks_mono {F G : TransitionForm Clock Var}
    (h : SyntacticallySubsumed F G) : F.bodyFreeClocks ⊆ G.bodyFreeClocks := by
  intro c hc
  rcases hc with hc | hc
  · exact Or.inl (h.current.localClocks_mono hc)
  · right
    cases hn : F.nextPart with
    | none => simp [TransitionForm.bodyFreeClocks, hn] at hc
    | some N =>
        obtain ⟨M, hm, hi, hf⟩ := h.next N hn
        simpa only [hm] using hi.freeClocks_mono hf (by simpa only [hn] using hc)

theorem SyntacticallySubsumed.restrictLocals_mono {F G : TransitionForm Clock Var}
    (h : SyntacticallySubsumed F G) (Q Qnext : Local Clock Var → Prop) :
    SyntacticallySubsumed (F.restrictLocals Q Qnext) (G.restrictLocals Q Qnext) := by
  refine ⟨⟨h.current.guards, h.current.resets,
    fun l hl => ⟨h.current.locals hl.1, hl.2⟩⟩, ?_, ?_⟩
  · apply Set.disjoint_left.2
    intro c hc hf
    apply Set.disjoint_left.1 h.outerFresh hc
    exact ⟨(F.restrictLocals_subsumed Q Qnext).bodyFreeClocks_mono hf.1, hf.2⟩
  · intro N hn
    obtain ⟨N₀, hN, rfl⟩ := Option.map_eq_some_iff.mp hn
    obtain ⟨M, hm, hi, hf⟩ := h.next N₀ hN
    refine ⟨M.restrictLocals Qnext,
      by simp only [TransitionForm.restrictLocals, hm, Option.map_some],
      ⟨hi.guards, hi.resets, fun l hl => ⟨hi.locals hl.1, hl.2⟩⟩, ?_⟩
    apply Set.disjoint_left.2
    intro c hc hcf
    apply Set.disjoint_left.1 hf hc
    rcases hcf with ⟨⟨l, hl, hcl⟩, hn⟩
    exact ⟨⟨l, hl.1, hcl⟩, hn⟩

namespace Local
def IsMarker : Local Clock Var → Prop
  | .marker _ => True
  | _ => False
end Local

theorem SyntacticallySubsumed.type_subsumption {F G : TransitionForm Clock Var}
    (h : SyntacticallySubsumed F G) :
    SyntacticallySubsumed (F.restrictLocals Local.IsMarker (fun _ => True))
      (G.restrictLocals Local.IsMarker (fun _ => True)) ∧
    SyntacticallySubsumed (F.restrictLocals Local.IsMarker Local.IsMarker)
      (G.restrictLocals Local.IsMarker Local.IsMarker) :=
  ⟨h.restrictLocals_mono _ _, h.restrictLocals_mono _ _⟩
end STLTableau.Section3
