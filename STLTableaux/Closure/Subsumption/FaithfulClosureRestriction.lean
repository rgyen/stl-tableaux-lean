import STLTableaux.Closure.Catalogue.FaithfulContextualCatalogue

/-! Predicate filtering and minimality of faithful closures. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}

namespace StateForm

def restrictLocals (S : StateForm Clock Var) (Q : Local Clock Var → Prop) :
    StateForm Clock Var :=
  { S with
    locals := {l ∈ S.locals | Q l}
    locals_finite := S.locals_finite.subset (fun _ h => h.1) }

end StateForm

namespace TransitionForm

def restrictLocals (F : TransitionForm Clock Var) (Q Qnext : Local Clock Var → Prop) :
    TransitionForm Clock Var :=
  ⟨F.current.restrictLocals Q, F.nextPart.map (fun N => N.restrictLocals Qnext)⟩

theorem restrictLocals_subsumed (F : TransitionForm Clock Var)
    (Q Qnext : Local Clock Var → Prop) :
    SyntacticallySubsumed (F.restrictLocals Q Qnext) F := by
  refine ⟨⟨fun _ h => h, fun _ _ h => h, fun _ h => h.1⟩, ?_, ?_⟩
  · exact Set.disjoint_left.2 (fun _ hc hf => hf.2 hc)
  · intro N hn
    obtain ⟨M, hm, rfl⟩ := Option.map_eq_some_iff.mp hn
    exact ⟨M, hm, ⟨fun _ h => h, fun _ _ h => h, fun _ h => h.1⟩,
      Set.disjoint_left.2 (fun _ hc hf => hf.2 hc)⟩

end TransitionForm

/-- Filtering a target retains a subsumed branch whenever each of its
included current and next locals passes the corresponding filter. -/
theorem SyntacticallySubsumed.restrictLocalsTarget
    {B F : TransitionForm Clock Var} (h : SyntacticallySubsumed B F)
    (Q Qnext : Local Clock Var → Prop)
    (hc : ∀ l ∈ B.current.locals, Q l)
    (hn : ∀ N M, B.nextPart = some N → F.nextPart = some M →
      ∀ l ∈ N.locals, Qnext l) :
    SyntacticallySubsumed B (F.restrictLocals Q Qnext) := by
  refine ⟨⟨h.current.guards, h.current.resets, fun l hl => ⟨h.current.locals hl, hc l hl⟩⟩,
    h.outerFresh, ?_⟩
  intro N hN
  obtain ⟨M, hM, hNM, hfresh⟩ := h.next N hN
  exact ⟨M.restrictLocals Qnext, by simp only [TransitionForm.restrictLocals, hM,
    Option.map_some], ⟨hNM.guards, hNM.resets,
      fun l hl => ⟨hNM.locals hl, hn N M hN hM l hl⟩⟩, hfresh⟩

namespace ClosureCatalogue

/-- A minimal closure cannot contain a bad predicate if deleting all bad
current and next predicates preserves its source and closedness. This uses
minimality itself, without assuming an expansion derivation for the closure. -/
theorem minimal_restriction_eq (E : ClosureCatalogue Clock Var)
    {anchor F : TransitionForm Clock Var} (hclosure : E.IsClosure anchor F)
    (Q Qnext : Local Clock Var → Prop)
    (hanchor : SyntacticallySubsumed anchor (F.restrictLocals Q Qnext))
    (hclosed : E.IsClosed (F.restrictLocals Q Qnext)) :
    F = F.restrictLocals Q Qnext := by
  have hdown := F.restrictLocals_subsumed Q Qnext
  exact (hclosure.minimal _ hanchor hclosed hdown).antisymm hdown

end ClosureCatalogue
end STLTableau.Section3
