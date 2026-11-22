import STLTableaux.Finiteness.Correctness.FiniteRootTableau

/-! The finite tableau has finite edge, initial, and final sets as well as
finite states. Incoming labels are fixed by their actual target judgement. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

namespace Subgraph

theorem judgement_restriction_edges_finite
    (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (R : Section3.StateForm Clock Var→Section3.TransitionForm Clock Var→Prop)
    (A : Set (Section3.TransitionForm Clock Var))
    (hf : (restrict (JudgementTableau.tableau X Q root R) A).states.Finite) :
    (restrict (JudgementTableau.tableau X Q root R) A).edges.Finite := by
  let S := (restrict (JudgementTableau.tableau X Q root R) A).states
  have hi := (hf.prod hf).image
    (fun p : Section3.TransitionForm Clock Var×Section3.TransitionForm Clock Var=>
      (p.1,JudgementTableau.incoming p.2,p.2))
  apply hi.subset
  intro e he
  obtain ⟨_,_,N,_,_,hlabel⟩ := he.1
  refine ⟨(e.1,e.2.2),⟨he.2.1,he.2.2⟩,?_⟩
  exact Prod.ext rfl (Prod.ext hlabel.symm rfl)

theorem judgement_restriction_initial_finite
    (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (R : Section3.StateForm Clock Var→Section3.TransitionForm Clock Var→Prop)
    (A : Set (Section3.TransitionForm Clock Var))
    (hf : (restrict (JudgementTableau.tableau X Q root R) A).states.Finite) :
    (restrict (JudgementTableau.tableau X Q root R) A).initial.Finite := by
  have hi := hf.image (fun F=>(JudgementTableau.incoming F,F))
  apply hi.subset
  intro e he
  exact ⟨e.2,he.2,Prod.ext he.1.2.symm rfl⟩

theorem judgement_restriction_final_finite
    (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (R : Section3.StateForm Clock Var→Section3.TransitionForm Clock Var→Prop)
    (A : Set (Section3.TransitionForm Clock Var))
    (hf : (restrict (JudgementTableau.tableau X Q root R) A).states.Finite) :
    (restrict (JudgementTableau.tableau X Q root R) A).final.Finite :=
  hf.subset (fun _ h=>h.2)
end Subgraph

variable [DecidableEq Clock] [Infinite Clock]

theorem finiteRootTableau_edges_finite (X : Set Var) (root : Formula Var) :
    (finiteRootTableau (Clock := Clock) X root).edges.Finite :=
  Subgraph.judgement_restriction_edges_finite _ _ _ _ _ (finiteRootTableau_states_finite X root)

theorem finiteRootTableau_initial_finite (X : Set Var) (root : Formula Var) :
    (finiteRootTableau (Clock := Clock) X root).initial.Finite :=
  Subgraph.judgement_restriction_initial_finite _ _ _ _ _ (finiteRootTableau_states_finite X root)

theorem finiteRootTableau_final_finite (X : Set Var) (root : Formula Var) :
    (finiteRootTableau (Clock := Clock) X root).final.Finite :=
  Subgraph.judgement_restriction_final_finite _ _ _ _ _ (finiteRootTableau_states_finite X root)
end STLTableau.Section4.Finiteness
