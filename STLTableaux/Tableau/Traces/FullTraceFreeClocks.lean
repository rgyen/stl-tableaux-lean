import STLTableaux.Tableau.Correctness.GeneratorPathCompleteness

namespace STLTableau.Section4.Generated
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

theorem fullTrace_freeClocks_subset_generator
    (X : Set Var) (Xc : Set Clock) (S : Section3.StateForm Clock Var)
    (p : Path Clock (ClosureState Clock Var))
    (hv : p.valid (freeSafeTableau X Xc S))
    (he : p.firstIncoming = p.firstState.incoming) :
    p.fullTrace.freeClocks ⊆ p.firstState.generator.freeClocks := by
  induction p with
  | last e s =>
      have hf := hv.2
      change e = s.incoming at he
      subst e
      intro c hc
      apply hf
      rcases hc with hc | ⟨⟨l, hl, hcl⟩, hn⟩
      · exact Or.inl hc
      · exact Or.inr ⟨Or.inl ⟨l, hl, hcl⟩, hn⟩
  | step e s t ih =>
      have hEdge := hv.2.2.2.2
      have ht := ih hv.2.1 hEdge.2
      change e = s.incoming at he
      subst e
      intro c hc
      apply hv.1.2
      rcases hc with hc | ⟨hc, hn⟩
      · exact Or.inl hc
      · refine Or.inr ⟨?_, hn⟩
        rcases hc with ⟨l, hl, hcl⟩ | hc
        · exact Or.inl ⟨l, hl, hcl⟩
        · right
          have hn : s.form.nextPart = some t.firstState.generator := hEdge.1
          simpa only [hn] using ht hc

end STLTableau.Section4.Generated
