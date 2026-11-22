import STLTableaux.Tableau.Construction.GeneratorPath
import STLTableaux.Closure.Correctness.FaithfulFreeClosure

/-! Tableau completeness (Theorem 4.34). The accepting path from the
initial generator gives one run whose trace is satisfied for every initial
clock valuation. -/
namespace STLTableau.Section4
open Section3
variable {Clock Var : Type*}

namespace Generated

/-- The path supplied by Lemma 4.33 is a run when it starts at a closure
of the initial generator. -/
theorem initial_run_exists [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (Xc : Set Clock) (S : Section3.StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hst : S.UnderlyingStable σ P) (hi : S.EvaluatedInvariant σ P α k)
    (hs : S.holds σ P α k) :
    ∃ p : Path Clock (ClosureState Clock Var),
      p.run (closureTableau ConcreteContextual.catalogue X Xc S) ∧
      p.accepting (closureTableau ConcreteContextual.catalogue X Xc S) ∧
      p.fullTrace.holds σ P α k := by
  obtain ⟨Φ,p,hc,hfirst,he,ha,hh⟩ :=
    generator_path_exists_with_closure X Xc S σ P α k S hst hi hs
  refine ⟨p, ⟨ha.1, ?_⟩, ha, hh⟩
  change ConcreteContextual.catalogue.IsClosure
    (Section3.TransitionForm.ofState p.firstState.generator) p.firstState.form ∧
    p.firstState.generator = S ∧ p.firstIncoming = p.firstState.incoming
  refine ⟨?_, ?_, he⟩
  · simpa only [hfirst] using hc
  · simp only [hfirst]

/-- A satisfied full trace implies satisfaction of the trace, which keeps
only the atomic state labels and the incoming clock constraints and resets. -/
theorem atomic_trace_of_fullTrace
    (p : Path Clock (ClosureState Clock Var))
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : p.fullTrace.holds σ P α k) :
    (p.trace labels labels_finite).holds σ P α k := by
  change (p.trace (fun s => s.form.current.locals) (fun s => s.form.current.locals_finite)).holds σ P α k at hs
  induction p generalizing α k with
  | last e s =>
      exact ⟨hs.1, fun l hl => hs.2 l hl.1⟩
  | step e s t ih =>
      refine ⟨⟨hs.1.1, fun l hl => hs.1.2 l hl.1⟩, ?_⟩
      change _ ∧ (if hk : k.1 < P.size then _ else False) at hs
      by_cases hk : k.1 < P.size
      · simp only [dif_pos hk] at hs ⊢
        exact ih _ _ hs.2
      · simpa only [dif_neg hk] using hs.2

end Generated
end STLTableau.Section4

namespace STLTableau.Section4
open Section3
variable {Clock Var : Type*}
namespace Generated

variable [DecidableEq Clock]

def freeSafeTableau (X : Set Var) (Xc : Set Clock) (S : Section3.StateForm Clock Var) :=
  tableau X Xc S (fun G F => ConcreteContextual.catalogue.IsClosure
    (Section3.TransitionForm.ofState G) F ∧ F.freeClocks ⊆ G.freeClocks)

theorem trace_freeClocks_subset_generator
    (X : Set Var) (Xc : Set Clock) (S : Section3.StateForm Clock Var)
    (p : Path Clock (ClosureState Clock Var))
    (hv : p.valid (freeSafeTableau X Xc S))
    (he : p.firstIncoming = p.firstState.incoming) :
    (p.trace labels labels_finite).freeClocks ⊆ p.firstState.generator.freeClocks := by
  induction p with
  | last e s =>
      have hf := hv.2
      change e = s.incoming at he
      subst e
      intro c hc
      apply hf
      rcases hc with hc | ⟨⟨l, hl, hcl⟩, hn⟩
      · exact Or.inl hc
      · exact Or.inr ⟨Or.inl ⟨l, hl.1, hcl⟩, hn⟩
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
        · exact Or.inl ⟨l, hl.1, hcl⟩
        · right
          have hn : s.form.nextPart = some t.firstState.generator := hEdge.1
          simpa only [hn] using ht hc

theorem valid_of_freeSafe_valid
    (X : Set Var) (Xc : Set Clock) (S : Section3.StateForm Clock Var)
    (p : Path Clock (ClosureState Clock Var))
    (hv : p.valid (freeSafeTableau X Xc S)) :
    p.valid (closureTableau ConcreteContextual.catalogue X Xc S) := by
  induction p with
  | last e s => exact hv.1
  | step e s t ih => exact ⟨hv.1.1, ih hv.2.1, hv.2.2.1.1, hv.2.2.2.1.1, hv.2.2.2.2⟩

end Generated
end STLTableau.Section4

namespace STLTableau.Section4
open Section3
variable {Clock Var : Type*}
namespace Generated

/-- A satisfied initial generator with no free clocks admits an accepting run
whose trace holds for every initial valuation. The proof selects a trace with
no free clocks. -/
theorem recognizes_of_satisfied_closed_generator [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (Xc : Set Clock) (S : Section3.StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock)
    (hst : S.UnderlyingStable σ P)
    (hi : S.EvaluatedInvariant σ P α ⟨0, by omega⟩)
    (hs : S.holds σ P α ⟨0, by omega⟩) (hclosed : S.freeClocks = ∅) :
    (closureTableau ConcreteContextual.catalogue X Xc S).recognizes
      labels_finite σ P := by
  obtain ⟨p,hpS,hpE,hpA,hpH⟩ :=
    generator_path_exists_of_closure_selection X Xc S
      (fun G F => ConcreteContextual.catalogue.IsClosure
        (Section3.TransitionForm.ofState G) F ∧ F.freeClocks ⊆ G.freeClocks)
      σ P (fun β j G => G.UnderlyingStable σ P ∧ G.EvaluatedInvariant σ P β j)
      (by
        intro β j G hgood hG
        obtain ⟨F,hc,hf,hiF,hstF,hfree⟩ :=
          FaithfulClosure.satisfied_closure_exists_free G σ P β j hG hgood.2 hgood.1
        exact ⟨F,⟨hc,hfree⟩,hf,fun N hn hk => ⟨hstF.next N hn,hiF.2 N hn hk⟩⟩)
      α ⟨0,by omega⟩ S ⟨hst,hi⟩ hs
  have hv := valid_of_freeSafe_valid X Xc S p hpA.1
  have hr : p.run (closureTableau ConcreteContextual.catalogue X Xc S) := by
    refine ⟨hv,?_,hpS,hpE⟩
    exact (Path.first_mem_of_valid _ p hv)
  have hf := trace_freeClocks_subset_generator X Xc S p hpA.1 hpE
  have hfclosed : (p.trace labels labels_finite).freeClocks = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro c hc
    have hm := hf hc
    rw [hpS,hclosed] at hm
    exact hm
  exact Tableau.recognizes_of_closed_trace _ labels_finite σ P p hr
    ⟨hv,hpA.2⟩ hfclosed α (atomic_trace_of_fullTrace p σ P α _ hpH)

end Generated
end STLTableau.Section4

namespace STLTableau.Section4
open Section3
variable {Clock Var : Type*}
namespace Generated

theorem partition_size_pos (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) :
    0 < P.size := by
  have hz : (0 : ℝ) ∈ σ.domain := ⟨le_rfl, σ.horizon_pos⟩
  rw [← P.covers] at hz
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
  exact lt_of_le_of_lt (Nat.zero_le i.1) i.2

theorem zero_mem_first_interval (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) :
    (0 : ℝ) ∈ P.interval ⟨0,partition_size_pos σ P⟩ := by
  have hz : (0 : ℝ) ∈ σ.domain := ⟨le_rfl,σ.horizon_pos⟩
  rw [← P.covers] at hz
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hz
  by_cases hj0 : j.1 = 0
  · have he : j = ⟨0,partition_size_pos σ P⟩ := Fin.ext hj0
    change (0 : ℝ) ∈ P.interval j at hj
    simpa only [he] using hj
  · obtain ⟨x,hx⟩ := P.nonempty ⟨0,partition_size_pos σ P⟩
    have hxd : x ∈ σ.domain := by
      rw [← P.covers]
      exact Set.mem_iUnion.mpr ⟨⟨0,partition_size_pos σ P⟩,hx⟩
    have ho := P.ordered (i := ⟨0,partition_size_pos σ P⟩) (j := j)
      (by change 0 < j.1; omega)
    have hxr := MarkedInterval.le_right_of_mem hx
    have hjl := MarkedInterval.left_le_of_mem hj
    have he : x = 0 := by have := hxd.1; linarith
    change x ∈ P.interval ⟨0,partition_size_pos σ P⟩ at hx
    simpa only [he] using hx

/-- Theorem 4.34 (tableau completeness). Satisfaction at time zero implies
recognition with respect to the given fully stable partition. -/
theorem recognizes_of_formula [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (Xc : Set Clock) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (hst : σ.StablePartition φ P)
    (hs : σ.Satisfies φ ⟨0,le_rfl,σ.horizon_pos⟩) :
    (closureTableau ConcreteContextual.catalogue X Xc
      (Section3.StateForm.ofLocal (.predicate (.plain φ)))).recognizes labels_finite σ P := by
  let α : ClockValuation Clock := fun _ => 0
  apply recognizes_of_satisfied_closed_generator X Xc _ σ P α
  · intro ψ hψ
    obtain ⟨p,hp,hpψ⟩ := hψ
    have he : p = .plain φ := by simpa only [Section3.StateForm.ofLocal,Set.mem_singleton_iff,
      Local.predicate.injEq] using hp
    subst p
    simpa only [Predicate.formula] using (hpψ ▸ hst)
  · intro l hl
    have he : l = .predicate (.plain φ) := hl
    subst l
    intro hk
    trivial
  · refine ⟨by simp [Section3.StateForm.ofLocal], ?_⟩
    intro l hl
    have he : l = .predicate (.plain φ) := hl
    subst l
    change if h : 0 < P.size then _ else False
    simp only [dif_pos (partition_size_pos σ P)]
    intro t ht
    exact ((hst ⟨0,partition_size_pos σ P⟩).stable
      ⟨0,le_rfl,σ.horizon_pos⟩ t (zero_mem_first_interval σ P) ht).mp hs
  · simp [Section3.StateForm.freeClocks, Section3.StateForm.guardClocks, Section3.StateForm.localClocks,
      Section3.StateForm.ofLocal, Section3.Local.freeClocks, Section3.Local.toJudgement, Section3.Judgement.freeClocks]

end Generated
end STLTableau.Section4
