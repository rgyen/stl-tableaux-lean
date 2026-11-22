/-
Copyright (c) 2026 STLTableau contributors. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: STLTableau contributors
-/
import STLTableaux.Finiteness.Derivation.SimplifiedClosure
import STLTableaux.Finiteness.Correctness.SimplifiedTableau
import STLTableaux.Tableau.Correctness.GeneratorPathCompleteness

/-! Soundness of the simplified tableau (Lemma D.5) and correspondence of
satisfied accepting runs with the original tableau (Lemma 4.35). The inclusion
from the original graph preserves the paired path and its edge labels. -/
namespace STLTableau.Section4.Finiteness

open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

private theorem simplified_original_valid_forward (X : Set Var) (Q : Set Clock)
    (root : Section3.StateForm Clock Var) (p : Path Clock (ClosureState Clock Var))
    (hp : p.valid (Generated.closureTableau ConcreteContextual.catalogue X Q root))
    (hr : p.firstState.generator.Ready) :
    p.valid (PairedTableau.tableau X Q root CompletedDerivation.Admitted) := by
  induction p with
  | last e s => exact ⟨⟨s.form, hp⟩, .original hp hr⟩
  | step e s t ih =>
      have hready := ConcreteContextual.closure_ready hp.1
        ((Section3.TransitionForm.ready_ofState s.generator).2 hr)
      have hedge : s.form.nextPart = some t.firstState.generator ∧
          t.firstIncoming = t.firstState.incoming := hp.2.2.2.2
      have htr := hready.2 t.firstState.generator hedge.1
      have htc := Path.first_mem_of_valid _ t hp.2.1
      have hs : s ∈ (PairedTableau.tableau X Q root CompletedDerivation.Admitted).states :=
        ⟨⟨s.form, hp.1⟩, .original hp.1 hr⟩
      have ht : t.firstState ∈
          (PairedTableau.tableau X Q root CompletedDerivation.Admitted).states :=
        ⟨⟨t.firstState.form, htc⟩, .original htc htr⟩
      exact ⟨hs, ih hp.2.1 htr, hs, ht, t.firstState.generator, hedge.1,
        .original htc htr, hedge.2⟩

/-- Every run from a ready original root is literally a run of the paired
simplified tableau. No change of stored generators or labels is made. -/
theorem simplified_original_run_forward (X : Set Var) (Q : Set Clock)
    (root : Section3.StateForm Clock Var) (hroot : root.Ready)
    (p : Path Clock (ClosureState Clock Var))
    (hp : p.run (Generated.closureTableau ConcreteContextual.catalogue X Q root)) :
    p.run (PairedTableau.tableau X Q root CompletedDerivation.Admitted) := by
  have hr : p.firstState.generator.Ready := hp.2.2.1 ▸ hroot
  refine ⟨simplified_original_valid_forward X Q root p hp.1 hr, ?_⟩
  have hc := hp.2.1
  have hstored : p.firstState ∈
      (PairedTableau.tableau X Q root CompletedDerivation.Admitted).states :=
    ⟨⟨p.firstState.form, hc⟩, .original hc hr⟩
  rw [hp.2.2.1] at hc
  exact ⟨hstored, .original hc hroot, hp.2.2.2⟩

/-- Lemma D.5 for an arbitrary input state and starting position satisfying
the positional and nonemptiness invariants. -/
theorem simplified_fullTrace_and_input_of_atomic [Nontrivial Clock]
    (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (p : Path Clock (ClosureState Clock Var))
    (hr : p.run (PairedTableau.tableau X Q root CompletedDerivation.Admitted))
    (ha : p.accepting (PairedTableau.tableau X Q root CompletedDerivation.Admitted))
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hi : root.EvaluatedNumeric σ P α k)
    (hs : (p.trace Generated.labels Generated.labels_finite).holds σ P α k) :
    p.fullTrace.holds σ P α k ∧ root.holds σ P α k := by
  let t := JudgementTableau.forgetGenerator p
  have ht : (t.trace JudgementTableau.labels JudgementTableau.labels_finite).holds σ P α k := by
    simpa only [t, JudgementTableau.ordinary_trace_forward] using hs
  obtain ⟨hf, _, hroot⟩ := JudgementTableau.fullTrace_and_root_of_accepting_run
    CompletedDerivation.Admitted CompletedDerivation.admitted_localLaws X Q root t
    (PairedTableau.forget_run X Q root _ p hr)
    (PairedTableau.forget_accepting X Q root _ p ha) σ P α k hi ht
  exact ⟨by simpa only [t, JudgementTableau.full_trace_forward] using hf, hroot⟩

local notation "plainRoot" φ =>
  Section3.StateForm.ofLocal (Section3.Local.predicate (Section3.Predicate.plain φ))

theorem simplified_fullTrace_and_formula_of_atomic [Nontrivial Clock]
    (X : Set Var) (Q : Set Clock) (φ : Formula Var)
    (p : Path Clock (ClosureState Clock Var))
    (hr : p.run (PairedTableau.tableau X Q (plainRoot φ) CompletedDerivation.Admitted))
    (ha : p.accepting (PairedTableau.tableau X Q (plainRoot φ) CompletedDerivation.Admitted))
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (hs : (p.trace Generated.labels Generated.labels_finite).holds σ P α ⟨0, by omega⟩) :
    p.fullTrace.holds σ P α ⟨0, by omega⟩ ∧ σ.Satisfies φ ⟨0, le_rfl, σ.horizon_pos⟩ := by
  have hi : (plainRoot φ : Section3.StateForm Clock Var).EvaluatedNumeric σ P α ⟨0, by omega⟩ := by
    intro l hl
    have he : l = .predicate (.plain φ) := hl
    subst l
    intro hk
    trivial
  obtain ⟨hf, hroot⟩ := simplified_fullTrace_and_input_of_atomic X Q _ p hr ha σ P α _ hi hs
  refine ⟨hf, ?_⟩
  have hplain := hroot.2 (.predicate (.plain φ)) (by simp [Section3.StateForm.ofLocal])
  change (if h : 0 < P.size then _ else False) at hplain
  simp only [dif_pos (Generated.partition_size_pos σ P)] at hplain
  exact hplain ⟨0, le_rfl, σ.horizon_pos⟩ (Generated.zero_mem_first_interval σ P)

private theorem simplified_original_satisfied_run_of_formula [Infinite Clock]
    (X : Set Var) (Q : Set Clock) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (hst : σ.StablePartition φ P) (hs : σ.Satisfies φ ⟨0, le_rfl, σ.horizon_pos⟩) :
    ∃ p : Path Clock (ClosureState Clock Var),
      p.run (Generated.closureTableau ConcreteContextual.catalogue X Q (plainRoot φ)) ∧
      p.accepting (Generated.closureTableau ConcreteContextual.catalogue X Q (plainRoot φ)) ∧
      p.fullTrace.holds σ P α ⟨0, by omega⟩ := by
  apply Generated.initial_run_exists X Q _ σ P α ⟨0, by omega⟩
  · intro ψ hψ
    obtain ⟨p, hp, hpψ⟩ := hψ
    have he : p = .plain φ := by simpa only [Section3.StateForm.ofLocal,
      Set.mem_singleton_iff, Local.predicate.injEq] using hp
    subst p
    simpa only [Section3.Predicate.formula] using (hpψ ▸ hst)
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
    simp only [dif_pos (Generated.partition_size_pos σ P)]
    intro t ht
    exact ((hst ⟨0, Generated.partition_size_pos σ P⟩).stable
      ⟨0, le_rfl, σ.horizon_pos⟩ t (Generated.zero_mem_first_interval σ P) ht).mp hs

/-- Lemma 4.35. For a fixed signal, fully stable partition, and valuation,
a satisfied accepting full trace exists in the original tableau if and
only if one exists in the simplified tableau. -/
theorem simplified_satisfied_accepting_iff [Infinite Clock]
    (X : Set Var) (Q : Set Clock) (φ : Formula Var) (hφ : φ.MixedReady)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (hst : σ.StablePartition φ P)
    (α : ClockValuation Clock) :
    (∃ p : Path Clock (ClosureState Clock Var),
      p.run (Generated.closureTableau ConcreteContextual.catalogue X Q (plainRoot φ)) ∧
      p.accepting (Generated.closureTableau ConcreteContextual.catalogue X Q (plainRoot φ)) ∧
      p.fullTrace.holds σ P α ⟨0, by omega⟩) ↔
    (∃ p : Path Clock (ClosureState Clock Var),
      p.run (PairedTableau.tableau X Q (plainRoot φ) CompletedDerivation.Admitted) ∧
      p.accepting (PairedTableau.tableau X Q (plainRoot φ) CompletedDerivation.Admitted) ∧
      p.fullTrace.holds σ P α ⟨0, by omega⟩) := by
  constructor
  · rintro ⟨p, hr, ha, hs⟩
    have hready : (plainRoot φ : Section3.StateForm Clock Var).Ready :=
      (Section3.StateForm.ready_ofLocal _).2 hφ
    have hm := simplified_original_run_forward X Q _ hready p hr
    exact ⟨p, hm, ⟨hm.1, ha.2⟩, hs⟩
  · rintro ⟨p, hr, ha, hs⟩
    have hs' := Generated.atomic_trace_of_fullTrace p σ P α ⟨0, by omega⟩ hs
    exact simplified_original_satisfied_run_of_formula X Q φ σ P α hst
      (simplified_fullTrace_and_formula_of_atomic X Q φ p hr ha σ P α hs').2

run_elab do
  for name in #[``simplified_original_run_forward, ``simplified_fullTrace_and_formula_of_atomic,
      ``simplified_satisfied_accepting_iff] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "simplified tableau: unexpected axiom {ax}"

end STLTableau.Section4.Finiteness
