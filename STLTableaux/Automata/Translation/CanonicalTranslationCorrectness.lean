/-
Copyright (c) 2026 STLTableau contributors. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: STLTableau contributors
-/
import STLTableaux.Automata.Translation.CanonicalTableauForward
import STLTableaux.Automata.Translation.CanonicalTableauCut
import STLTableaux.Automata.Translation.FiniteTableauTranslationSupport

/-! Translation correctness for the finite tableau and the automaton of
Definition 5.3. -/
namespace STLTableau.Section4.Finiteness
open Section3

variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
variable (X : Set Var) (root : Formula.NormalizedInput Var)
local notation "U" => finiteTableau (Clock := Clock) X root.val

private theorem canonical_visits_normalizedReady {τ : ℝ} {σ : FiniteSignal Var}
    (h : (U).TranslationReady) (e : (U).CanonicalExecution h τ σ)
    (i : Fin e.n) : (e.start i).val.1.val.form.NormalizedReady := by
  obtain ⟨k, hk⟩ := i
  induction k with
  | zero => exact finiteTableau_initial_normalizedReady X root e.initial_edge
  | succ k ih =>
    let j : Fin (e.n - 1) := ⟨k, by omega⟩
    let i : Fin e.n := ⟨k, by omega⟩
    have edge := (e.jump j).property.1
    change ((e.finish i).val.1.val, (e.jump j).val, (e.start ⟨k + 1, hk⟩).val.1.val) ∈
      (U).edges at edge
    rw [← (e.flow i).1] at edge
    exact finiteTableau_edge_normalizedReady X root.val edge (ih i.isLt)

private theorem canonical_recognizes_at_cut {τ : ℝ} {σ : FiniteSignal Var}
    (h : (U).TranslationReady) (e : (U).CanonicalExecution h τ σ)
    (goal : e.goal) (P : IntervalPartition σ.domain) (induced : e.Induces P) :
    (U).recognizes Generated.labels_finite σ P := by
  apply e.recognizes Generated.labels_finite (finiteTableau_trace_closed X root.val)
    ?_ ?_ induced goal
  · intro l q hi
    exact finiteTableau_initial_nonterminal X root.val (e := (l, q.val)) hi
  · intro i l hl
    exact (canonical_visits_normalizedReady X root h e i).1 l hl.1

/-- Lemma 5.5. An accepting run yields a goal-reaching execution that follows
the given partition boundaries, with a positive flow after a final singleton
when needed. A goal at the horizon may be reached by one jump from the last
flow endpoint. Conversely, an admissible execution that visits a goal
induces a recognizing partition at every admissible goal cut. At least
one such cut and partition exist. -/
theorem canonical_translation_correctness (hX : X.Finite)
    (vars : ∀ x ∈ rootVariables root.val, x ∈ X)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) root.val → a.relation = .ge)
    (σ : FiniteSignal Var) :
    let h := finiteTableau_translationReady (Clock := Clock) X root.val hX vars
    (SignalAtomRightContinuous σ root.val → ∀ P : IntervalPartition σ.domain,
      (U).recognizes Generated.labels_finite σ P →
      ∃ aug : FiniteSignal (U).HAVar,
        aug.reindex (Sum.inl : (U).realVariables → (U).HAVar) = σ.reindex Subtype.val ∧
        ((U).canonicalAutomaton h σ.horizon).PrelimReachesStateOrFinalJump aug
          ((U).canonicalGoal h σ.horizon)) ∧
    (∀ (e : (U).CanonicalExecution h σ.horizon σ) (P : IntervalPartition σ.domain),
      e.GoalInduces P → (U).recognizes Generated.labels_finite σ P) ∧
    (∀ (e : (U).CanonicalExecution h σ.horizon σ), e.VisitsGoal →
      ∃ P : IntervalPartition σ.domain, e.GoalInduces P ∧
        (U).recognizes Generated.labels_finite σ P) := by
  intro h
  have successor (a b : (U).states) (l : EdgeLabel Clock)
      (goal : a ∈ (U).goalModes) (edge : (a.val,l,b.val) ∈ (U).edges) :=
    finiteTableau_final_successor X root.val (e := (a.val, l, b.val)) goal edge
  refine ⟨?_,?_,?_⟩
  · intro well P recognized
    obtain ⟨empty, hg, hl, he⟩ :=
      finiteTableau_final_continuation (Clock := Clock) X root.val
    obtain ⟨e,goal⟩ :=
      (U).forward_of_recognized h σ P root.val well Generated.labels_finite recognized
        (fun q a ha => let sub := finiteTableau_atom_subformula X root.val q a ha
          ⟨nonStrict a sub,sub⟩)
        empty hg hl he
    exact e.prelim_goal goal
  · rintro e P ⟨i,r,pos,hr,goal,layout⟩
    exact canonical_recognizes_at_cut X root h (e.truncate i r pos hr) goal P layout
  · intro e goal
    obtain ⟨i,r,pos,hr,g⟩ := (e.visitsGoal_iff_cut successor).mp goal
    obtain ⟨P,layout⟩ := (e.truncate i r pos hr).exists_induces
    exact ⟨P,⟨i,r,pos,hr,g,layout⟩,
      canonical_recognizes_at_cut X root h (e.truncate i r pos hr) g P layout⟩

/-- For a system execution starting in its first flow, flow-wise
well-behavedness and full-horizon observation supply the right continuity
required in Lemma 5.5(1). The property execution can start at a singleton. -/
theorem canonical_forward_of_initialFlow {Mode Label : Type*}
    {H : HybridAutomaton Mode Label Var} (hX : X.Finite)
    (vars : ∀ x ∈ rootVariables root.val, x ∈ X)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) root.val → a.relation = .ge)
    (σ : FiniteSignal Var) (e : H.PrelimExecution σ) (full : e.ReachesHorizon)
    (direct : e.initialState = e.start ⟨0,e.nonempty⟩) (well : e.WellBehaved root.val)
    (P : IntervalPartition σ.domain)
    (recognized : (U).recognizes Generated.labels_finite σ P) :
    let h := finiteTableau_translationReady (Clock := Clock) X root.val hX vars
    ∃ aug : FiniteSignal (U).HAVar,
      aug.reindex (Sum.inl : (U).realVariables → (U).HAVar) = σ.reindex Subtype.val ∧
      ((U).canonicalAutomaton h σ.horizon).PrelimReachesStateOrFinalJump aug
        ((U).canonicalGoal h σ.horizon) :=
  (canonical_translation_correctness X root hX vars nonStrict σ).1
    (well.signalAtomRightContinuous full) P recognized

end STLTableau.Section4.Finiteness

namespace STLTableau.Section4.Tableau
open Section3
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
variable (hf : ∀ q, (T.label q).Finite)

/-- Recognition uses just its trace's atomic observations. Restricting a
signal to another observation with the same horizon and strengthening its
atomic truth pointwise cannot invalidate a satisfied trace. -/
theorem recognizes_of_atom_implication {σ ρ : FiniteSignal Var} (h : σ.horizon = ρ.horizon)
    (P : IntervalPartition σ.domain)
    (atoms : ∀ (a : AtomicProposition Var) (t : σ.Time) (u : ρ.Time), t.val = u.val →
      a.Holds (σ.value t) → a.Holds (ρ.value u))
    (recognized : T.recognizes hf σ P) :
    T.recognizes hf ρ (show IntervalPartition ρ.domain from by
      change IntervalPartition (Set.Ico 0 ρ.horizon)
      rw [← h]
      exact P) := by
  rcases σ with ⟨τ,hτ,v⟩
  rcases ρ with ⟨s,hs,w⟩
  dsimp only at h
  subst s
  obtain ⟨p,run,accepting,holds⟩ := recognized
  refine ⟨p,run,accepting,?_⟩
  intro α
  have locals (q : State) (i : STLTableau.Judgement.Position P) (ν : ClockValuation Clock)
      (sat : ∀ l ∈ T.label q, l.holds ⟨τ,hτ,v⟩ P ν i) :
      ∀ l ∈ T.label q, l.holds ⟨τ,hs,w⟩ P ν i := by
    intro l hl
    have live := sat l hl
    have kinds := T.label_atomic _ _ hl
    rcases l with _ | _ | p
    · exact live
    · exact live
    · rcases p with _ | _ | _
      · rename_i φ
        cases φ with
        | truth => exact live
        | neg φ => cases φ <;> first | exact live | contradiction
        | and _ _ | «until» _ _ _ => exact False.elim kinds
        | atom a =>
          by_cases hi : i.val < P.size
          · simp only [Local.holds,Local.toJudgement,Section3.Judgement.holds,dif_pos hi,
              Predicate.holds,predicateSatisfies,FiniteSignal.Satisfies] at live ⊢
            intro t ht
            exact atoms a t t rfl (live t ht)
          · simp only [Local.holds,Local.toJudgement,Section3.Judgement.holds,dif_neg hi] at live
      · exact False.elim kinds
      · exact False.elim kinds
  have mono (p : Path Clock State) (i : STLTableau.Judgement.Position P)
      (ν : ClockValuation Clock) (sat : (p.trace T.label hf).holds ⟨τ,hτ,v⟩ P ν i) :
      (p.trace T.label hf).holds ⟨τ,hs,w⟩ P ν i := by
    induction p generalizing i ν with
    | last l q => exact ⟨sat.1,locals q _ _ sat.2⟩
    | step l q tail ih =>
      refine ⟨⟨sat.1.1,locals q _ _ sat.1.2⟩,?_⟩
      have ht := sat.2
      by_cases hi : i.val < P.size
      · simp only [dif_pos hi] at ht ⊢
        exact ih _ _ ht
      · simp only [dif_neg hi] at ht
  exact mono p _ _ (holds α)

end STLTableau.Section4.Tableau

namespace STLTableau.Section4.Finiteness

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``canonical_translation_correctness, ``canonical_forward_of_initialFlow,
      ``Tableau.recognizes_of_atom_implication] do
    for ax in ← Lean.collectAxioms decl do
      unless allowed.contains ax do throwError "{decl} uses {ax}"

end STLTableau.Section4.Finiteness
