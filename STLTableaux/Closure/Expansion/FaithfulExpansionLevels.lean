import STLTableaux.Closure.Expansion.FaithfulPExpansionProvenance

/-! Auxiliary complete expansion rounds. A round processes all current
predicates, with separate relations for fixed clock names and for
renaming the source's next reset clocks. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}

namespace ExpansionFamily

inductive Sequence (Step : Predicate Clock Var → TransitionForm Clock Var →
    TransitionForm Clock Var → Prop) : List (Predicate Clock Var) →
    TransitionForm Clock Var → TransitionForm Clock Var → Prop
  | nil (F) : Sequence Step [] F F
  | cons {p ps F G H} : Step p F G → Sequence Step ps G H → Sequence Step (p :: ps) F H

def EnumeratesCurrent (ps : List (Predicate Clock Var)) (F : TransitionForm Clock Var) : Prop :=
  ps.Nodup ∧ ∀ p, p ∈ ps ↔ Local.predicate p ∈ F.current.locals

/-- Each source current predicate is processed once, in any enumeration.
New predicates are not inserted into this round's enumeration. -/
def Round (Step : Predicate Clock Var → TransitionForm Clock Var →
    TransitionForm Clock Var → Prop) (F G : TransitionForm Clock Var) : Prop :=
  ∃ ps, EnumeratesCurrent ps F ∧ Sequence Step ps F G

/-- The complete family, not a chosen execution or a cumulative union. -/
def level (Step : Predicate Clock Var → TransitionForm Clock Var →
    TransitionForm Clock Var → Prop) (F : TransitionForm Clock Var) : ℕ → Set (TransitionForm Clock Var)
  | 0 => {F}
  | i + 1 => {G | ∃ H ∈ level Step F i, Round Step H G}

theorem exists_enumeration (F : TransitionForm Clock Var) : ∃ ps, EnumeratesCurrent ps F := by
  classical
  refine ⟨(FaithfulClosure.statePredicates F.current).toList, Finset.nodup_toList _, ?_⟩
  intro p
  simp only [Finset.mem_toList, FaithfulClosure.mem_statePredicates]

/-- Local syntactic contracts used by the round argument. Concrete literal
and alpha-represented minimal expansions are proved to satisfy these below. -/
structure StepLaws (Step : Predicate Clock Var → TransitionForm Clock Var →
    TransitionForm Clock Var → Prop)
    (Closed : TransitionForm Clock Var → Predicate Clock Var → Prop) : Prop where
  current_mono : ∀ {p F G}, Step p F G → F.current.locals ⊆ G.current.locals
  closed_mono : ∀ {p F G}, Step p F G → ∀ q, Closed F q → Closed G q
  target_closed : ∀ {p F G}, Step p F G → Closed G p
  new_current : ∀ {p F G}, Step p F G → ∀ q,
    Local.predicate q ∈ G.current.locals → Local.predicate q ∉ F.current.locals →
    ¬ Closed F p ∧ q.complexity < p.complexity

namespace Sequence

theorem current_mono {Step Closed} (laws : StepLaws (Clock := Clock) (Var := Var) Step Closed)
    {ps F G} (h : Sequence Step ps F G) : F.current.locals ⊆ G.current.locals := by
  induction h with
  | nil => exact Set.Subset.refl _
  | cons hs ht ih => exact (laws.current_mono hs).trans ih

theorem closed_mono {Step Closed} (laws : StepLaws (Clock := Clock) (Var := Var) Step Closed)
    {ps F G} (h : Sequence Step ps F G) (q : Predicate Clock Var) : Closed F q → Closed G q := by
  induction h with
  | nil => exact id
  | cons hs ht ih => exact fun hq => ih (laws.closed_mono hs q hq)

theorem processed_closed {Step Closed} (laws : StepLaws (Clock := Clock) (Var := Var) Step Closed)
    {ps F G} (h : Sequence Step ps F G) (q : Predicate Clock Var) (hq : q ∈ ps) :
    Closed G q := by
  induction h with
  | nil => simp at hq
  | @cons p ps F H G hs ht ih =>
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ht.closed_mono laws q (laws.target_closed hs)
      · exact ih hq

/-- A new final predicate originates at a processed source-unclosed
predicate. This statement does not require a round enumeration. -/
theorem new_current_origin {Step Closed}
    (laws : StepLaws (Clock := Clock) (Var := Var) Step Closed)
    {ps F G} (h : Sequence Step ps F G) (q : Predicate Clock Var)
    (hq : Local.predicate q ∈ G.current.locals) (hnew : Local.predicate q ∉ F.current.locals) :
    ∃ p ∈ ps, ¬ Closed F p ∧ q.complexity < p.complexity := by
  induction h with
  | nil => exact (hnew hq).elim
  | @cons p ps F H G hs ht ih =>
      by_cases hqH : Local.predicate q ∈ H.current.locals
      · obtain ⟨hopen, hlt⟩ := laws.new_current hs q hqH hnew
        exact ⟨p, List.mem_cons_self, hopen, hlt⟩
      · obtain ⟨r, hr, hopen, hlt⟩ := ih hq hqH
        exact ⟨r, List.mem_cons_of_mem p hr,
          (fun hc => hopen (laws.closed_mono hs r hc)), hlt⟩

end Sequence

/-- Every still-unclosed predicate after a complete round was introduced
while processing an initially unclosed source predicate of larger complexity. -/
theorem Round.unclosed_origin {Step Closed}
    (laws : StepLaws (Clock := Clock) (Var := Var) Step Closed)
    {F G} (h : Round Step F G) (q : Predicate Clock Var)
    (hq : Local.predicate q ∈ G.current.locals) (hopen : ¬ Closed G q) :
    ∃ p, Local.predicate p ∈ F.current.locals ∧ ¬ Closed F p ∧
      q.complexity < p.complexity := by
  obtain ⟨ps, hen, hseq⟩ := h
  have hnew : Local.predicate q ∉ F.current.locals := by
    intro hqF
    exact hopen (hseq.processed_closed laws q ((hen.2 q).2 hqF))
  obtain ⟨p, hp, hpc, hlt⟩ := hseq.new_current_origin laws q hq hnew
  exact ⟨p, (hen.2 p).1 hp, hpc, hlt⟩

theorem Sequence.mono {Step Step' : Predicate Clock Var → TransitionForm Clock Var →
    TransitionForm Clock Var → Prop}
    (hStep : ∀ {p F G}, Step p F G → Step' p F G)
    {ps F G} (h : Sequence Step ps F G) : Sequence Step' ps F G := by
  induction h with
  | nil F => exact .nil F
  | cons hs ht ih => exact .cons (hStep hs) ih

theorem Round.mono {Step Step' : Predicate Clock Var → TransitionForm Clock Var →
    TransitionForm Clock Var → Prop}
    (hStep : ∀ {p F G}, Step p F G → Step' p F G)
    {F G} (h : Round Step F G) : Round Step' F G := by
  obtain ⟨ps, hen, hseq⟩ := h
  exact ⟨ps, hen, hseq.mono hStep⟩

theorem level_mono {Step Step' : Predicate Clock Var → TransitionForm Clock Var →
    TransitionForm Clock Var → Prop}
    (hStep : ∀ {p F G}, Step p F G → Step' p F G)
    (F : TransitionForm Clock Var) (i : ℕ) : level Step F i ⊆ level Step' F i := by
  induction i with
  | zero => exact Set.Subset.refl _
  | succ i ih =>
      rintro G ⟨H, hm, hr⟩
      exact ⟨H, ih hm, hr.mono hStep⟩

end ExpansionFamily

namespace ClosureCatalogue
abbrev ExpansionSequence (E : ClosureCatalogue Clock Var) := ExpansionFamily.Sequence E.PExpansion
abbrev ExpansionRound (E : ClosureCatalogue Clock Var) := ExpansionFamily.Round E.PExpansion
abbrev expansionLevel (E : ClosureCatalogue Clock Var) := ExpansionFamily.level E.PExpansion
end ClosureCatalogue

namespace NextAlphaPath

theorem ruleClosed_iff [DecidableEq Clock] {F G : TransitionForm Clock Var}
    (hp : NextAlphaPath F G) (q : Predicate Clock Var) :
    ConcreteContextual.catalogue.RuleClosedFor G q ↔ ConcreteContextual.catalogue.RuleClosedFor F q := by
  induction hp with
  | refl => rfl
  | step F e hf tail ih =>
      exact ih.trans (ConcreteContextual.ruleClosed_alphaNext_iff F e hf q)

end NextAlphaPath

namespace ConcreteContextual

/-- The appendix convention is explicit: current bindings remain literal,
while existing source-next binders may be capture-avoiding alpha converted. -/
def AlphaPExpansion [DecidableEq Clock] (p : Predicate Clock Var)
    (F G : TransitionForm Clock Var) : Prop :=
  ∃ Fa, NextAlphaPath F Fa ∧ catalogue.PExpansion p Fa G

abbrev AlphaExpansionSequence [DecidableEq Clock] := ExpansionFamily.Sequence (AlphaPExpansion (Clock := Clock) (Var := Var))
abbrev AlphaExpansionRound [DecidableEq Clock] := ExpansionFamily.Round (AlphaPExpansion (Clock := Clock) (Var := Var))
abbrev alphaExpansionLevel [DecidableEq Clock] := ExpansionFamily.level (AlphaPExpansion (Clock := Clock) (Var := Var))

theorem literalStepLaws [DecidableEq Clock] :
    ExpansionFamily.StepLaws (catalogue (Clock := Clock) (Var := Var)).PExpansion
      (catalogue (Clock := Clock) (Var := Var)).RuleClosedFor where
  current_mono hs := hs.extension.current.locals
  closed_mono hs := ruleClosed_mono hs.extension
  target_closed hs := hs.target_ruleClosed
  new_current := by
    intro p F G hs q hq hn
    refine ⟨?_, pExpansion_new_current_complexity hs hq hn⟩
    rcases hs with ⟨_, rfl⟩ | ⟨ho, _⟩
    · exact (hn hq).elim
    · exact ho

theorem alphaStepLaws [DecidableEq Clock] :
    ExpansionFamily.StepLaws (AlphaPExpansion (Clock := Clock) (Var := Var))
      (catalogue (Clock := Clock) (Var := Var)).RuleClosedFor where
  current_mono := by
    rintro p F G ⟨Fa, hp, hs⟩ l hl
    apply hs.extension.current.locals
    rw [hp.current]
    exact hl
  closed_mono := by
    rintro p F G ⟨Fa, hp, hs⟩ q hq
    exact ruleClosed_mono hs.extension q ((hp.ruleClosed_iff q).2 hq)
  target_closed := by
    rintro p F G ⟨Fa, hp, hs⟩
    exact hs.target_ruleClosed
  new_current := by
    rintro p F G ⟨Fa, hp, hs⟩ q hq hn
    have hnFa : Local.predicate q ∉ Fa.current.locals := by rwa [hp.current]
    obtain ⟨ho, hlt⟩ := literalStepLaws.new_current hs q hq hnFa
    exact ⟨fun h => ho ((hp.ruleClosed_iff p).2 h), hlt⟩

theorem literal_round_unclosed_origin [DecidableEq Clock]
    {F G : TransitionForm Clock Var} (h : catalogue.ExpansionRound F G)
    (q : Predicate Clock Var) (hq : Local.predicate q ∈ G.current.locals)
    (ho : ¬ catalogue.RuleClosedFor G q) :
    ∃ p, Local.predicate p ∈ F.current.locals ∧ ¬ catalogue.RuleClosedFor F p ∧
      q.complexity < p.complexity := h.unclosed_origin literalStepLaws q hq ho

theorem alpha_round_unclosed_origin [DecidableEq Clock]
    {F G : TransitionForm Clock Var} (h : AlphaExpansionRound F G)
    (q : Predicate Clock Var) (hq : Local.predicate q ∈ G.current.locals)
    (ho : ¬ catalogue.RuleClosedFor G q) :
    ∃ p, Local.predicate p ∈ F.current.locals ∧ ¬ catalogue.RuleClosedFor F p ∧
      q.complexity < p.complexity := h.unclosed_origin alphaStepLaws q hq ho

/-- Sequentially preserve truth and the full invariant while processing a
fixed list of current predicates, including every listed identity step. -/
theorem alpha_sequence_satisfied [DecidableEq Clock] [Infinite Clock]
    (ps : List (Predicate Clock Var)) (F : TransitionForm Clock Var)
    (hm : ∀ p ∈ ps, Local.predicate p ∈ F.current.locals)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : F.holds σ P α k) (hi : F.EvaluatedInvariant σ P α k)
    (hst : F.UnderlyingStable σ P) :
    ∃ G, AlphaExpansionSequence ps F G ∧ G.holds σ P α k ∧
      G.EvaluatedInvariant σ P α k ∧ G.UnderlyingStable σ P := by
  induction ps generalizing F with
  | nil => exact ⟨F, .nil F, hs, hi, hst⟩
  | cons p ps ih =>
      obtain ⟨Fa, G, hp, hexp, hsG, hiG, hstG⟩ :=
        satisfied_pExpansion_preserving F p (hm p List.mem_cons_self) σ P α k hs hi hst
      have hstep : AlphaPExpansion p F G := ⟨Fa, hp, hexp⟩
      obtain ⟨H, htail, hsH, hiH, hstH⟩ := ih G
        (fun q hq => alphaStepLaws.current_mono hstep (hm q (List.mem_cons_of_mem p hq)))
        hsG hiG hstG
      exact ⟨H, .cons hstep htail, hsH, hiH, hstH⟩

theorem alpha_round_satisfied [DecidableEq Clock] [Infinite Clock]
    (F : TransitionForm Clock Var) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : F.holds σ P α k) (hi : F.EvaluatedInvariant σ P α k)
    (hst : F.UnderlyingStable σ P) :
    ∃ G, AlphaExpansionRound F G ∧ G.holds σ P α k ∧
      G.EvaluatedInvariant σ P α k ∧ G.UnderlyingStable σ P := by
  obtain ⟨ps, hen⟩ := ExpansionFamily.exists_enumeration F
  obtain ⟨G, hseq, hsat, hInv, hStable⟩ := alpha_sequence_satisfied ps F
    (fun p hp => (hen.2 p).1 hp) σ P α k hs hi hst
  exact ⟨G, ⟨ps, hen, hseq⟩, hsat, hInv, hStable⟩

/-- The invariant-preserving witness belongs to the actual complete i-th
family, not merely to some independent terminating construction. -/
theorem alpha_level_satisfied [DecidableEq Clock] [Infinite Clock]
    (F : TransitionForm Clock Var) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : F.holds σ P α k) (hi : F.EvaluatedInvariant σ P α k)
    (hst : F.UnderlyingStable σ P) (i : ℕ) :
    ∃ G ∈ alphaExpansionLevel F i, G.holds σ P α k ∧
      G.EvaluatedInvariant σ P α k ∧ G.UnderlyingStable σ P := by
  induction i with
  | zero => exact ⟨F, rfl, hs, hi, hst⟩
  | succ i ih =>
      obtain ⟨G, hm, hsG, hiG, hstG⟩ := ih
      obtain ⟨H, hr, hsH, hiH, hstH⟩ := alpha_round_satisfied G σ P α k hsG hiG hstG
      exact ⟨H, ⟨G, hm, hr⟩, hsH, hiH, hstH⟩

theorem alpha_sequence_source [DecidableEq Clock]
    {ps : List (Predicate Clock Var)} {F G : TransitionForm Clock Var}
    (h : AlphaExpansionSequence ps F G) :
    ∃ Fa, NextAlphaPath F Fa ∧ SyntacticallySubsumed Fa G := by
  induction h with
  | nil F => exact ⟨F, .refl F, .refl F⟩
  | @cons p ps F H G hs ht ih =>
      obtain ⟨F', hp, hexp⟩ := hs
      obtain ⟨Ha, hpH, hHG⟩ := ih
      obtain ⟨Fa, hpF, hFH⟩ := NextAlphaPath.transport_subsumed hexp.extension hpH
      exact ⟨Fa, hp.trans hpF, hFH.trans hHG⟩

theorem alpha_round_source [DecidableEq Clock]
    {F G : TransitionForm Clock Var} (h : AlphaExpansionRound F G) :
    ∃ Fa, NextAlphaPath F Fa ∧ SyntacticallySubsumed Fa G := by
  obtain ⟨ps, hen, hseq⟩ := h
  exact alpha_sequence_source hseq

/-- The initial source is retained through the same scoped alpha choices
made by the actual level derivation. -/
theorem alpha_level_source [DecidableEq Clock] (F : TransitionForm Clock Var)
    (i : ℕ) {G : TransitionForm Clock Var} (hm : G ∈ alphaExpansionLevel F i) :
    ∃ Fa, NextAlphaPath F Fa ∧ SyntacticallySubsumed Fa G := by
  induction i generalizing G with
  | zero =>
      have he : G = F := hm
      subst G
      exact ⟨F, .refl F, .refl F⟩
  | succ i ih =>
      obtain ⟨H, hmH, hr⟩ := hm
      obtain ⟨Fa, hpF, hFH⟩ := ih hmH
      obtain ⟨Ha, hpH, hHG⟩ := alpha_round_source hr
      obtain ⟨Fa', hpF', hFH'⟩ := NextAlphaPath.transport_subsumed hFH hpH
      exact ⟨Fa', hpF.trans hpF', hFH'.trans hHG⟩

/-- Literal derivations are admitted by the explicit alpha convention. No
converse equality of literal and alpha families is asserted. -/
theorem literal_level_subset_alpha [DecidableEq Clock]
    (F : TransitionForm Clock Var) (i : ℕ) :
    catalogue.expansionLevel F i ⊆ alphaExpansionLevel F i :=
  ExpansionFamily.level_mono (fun {p G H} h => ⟨G, NextAlphaPath.refl G, h⟩) F i

end ConcreteContextual
end STLTableau.Section3
