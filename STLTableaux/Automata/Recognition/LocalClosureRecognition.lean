import STLTableaux.Automata.Translation.LocalClosureGraph

/-! Transferring recognition to the original finite tableau. The only
additional edge has an empty final continuation. Its deletion here is a
comparison of tableau languages, not a deletion of an execution jump. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
variable (X : Set Var) (root : Formula.NormalizedInput Var)
local notation "T" => (inputTableau (Clock := Clock) X root)
local notation "U" => (localClosureGraph (Clock := Clock) X root)
local notation "Tr" => Section3.TransitionForm Clock Var
local notation "labs" => (JudgementTableau.labels (Clock := Clock) (Var := Var))
local notation "hfin" => (JudgementTableau.labels_finite (Clock := Clock) (Var := Var))

private theorem no_edge_from_empty {l : EdgeLabel Clock} {s : Tr}
    (he : (emptyMode,l,s) ∈ (U).edges) : False := by
  rcases he.1 with old | added
  · obtain ⟨_,_,N,hn,_,_⟩ := old.1
    cases hn
  · exact added.2.1 rfl

private theorem transferPath (p : Path Clock Tr) (hv : p.valid U)
    (hs : p.firstState ∈ (T).states) (hf : p.lastState ∈ (U).final) :
    ∃ q : Path Clock Tr, q.accepting T ∧ q.firstIncoming = p.firstIncoming ∧
      q.firstState = p.firstState ∧ ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
        (α : ClockValuation Clock) k,
        (p.trace labs hfin).holds σ P α k → (q.trace labs hfin).holds σ P α k := by
  induction p with
  | last l s =>
    have hsf : s ∈ (T).final := by
      rcases hf.1 with hem | old
      · exact ⟨show s.nextPart = none by rw [show s = emptyMode from hem]; rfl,hs⟩
      · exact old
    exact ⟨.last l s,⟨hs,hsf⟩,rfl,rfl,fun _ _ _ _ => id⟩
  | step l s p ih =>
    rcases hv.2.2.1 with old | added
    · obtain ⟨q,hq,hl,hstate,ht⟩ := ih hv.2.1 old.2.2 hf
      refine ⟨.step l s q,⟨⟨hs,hq.1,?_⟩,hq.2⟩,rfl,rfl,?_⟩
      · simpa only [hl,hstate] using old
      · intro σ P α k hholds
        have hhead := hholds.1
        have htail := hholds.2
        refine ⟨hhead,?_⟩
        by_cases hk : k.val < P.size
        · simp only [dif_pos hk] at htail ⊢
          exact ht _ _ _ _ htail
        · simp only [dif_neg hk] at htail
    · obtain ⟨hfinal,_,hlabel,hstate⟩ := added
      cases p with
      | step l' s' p' =>
        change s' = emptyMode at hstate
        subst s'
        exact (no_edge_from_empty X root hv.2.1.2.2).elim
      | last l' s' =>
        exact ⟨.last l s,⟨hs,hfinal⟩,rfl,rfl,fun _ _ _ _ ht => ht.1⟩

theorem recognizes_original_of_localClosure (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (h : (U).recognizes hfin σ P) :
    (T).recognizes hfin σ P := by
  obtain ⟨p,hr,ha,ht⟩ := h
  have hi : (p.firstIncoming,p.firstState) ∈ (T).initial := hr.2.1
  obtain ⟨q,hq,hl,hstate,hs⟩ := transferPath X root p hr.1 hi.2 ha.2
  exact ⟨q,⟨hq.1,by rw [hl,hstate]; exact hi⟩,hq,fun α => hs _ _ _ _ (ht α)⟩

theorem original_formula_of_localClosure_recognizes (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (h : (U).recognizes hfin σ P) :
    σ.Satisfies root.val ⟨0,le_rfl,σ.horizon_pos⟩ :=
  finiteRootTableau_sound X root.val σ P (recognizes_original_of_localClosure X root σ P h)

omit [DecidableEq Clock] [Infinite Clock] in
/-- The local consistency filter cannot discard an actually satisfied
state form, even at the terminal position. -/
private theorem consistent_of_state {N : Section3.StateForm Clock Var}
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain} {α : ClockValuation Clock} {k}
    (hn : N.holds σ P α k) : ConsistentPart N := by
  intro ht l hl
  have hend : k.val = P.size := hn.2 .terminal ht
  have h := hn.2 l hl
  cases l with
  | terminal => exact Or.inl rfl
  | predicate p =>
    simp [Local.holds,Local.toJudgement,Section3.Judgement.holds,hend] at h
  | marker m =>
    have he : m = ● := by
      simpa [Local.holds,Local.toJudgement,Section3.Judgement.holds,hend] using h
    exact Or.inr (congrArg Local.marker he)

omit [DecidableEq Clock] [Infinite Clock] in
private theorem consistent_of_form {F : Tr} {σ : FiniteSignal Var}
    {P : IntervalPartition σ.domain} {α : ClockValuation Clock} {k}
    (hf : F.holds σ P α k) : ConsistentClosure F := by
  refine ⟨consistent_of_state hf.1,?_⟩
  intro N hN
  have hn := hf.2
  simp only [show F.nextPart = some N from hN] at hn
  by_cases hk : k.val < P.size
  · simp only [dif_pos hk] at hn
    exact consistent_of_state hn
  · simp only [dif_neg hk] at hn

private theorem all_consistent (Q : Set Clock) (seed : Section3.StateForm Clock Var)
    (p : Path Clock Tr) (ha : p.accepting (JudgementTableau.tableau X Q seed Derives))
    (he : p.firstIncoming = JudgementTableau.incoming p.firstState)
    {N : Section3.StateForm Clock Var} (hN : Derives N p.firstState)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hi : N.EvaluatedNumeric σ P α k)
    (hs : (p.trace labs hfin).holds σ P α k) :
    Subgraph.AllStates {F | ConsistentClosure F} p := by
  induction p generalizing N α k with
  | last =>
    exact consistent_of_form (JudgementTableau.fullTrace_and_input_of_atomic_trace
      Derives derives_localLaws X Q seed _ ha he N hN σ P α k hi hs).2.1
  | step l F t ih =>
    have hf := (JudgementTableau.fullTrace_and_input_of_atomic_trace Derives derives_localLaws
      X Q seed _ ha he N hN σ P α k hi hs).2.1
    refine ⟨consistent_of_form hf,?_⟩
    obtain ⟨_,_,M,hn,hd,hlabel⟩ := ha.1.2.2
    have hnp := JudgementTableau.nonPredicate_of_atomic_trace Derives derives_localLaws
      X Q seed _ ha he σ P α k hs
    have hnum := derives_localLaws.numeric hN σ P α k hi hnp
    change l = JudgementTableau.incoming F at he
    subst l
    change _ ∧ (if hk : k.val < P.size then _ else False) at hs
    by_cases hk : k.val < P.size
    · simp only [dif_pos hk] at hs
      exact ih ⟨ha.1.2.1,ha.2⟩ hlabel hd _ _ (hnum.2 M hn hk) hs.2
    · simp only [dif_neg hk] at hs
      exact hs.2.elim

private theorem valid_in_extended (p : Path Clock Tr) (hp : p.valid T) :
    p.valid (withEmptyContinuation X root) := by
  induction p with
  | last => exact Or.inr hp
  | step l s t ih => exact ⟨Or.inr hp.1,ih hp.2.1,Or.inl hp.2.2⟩

/-- Local contradiction checks and the empty continuation do not change
which signals are recognized on a given partition. -/
theorem localClosure_recognizes_iff_original (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) :
    (U).recognizes hfin σ P ↔ (T).recognizes hfin σ P := by
  refine ⟨recognizes_original_of_localClosure X root σ P,?_⟩
  rintro ⟨p,hr,ha,hs⟩
  have hrun := ((Subgraph.run_iff _ _ p).mp hr).1
  have hacc := ((Subgraph.accepting_iff _ _ p).mp ha).1
  let α : ClockValuation Clock := fun _ => 0
  have hi : (Section3.StateForm.ofLocal (.predicate (.plain root.val))).EvaluatedNumeric
      σ P α ⟨0,by omega⟩ := by
    intro l hl
    have he : l = .predicate (.plain root.val) := hl
    subst l
    intro hk
    trivial
  have hall := all_consistent X _ _ p hacc hrun.2.2 hrun.2.1 σ P α ⟨0,by omega⟩ hi (hs α)
  have hvalid := valid_in_extended X root p hr.1
  exact ⟨p,(Subgraph.run_iff _ _ p).mpr ⟨⟨hvalid,hr.2⟩,hall⟩,
    (Subgraph.accepting_iff _ _ p).mpr ⟨⟨hvalid,Or.inr ha.2⟩,hall⟩,hs⟩

end STLTableau.Section4.Finiteness
