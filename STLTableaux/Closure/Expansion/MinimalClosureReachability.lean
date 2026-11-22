import STLTableaux.Closure.Expansion.FaithfulExpansionRank

/-! Reachability of minimal closures by complete expansion rounds. The
search stays below a given closure and uses its fixed clock names. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace ExpansionFamily

theorem Sequence.append {Step : Predicate Clock Var → TransitionForm Clock Var →
    TransitionForm Clock Var → Prop} {ps qs F G H}
    (h : Sequence Step ps F G) (g : Sequence Step qs G H) :
    Sequence Step (ps ++ qs) F H := by
  induction h with
  | nil => exact g
  | cons hs ht ih => exact .cons hs (ih g)

theorem level_sequence {Step : Predicate Clock Var → TransitionForm Clock Var →
    TransitionForm Clock Var → Prop} (F : TransitionForm Clock Var) (i : ℕ)
    {G : TransitionForm Clock Var} (hm : G ∈ level Step F i) :
    ∃ ps, Sequence Step ps F G := by
  induction i generalizing G with
  | zero =>
      have he : G = F := hm
      subst G
      exact ⟨[], .nil F⟩
  | succ i ih =>
      obtain ⟨H, hH, qs, hen, hseq⟩ := hm
      obtain ⟨ps, hps⟩ := ih hH
      exact ⟨ps ++ qs, hps.append hseq⟩

end ExpansionFamily
namespace ConcreteContextual

/-- Process an enumeration while choosing each actual minimal p-expansion
below a fixed closed upper bound. -/
theorem literal_sequence_below [DecidableEq Clock]
    (ps : List (Predicate Clock Var)) (F U : TransitionForm Clock Var)
    (hm : ∀ p ∈ ps, Local.predicate p ∈ F.current.locals)
    (hFU : SyntacticallySubsumed F U) (hcU : catalogue.IsClosed U) :
    ∃ G, catalogue.ExpansionSequence ps F G ∧
      SyntacticallySubsumed F G ∧ SyntacticallySubsumed G U := by
  induction ps generalizing F with
  | nil => exact ⟨F, .nil F, .refl F, hFU⟩
  | cons p ps ih =>
      have hpU : Local.predicate p ∈ U.current.locals :=
        hFU.current.locals (hm p List.mem_cons_self)
      obtain ⟨H, hFH, hHU⟩ := catalogue.pExpansion_exists_below p hFU (hcU p hpU)
      obtain ⟨G, hseq, hHG, hGU⟩ := ih H
        (fun q hq => hFH.extension.current.locals (hm q (List.mem_cons_of_mem p hq)))
        hHU
      exact ⟨G, .cons hFH hseq, hFH.extension.trans hHG, hGU⟩

theorem literal_round_below [DecidableEq Clock]
    (F U : TransitionForm Clock Var) (hFU : SyntacticallySubsumed F U)
    (hcU : catalogue.IsClosed U) :
    ∃ G, catalogue.ExpansionRound F G ∧
      SyntacticallySubsumed F G ∧ SyntacticallySubsumed G U := by
  obtain ⟨ps, hen⟩ := ExpansionFamily.exists_enumeration F
  obtain ⟨G, hseq, hFG, hGU⟩ := literal_sequence_below ps F U
    (fun p hp => (hen.2 p).1 hp) hFU hcU
  exact ⟨G, ⟨ps, hen, hseq⟩, hFG, hGU⟩

/-- Every complete level has a member between the original source and its
fixed closed upper bound. -/
theorem literal_level_below [DecidableEq Clock]
    (F U : TransitionForm Clock Var) (hFU : SyntacticallySubsumed F U)
    (hcU : catalogue.IsClosed U) (i : ℕ) :
    ∃ G ∈ catalogue.expansionLevel F i,
      SyntacticallySubsumed F G ∧ SyntacticallySubsumed G U := by
  induction i with
  | zero => exact ⟨F, rfl, .refl F, hFU⟩
  | succ i ih =>
      obtain ⟨H, hm, hFH, hHU⟩ := ih
      obtain ⟨G, hr, hHG, hGU⟩ := literal_round_below H U hHU hcU
      exact ⟨G, ⟨H, hm, hr⟩, hFH.trans hHG, hGU⟩

/-- Every minimal closure belongs to a complete-round expansion level. -/
theorem minimal_closure_mem_expansion_level [DecidableEq Clock]
    {F U : TransitionForm Clock Var} (hc : catalogue.IsClosure F U) :
    ∃ i : ℕ, U ∈ catalogue.expansionLevel F i := by
  obtain ⟨i, hz⟩ := literal_level_rank_eventually_zero F
  obtain ⟨G, hm, hFG, hGU⟩ := literal_level_below F U hc.extension hc.closed i
  have hall := (ExpansionFamily.familyRank_zero_iff_closed
    (literal_expansionLevel_bounded F i)).1 (hz i le_rfl)
  have hcG : catalogue.IsClosed G := hall G hm
  have hUG := hc.minimal G hFG hcG hGU
  have he : G = U := hGU.antisymm hUG
  exact ⟨i, he ▸ hm⟩

/-- Explicit finite single-predicate expansion derivation, with literal
source and target clock names as in the given minimal closure. -/
theorem minimal_closure_expansion_sequence [DecidableEq Clock]
    {F U : TransitionForm Clock Var} (hc : catalogue.IsClosure F U) :
    ∃ ps, catalogue.ExpansionSequence ps F U := by
  obtain ⟨i, hm⟩ := minimal_closure_mem_expansion_level hc
  exact ExpansionFamily.level_sequence F i hm

end ConcreteContextual
end STLTableau.Section3
