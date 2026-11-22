import STLTableaux.Closure.Normalization.FaithfulAlphaNormalization
import STLTableaux.Finiteness.Inventory.FiniteInventory
import STLTableaux.Finiteness.ClockAllocation.CompatibleClockNames

/-! Clock support of actual mixed transition forms in the sparse inventory.
This does not establish representative-path membership in that inventory. -/
namespace STLTableau.Section4.Finiteness.FiniteInventory
open Section3
variable {Clock Var Slot : Type*} [Fintype Slot]

 theorem clockAt_mem (t : Slot → Triple Clock Var) (s : Slot) (i : Fin 3) :
    clockAt (t s) i ∈ clocks t := by
  classical
  exact Finset.mem_image.mpr ⟨(s,i), Finset.mem_univ _, rfl⟩

 theorem local_support (P : Finset (Formula Var)) (t : Slot → Triple Clock Var)
    {l : Local Clock Var} (hl : l ∈ locals P t) : l.freeClocks ⊆ (clocks t : Set Clock) := by
  classical
  rcases Finset.mem_union.mp hl with h | h
  · rcases Finset.mem_union.mp h with h | h
    · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp h
      cases b with
      | none => simp [Local.freeClocks, Local.toJudgement, Section3.Judgement.freeClocks]
      | some b => simp [Local.freeClocks, Local.toJudgement, Section3.Judgement.freeClocks]
    · obtain ⟨φ, _, rfl⟩ := Finset.mem_image.mp h
      simp [Local.freeClocks, Local.toJudgement, Section3.Judgement.freeClocks]
  · obtain ⟨⟨s,tag⟩, _, rfl⟩ := Finset.mem_image.mp h
    have h₀ := clockAt_mem t s 0
    have h₁ := clockAt_mem t s 1
    have h₂ := clockAt_mem t s 2
    simp only [clockAt] at h₀ h₁ h₂
    rcases tag with b | ⟨r,b,q⟩
    · simpa [slotLocal, Local.freeClocks, Local.toJudgement, Section3.Judgement.freeClocks] using h₀
    · cases r <;> simp_all [slotLocal, Local.freeClocks, Local.toJudgement,
        Section3.Judgement.freeClocks, Set.insert_subset_iff, Set.singleton_subset_iff]

 theorem guard_support (t : Slot → Triple Clock Var) {g : Guard Clock}
    (hg : g ∈ guards t) : g.clock ∈ clocks t := by
  classical
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hg
  exact clockAt_mem t x.1 x.2.1

 theorem reset_support (t : Slot → Triple Clock Var) {c : Clock} {a : NNReal}
    (hr : (c,a) ∈ resets t) : c ∈ clocks t := by
  classical
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hr
  have h : clockAt (t x.1) x.2.1 = c := congrArg Prod.fst hx
  rw [← h]
  exact clockAt_mem t x.1 x.2.1

 theorem within_support (P : Finset (Formula Var)) (t : Slot → Triple Clock Var)
    {S : Section3.StateForm Clock Var} (hS : Within (locals P t) (guards t) (resets t) S) :
    S.guardClocks ∪ S.localClocks ∪ S.resets.clocks ⊆ (clocks t : Set Clock) := by
  rintro c ((⟨g,hg,rfl⟩ | ⟨l,hl,hc⟩) | ⟨a,ha⟩)
  · exact guard_support t (hS.2.1 hg)
  · exact local_support P t (hS.1 hl) hc
  · exact reset_support t (hS.2.2 c a ha)

 theorem transition_allClocks_subset (P : Finset (Formula Var))
    (t : Slot → Triple Clock Var) {S : Section3.TransitionForm Clock Var}
    (hS : TransitionWithin (locals P t) (guards t) (resets t) S) :
    S.allClocks ⊆ (clocks t : Set Clock) := by
  have hc := within_support P t hS.1
  have hn := fun N h => within_support P t (hS.2 N h)
  cases he : S.nextPart with
  | none =>
    simp only [Section3.TransitionForm.allClocks, Section3.TransitionForm.freeClocks,
      Section3.TransitionForm.bodyFreeClocks, Section3.TransitionForm.boundClocks, he]
    intro c h
    rcases h with (h | ⟨h | h, _⟩) | h | h
    · exact hc (Or.inl (Or.inl h))
    · exact hc (Or.inl (Or.inr h))
    · exact False.elim h
    · exact hc (Or.inr h)
    · exact False.elim h
  | some N =>
    have hN := hn N he
    simp only [Section3.TransitionForm.allClocks, Section3.TransitionForm.freeClocks,
      Section3.TransitionForm.bodyFreeClocks, Section3.TransitionForm.boundClocks, he,
      Section3.StateForm.freeClocks]
    intro c h
    rcases h with (h | ⟨h | h | ⟨h, _⟩, _⟩) | h | h
    · exact hc (Or.inl (Or.inl h))
    · exact hc (Or.inl (Or.inr h))
    · exact hN (Or.inl (Or.inl h))
    · exact hN (Or.inl (Or.inr h))
    · exact hc (Or.inr h)
    · exact hN (Or.inr h)

 theorem transition_allClocks_card_le (P : Finset (Formula Var))
    (t : Slot → Triple Clock Var) {S : Section3.TransitionForm Clock Var}
    (hS : TransitionWithin (locals P t) (guards t) (resets t) S) :
    S.allClocks_finite.toFinset.card ≤ 3 * Fintype.card Slot := by
  classical
  exact (Finset.card_le_card (by
    intro c hc
    exact transition_allClocks_subset P t hS (by simpa using hc))).trans (clocks_card_le t)

end STLTableau.Section4.Finiteness.FiniteInventory
