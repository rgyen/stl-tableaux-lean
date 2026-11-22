import STLTableaux.Finiteness.Inventory.FiniteInventory
import STLTableaux.Finiteness.Inventory.RootClockConstants
import STLTableaux.Closure.Normalization.NormalizedStability

/-! A finite cover of transition forms over fixed clock, formula, and
guard/reset constant inventories. -/
namespace STLTableau.FiniteClockFormInventory

open Section3
open Section4.Finiteness (FormConstantsWithin StateConstantsWithin)
open Section4.Finiteness.FiniteInventory

variable {Clock Var : Type*}

private def timed (s : TemporalKind × TimeInterval × Formula Var) : Formula Var :=
  match s.1 with
  | .always => Formula.always s.2.1 s.2.2
  | .eventually => Formula.eventually s.2.1 s.2.2

private theorem timed_injective : Function.Injective (timed (Var := Var)) := by
  rintro ⟨k, I, φ⟩ ⟨l, J, ψ⟩ h
  cases k <;> cases l <;>
    simp only [timed, Formula.eventually, Formula.always,
      Formula.neg.injEq, Formula.until.injEq, reduceCtorEq, true_and] at h
  all_goals rcases h with ⟨rfl, rfl⟩; rfl

private noncomputable def timings (P : Finset (Formula Var)) :
    Finset (TemporalKind × TimeInterval × Formula Var) :=
  (P.finite_toSet.preimage timed_injective.injOn).toFinset

private theorem timings_mem {P : Finset (Formula Var)}
    {s : TemporalKind × TimeInterval × Formula Var} (h : timed s ∈ P) :
    s ∈ timings P := by
  simpa [timings] using h

private theorem marker_rep (m : Marker) : ∃ b : Bool, mark b = m := by
  cases m
  · exact ⟨true, rfl⟩
  · exact ⟨false, rfl⟩

private theorem relation_rep (r : ClockRelation) : ∃ i : Fin 5, relationAt i = r := by
  cases r
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩

private noncomputable def localInventory (Q : Finset Clock) (P : Finset (Formula Var)) :
    Finset (Local Clock Var) := by
  classical
  let bits : Finset Bool := Finset.univ
  exact {Local.terminal, Local.marker .open, Local.marker .closed} ∪
    P.image (fun φ => Local.predicate (.plain φ)) ∪
    (Q.product (bits.product (timings P))).image
      (fun x => Local.predicate (.upper x.1 (mark x.2.1)
        x.2.2.1 x.2.2.2.1 x.2.2.2.2)) ∪
    (Q.product (Q.product (bits.product (bits.product (timings P))))).image
      (fun x => Local.predicate (.bounded x.1 x.2.1 (mark x.2.2.1) (mark x.2.2.2.1)
        x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2))

private theorem mem_localInventory (Q : Finset Clock) (P : Finset (Formula Var))
    (S : Section3.StateForm Clock Var) (hL : S.localClocks ⊆ (Q : Set Clock))
    (hP : S.underlyingFormulas ⊆ (P : Set (Formula Var))) :
    S.locals ⊆ (localInventory Q P : Set (Local Clock Var)) := by
  classical
  intro l hl
  have hcl : l.freeClocks ⊆ (Q : Set Clock) :=
    fun _ hc => hL ⟨l, hl, hc⟩
  change l ∈ localInventory Q P
  cases l with
  | terminal => simp [localInventory]
  | marker m => cases m <;> simp [localInventory]
  | predicate p =>
    have hp : p.formula ∈ P := hP ⟨p, hl, rfl⟩
    cases p with
    | plain φ =>
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨φ, hp, rfl⟩)))
    | upper c b kind I φ =>
      have hc : c ∈ Q := hcl (by simp [Local.freeClocks, Local.toJudgement, Section3.Judgement.freeClocks])
      obtain ⟨x, rfl⟩ := marker_rep b
      have hT : (kind,I,φ) ∈ timings P := timings_mem (by cases kind <;> exact hp)
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(c,x,kind,I,φ), by simp [hc,hT], rfl⟩
    | bounded c d b q kind I φ =>
      have hc : c ∈ Q := hcl (by simp [Local.freeClocks, Local.toJudgement, Section3.Judgement.freeClocks])
      have hd : d ∈ Q := hcl (by simp [Local.freeClocks, Local.toJudgement, Section3.Judgement.freeClocks])
      obtain ⟨x, rfl⟩ := marker_rep b
      obtain ⟨y, rfl⟩ := marker_rep q
      have hT : (kind,I,φ) ∈ timings P := timings_mem (by cases kind <;> exact hp)
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(c,d,x,y,kind,I,φ), by simp [hc,hd,hT], rfl⟩

private noncomputable def guardInventory (Q : Finset Clock) (C : Finset NNReal) :
    Finset (Guard Clock) := by
  classical
  exact (Q.product ((Finset.univ : Finset (Fin 5)).product C)).image
    fun x => ⟨x.1, relationAt x.2.1, x.2.2⟩

private theorem state_within (Q : Finset Clock) (P : Finset (Formula Var))
    (C : Finset NNReal) (S : Section3.StateForm Clock Var)
    (hL : S.localClocks ⊆ (Q : Set Clock))
    (hG : S.guardClocks ⊆ (Q : Set Clock))
    (hR : S.resets.clocks ⊆ (Q : Set Clock))
    (hP : S.underlyingFormulas ⊆ (P : Set (Formula Var)))
    (hC : StateConstantsWithin C S) :
    Within (localInventory Q P) (guardInventory Q C) (Q.product C) S := by
  classical
  refine ⟨mem_localInventory Q P S hL hP, ?_, ?_⟩
  · rintro ⟨c,r,a⟩ hg
    have hc : c ∈ Q := hG ⟨⟨c,r,a⟩, hg, rfl⟩
    have ha : a ∈ C := hC.1 _ hg
    obtain ⟨i, rfl⟩ := relation_rep r
    exact Finset.mem_image.mpr ⟨(c,i,a), by simp [hc,ha], rfl⟩
  · intro c a h
    exact Finset.mem_product.mpr ⟨hR ⟨a,h⟩, hC.2 c a h⟩

theorem finite_cover (Q : Finset Clock) (P : Finset (Formula Var)) (C : Finset NNReal) :
    ∃ T : Set (Section3.TransitionForm Clock Var), T.Finite ∧
      ∀ F : Section3.TransitionForm Clock Var, F.allClocks ⊆ (Q : Set Clock) →
        F.underlyingFormulas ⊆ (P : Set (Formula Var)) →
        FormConstantsWithin C F → F ∈ T := by
  classical
  refine ⟨_, transition_finite (localInventory Q P) (guardInventory Q C) (Q.product C), ?_⟩
  intro F hQ hP hC
  refine ⟨state_within Q P C F.current ?_ ?_ ?_ ?_ hC.1, ?_⟩
  · intro c hc
    by_cases hr : c ∈ F.current.resets.clocks
    · exact hQ (Or.inr (Or.inl hr))
    · exact hQ (Or.inl (Or.inr ⟨Or.inl hc, hr⟩))
  · exact fun _ hc => hQ (Or.inl (Or.inl hc))
  · exact fun _ hc => hQ (Or.inr (Or.inl hc))
  · exact fun _ hp => hP (Or.inl hp)
  · intro N hn
    refine state_within Q P C N ((Section3.TransitionForm.nextLocalClocks_subset_all hn).trans hQ)
      ?_ (fun _ hc => hQ (Or.inr (Section3.TransitionForm.nextResets_subset_bound hn hc))) ?_ (hC.2 N hn)
    · intro c hc
      by_cases hr : c ∈ F.current.resets.clocks
      · exact hQ (Or.inr (Or.inl hr))
      · have hb : c ∈ F.bodyFreeClocks := by
          unfold Section3.TransitionForm.bodyFreeClocks
          rw [hn]
          exact Or.inr (Or.inl hc)
        exact hQ (Or.inl (Or.inr ⟨hb,hr⟩))
    · intro φ hp
      apply hP
      unfold Section3.TransitionForm.underlyingFormulas
      rw [hn]
      exact Or.inr hp

end STLTableau.FiniteClockFormInventory
