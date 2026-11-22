import STLTableaux.Finiteness.ClockAllocation.CompatibleClockNames
import STLTableaux.Finiteness.Derivation.NormalizationRenaming
import STLTableaux.Closure.Normalization.FaithfulAlphaNormalization
import STLTableaux.Closure.Subsumption.FaithfulClosureOrder

/-! Finite-support clock permutations and syntactic interface compatibility.
Semantic path lifting and admissibility of renamed derivations remain separate. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

/-- Extend only the current finite-support injection, never all historical names. -/
theorem supported_clock_permutation (U Q : Finset Clock) (f : U → Q)
    (hf : Function.Injective f) :
    ∃ e : Equiv.Perm Clock, ∀ u : U, e u.val = (f u).val := by
  classical
  exact Equiv.Perm.exists_extending_pair (fun u : U => u.val)
    (fun u => (f u).val) Subtype.val_injective (Subtype.val_injective.comp hf)

 theorem compatible_clock_permutations (U E : Nat → Finset Clock) (Q : Finset Clock)
    (hl : ∀ i, E i ⊆ U i) (hr : ∀ i, E i ⊆ U (i + 1))
    (hc : ∀ i, (U i).card ≤ Q.card) :
    ∃ e : Nat → Equiv.Perm Clock,
      (∀ i c, c ∈ U i → e i c ∈ Q) ∧
      ∀ i c, c ∈ E i → e i c = e (i + 1) c := by
  classical
  obtain ⟨a, ha, he⟩ := compatible_clock_names U E Q.card hl hr hc
  let q : Fin Q.card ≃ Q := by simpa using (Fintype.equivFin Q).symm
  have ext (i : Nat) : ∃ e : Equiv.Perm Clock,
      ∀ u : U i, e u.val = (q (a i u)).val :=
    supported_clock_permutation (U i) Q (fun u => q (a i u)) (q.injective.comp (ha i))
  choose e h using ext
  refine ⟨e, ?_, ?_⟩
  · intro i c hc
    rw [h i ⟨c,hc⟩]
    exact (q (a i ⟨c,hc⟩)).property
  · intro i c hc
    rw [h i ⟨c,hl i hc⟩, h (i+1) ⟨c,hr i hc⟩, he i ⟨c,hc⟩]

 theorem local_rename_congr (l : Local Clock Var) (e f : Equiv.Perm Clock)
    (h : ∀ c ∈ l.freeClocks, e c = f c) : l.rename e = l.rename f := by
  cases l with
  | terminal => rfl
  | marker => rfl
  | predicate p =>
    cases p with
    | plain => rfl
    | upper c m k I φ =>
      have hc := h c (by simp [Local.freeClocks, Local.toJudgement, Section3.Judgement.freeClocks])
      simp only [Local.rename, Section3.Predicate.rename, hc]
    | bounded c d m n k I φ =>
      have hc := h c (by simp [Local.freeClocks, Local.toJudgement, Section3.Judgement.freeClocks])
      have hd := h d (by simp [Local.freeClocks, Local.toJudgement, Section3.Judgement.freeClocks])
      simp only [Local.rename, Section3.Predicate.rename, hc, hd]

 theorem reset_rename_congr (R : ClockResetSet Clock) (e f : Equiv.Perm Clock)
    (h : ∀ c ∈ R.clocks, e c = f c) : R.rename e = R.rename f := by
  have hv : (R.rename e).value = (R.rename f).value := by
    funext c
    change R.value (e.symm c) = R.value (f.symm c)
    by_cases he : ∃ a, R.value (e.symm c) = some a
    · have hh := h (e.symm c) he
      have hi : e.symm c = f.symm c := f.injective (by simpa using hh.symm)
      rw [hi]
    · by_cases hf : ∃ a, R.value (f.symm c) = some a
      · have hh := h (f.symm c) hf
        have hi : e.symm c = f.symm c := e.injective (by simpa using hh.symm)
        rw [hi]
      · cases hx : R.value (e.symm c) <;> cases hy : R.value (f.symm c) <;> simp_all
  cases hE : R.rename e with
  | mk ev ef =>
    cases hF : R.rename f with
    | mk fv ff =>
      simp only [hE, hF] at hv ⊢
      cases hv
      rfl

/-- All syntactic state clocks, including clocks bound by resets. -/
def stateClockSupport (S : Section3.StateForm Clock Var) : Set Clock :=
  S.guardClocks ∪ S.localClocks ∪ S.resets.clocks

 theorem state_rename_congr (S : Section3.StateForm Clock Var) (e f : Equiv.Perm Clock)
    (h : ∀ c ∈ stateClockSupport S, e c = f c) : S.rename e = S.rename f := by
  apply Section3.StateForm.ext_components
  · apply Set.image_congr
    intro g hg
    have hh := h g.clock (Or.inl (Or.inl ⟨g,hg,rfl⟩))
    simp [Section3.Guard.rename, hh]
  · exact reset_rename_congr S.resets e f (fun c hc => h c (Or.inr hc))
  · apply Set.image_congr
    intro l hl
    exact local_rename_congr l e f (fun c hc => h c (Or.inl (Or.inr ⟨l,hl,hc⟩)))

 theorem shared_state_rename (N : Section3.StateForm Clock Var) (E : Finset Clock)
    (e f : Equiv.Perm Clock) (hs : stateClockSupport N ⊆ (E : Set Clock))
    (he : ∀ c ∈ E, e c = f c) : N.rename e = N.rename f :=
  state_rename_congr N e f (fun c hc => he c (hs hc))

 theorem transition_support_eq (S : Section3.TransitionForm Clock Var) :
    S.allClocks = stateClockSupport S.current ∪
      (match S.nextPart with | none => ∅ | some N => stateClockSupport N) := by
  ext c
  cases hn : S.nextPart <;>
    simp only [Section3.TransitionForm.allClocks, Section3.TransitionForm.freeClocks,
      Section3.TransitionForm.bodyFreeClocks, Section3.TransitionForm.boundClocks,
      Section3.StateForm.freeClocks, stateClockSupport, hn,
      Set.mem_union, Set.mem_sdiff, Set.mem_empty_iff_false] <;> tauto

 theorem transition_rename_congr (S : Section3.TransitionForm Clock Var)
    (e f : Equiv.Perm Clock) (h : ∀ c ∈ S.allClocks, e c = f c) :
    renameTransition e S = renameTransition f S := by
  have hc := state_rename_congr S.current e f (fun c hc =>
    h c (by rw [transition_support_eq]; exact Or.inl hc))
  unfold renameTransition
  rw [hc]
  cases hn : S.nextPart with
  | none => rfl
  | some N =>
    have hN := state_rename_congr N e f (fun c hc =>
      h c (by rw [transition_support_eq, hn]; exact Or.inr hc))
    simp only [Option.map_some, hN]


end STLTableau.Section4.Finiteness
