import STLTableaux.Finiteness.Derivation.Derivation
import STLTableaux.Closure.Subsumption.FaithfulClosureOrder

/-! Automatic correspondence between a resolution tree's full annotations and
its erased output under the actual syntactic normalizer. No semantic correctness
of normalization, reset compatibility, or resolution existence is asserted. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

/-- Every actual raw expansion has a non-atomic source. -/
theorem RawBranch.source_nonatomic [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B) : ¬ p.IsAtomic := by
  cases h with
  | finite rule _ =>
    cases rule <;> simp [Predicate.ofFinite,Predicate.IsAtomic,
      Formula.or,Formula.always,Formula.eventually,Formula.release,Formula.untimedUntil]
  | infinite rule _ => cases rule <;> simp [Predicate.ofUnbounded,Predicate.IsAtomic]
  | opening c m kind a φ =>
    cases kind <;> simp [UnboundedClocked.formula,Predicate.IsAtomic,
      Formula.always,Formula.eventually]

namespace DerivationNormalization

theorem projection_union (F G : Section3.TransitionForm Clock Var) :
    (F.union G).atomicProjection = F.atomicProjection.union G.atomicProjection := by
  apply congrArg₂ Section3.TransitionForm.mk
  · apply Section3.StateForm.ext_components
    · rfl
    · rfl
    · ext l
      simp only [Section3.TransitionForm.atomicProjection,Section3.TransitionForm.restrictCurrent,
      Section3.TransitionForm.union,Section3.StateForm.union,Set.mem_setOf_eq,Set.mem_union]
      exact or_and_right
  · rfl

theorem projection_underReset (R : ClockResetSet Clock) (F : Section3.TransitionForm Clock Var) :
    (F.underReset R).atomicProjection = F.atomicProjection.underReset R := rfl

theorem projection_eq_self (F : Section3.TransitionForm Clock Var)
    (h : ∀ l ∈ F.current.locals, Section3.TransitionForm.KeepAtomic l) :
    F.atomicProjection = F := by
  apply congrArg₂ Section3.TransitionForm.mk
  · apply Section3.StateForm.ext_components
    · rfl
    · rfl
    · ext l
      exact ⟨fun hl => hl.1,fun hl => ⟨hl,h l hl⟩⟩
  · rfl

/-- The retained source changes only current locals; projection removes it.
No source clock assignment, guard or next part is discarded by this lemma. -/
theorem projection_add_nonatomic (p : Predicate Clock Var) (hp : ¬ p.IsAtomic)
    (F : Section3.TransitionForm Clock Var) :
    ((Section3.TransitionForm.ofState (Section3.StateForm.ofLocal (.predicate p))).union F).atomicProjection =
      F.atomicProjection := by
  apply congrArg₂ Section3.TransitionForm.mk
  · apply Section3.StateForm.ext_components
    · exact Set.empty_union _
    · change ClockResetSet.empty.union F.current.resets = F.current.resets
      have hempty : ∀ R : ClockResetSet Clock, ClockResetSet.empty.union R = R := by
        intro R
        cases R
        rfl
      exact hempty _
    · ext l
      change ((l ∈ ({Local.predicate p} : Set _) ∨ l ∈ F.current.locals) ∧
        Section3.TransitionForm.KeepAtomic l) ↔
          l ∈ F.current.locals ∧ Section3.TransitionForm.KeepAtomic l
      constructor
      · rintro ⟨hl,ha⟩
        rcases hl with hl | hl
        · have he : l = Local.predicate p := hl
          subst l
          exact False.elim (hp ha)
        · exact ⟨hl,ha⟩
      · exact fun h => ⟨Or.inr h.1,h.2⟩
  · rfl

/-- Stopping is permitted only at atomic current requirements or a frozen next
body. Both normalize to forms whose current locals are already atomic. -/
theorem leaf_projection (J : MixedJ Clock Var) (h : ResolutionLeaf J) :
    Section3.TransitionForm.normalize? J =
      (Section3.TransitionForm.normalize? J).map Section3.TransitionForm.atomicProjection := by
  cases h with
  | terminal =>
    apply congrArg some
    exact (projection_eq_self _ (by intro l hl; have he : l = .terminal := hl; subst l; trivial)).symm
  | clock c r a =>
    apply congrArg some
    exact (projection_eq_self _ (by intro l hl; exact False.elim hl)).symm
  | marker m =>
    apply congrArg some
    exact (projection_eq_self _ (by intro l hl; have he : l = .marker m := hl; subst l; trivial)).symm
  | atomic p hp =>
    apply congrArg some
    exact (projection_eq_self _ (by intro l hl; have he : l = .predicate p := hl; subst l; exact hp)).symm
  | next N =>
    cases hn : Section3.TransitionForm.normalize? N with
    | none => simp [Section3.TransitionForm.normalize?,hn]
    | some F =>
      cases hnext : F.nextPart with
      | some G => simp [Section3.TransitionForm.normalize?,hn,hnext]
      | none =>
        have he := projection_eq_self (Section3.TransitionForm.ofNextState F.current)
          (by intro l hl; exact False.elim hl)
        simpa [Section3.TransitionForm.normalize?,hn,hnext] using (congrArg some he).symm

end DerivationNormalization

/-- Normalizing the erased output gives the atomic projection of the
normalized full output. The projection retains guards, resets, and the
next part. The equality also covers failed normalization. -/
theorem Resolve.normalize_erased_eq_projection [DecidableEq Clock]
    {J H A : MixedJ Clock Var} (D : Resolve J H A) :
    Section3.TransitionForm.normalize? A =
      (Section3.TransitionForm.normalize? H).map Section3.TransitionForm.atomicProjection := by
  induction D with
  | leaf h => exact DerivationNormalization.leaf_projection _ h
  | @conj J K H G A B D E ih ig =>
    cases hH : Section3.TransitionForm.normalize? H with
    | none => simp [Section3.TransitionForm.normalize?,ih,hH]
    | some F =>
      cases hG : Section3.TransitionForm.normalize? G with
      | none => simp [Section3.TransitionForm.normalize?,ih,ig,hH,hG]
      | some G =>
        simp only [Section3.TransitionForm.normalize?,ih,ig,hH,hG,Option.map_some]
        exact congrArg some (DerivationNormalization.projection_union F G).symm
  | @reset R J H A D ih =>
    cases hH : Section3.TransitionForm.normalize? H with
    | none => simp [Section3.TransitionForm.normalize?,ih,hH]
    | some F =>
      simp only [Section3.TransitionForm.normalize?,ih,hH,Option.map_some]
      exact congrArg some (DerivationNormalization.projection_underReset R F).symm
  | structural _ D ih => exact ih
  | @expandCtx p B Γ H A hraw hp hf D ih =>
    cases hH : Section3.TransitionForm.normalize? H with
    | none => simp [Section3.TransitionForm.normalize?,ih,hH]
    | some F =>
      simp only [Section3.TransitionForm.normalize?,ih,hH,Option.map_some]
      exact congrArg some (DerivationNormalization.projection_add_nonatomic p hp F).symm
  | @expandSolo p B H A hraw hp hf D ih =>
    cases hH : Section3.TransitionForm.normalize? H with
    | none => simp [Section3.TransitionForm.normalize?,ih,hH]
    | some F =>
      simp only [Section3.TransitionForm.normalize?,ih,hH,Option.map_some]
      exact congrArg some (DerivationNormalization.projection_add_nonatomic p hp F).symm
  | boundaryRequired _ _ D ih => exact ih
  | boundaryOptional _ _ D ih => exact ih
  | unusedReset _ _ _ _ D ih => exact ih

/-- A single successful normalization of the full output suffices; the erased
normalization equation is a theorem, not a second certification premise. -/
theorem Resolve.normalize_erased_of_full [DecidableEq Clock]
    {J H A : MixedJ Clock Var} (D : Resolve J H A)
    {F : Section3.TransitionForm Clock Var} (hF : Section3.TransitionForm.normalize? H = some F) :
    Section3.TransitionForm.normalize? A = some F.atomicProjection := by
  rw [D.normalize_erased_eq_projection,hF]
  rfl

end STLTableau.Section4.Finiteness
