import STLTableaux.Finiteness.Derivation.Pending.PendingComplexity
import STLTableaux.Finiteness.Derivation.DerivationNormalizationSoundness

/-! The actual zero-current-weight base of local completion. No resolution
witness is assumed and no neutral/empty judgement is introduced. The frozen
next requirement is already a permitted leaf, whatever its inner predicates. -/
namespace STLTableau.Section4.Finiteness.PendingCompletionBase
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

/-- Every current obligation with zero pending weight is an allowed literal
leaf or a conjunction/reset combination of such leaves. This returns the actual
Type-valued resolution witness, not just an existence or semantic assertion. -/
noncomputable def resolve_zero (J : MixedJ Clock Var) : pendingWeight J = 0 → Resolve J J J := by
  classical
  induction J with
  | terminal => exact fun _ => .leaf .terminal
  | clock c r a => exact fun _ => .leaf (.clock c r a)
  | marker m => exact fun _ => .leaf (.marker m)
  | next N ih => exact fun _ => .leaf (.next N)
  | predicate p =>
    intro hz
    by_cases hp : p.IsAtomic
    · exact .leaf (.atomic p hp)
    · have he : 3 ^ p.complexity = 0 := by
        simpa only [pendingWeight,if_neg hp] using hz
      have hpos : 0 < 3 ^ p.complexity := pow_pos (by omega) _
      exact False.elim ((Nat.ne_of_gt hpos) he)
  | conj J K ih ig =>
    intro hz
    change pendingWeight J + pendingWeight K = 0 at hz
    exact .conj (ih (Nat.add_eq_zero_iff.mp hz).1) (ig (Nat.add_eq_zero_iff.mp hz).2)
  | reset R J ih => exact fun hz => .reset R (ih hz)

theorem nonempty_resolve_zero (J : MixedJ Clock Var) (hz : pendingWeight J = 0) :
    Nonempty (Resolve J J J) := ⟨resolve_zero J hz⟩

/-- Since full and erased syntax coincide in this constructed base witness,
its successfully normalized form is already its own atomic projection. -/
theorem projection_fixed (J : MixedJ Clock Var) (hz : pendingWeight J = 0)
    {F : Section3.TransitionForm Clock Var} (hsafe : SafeNormalization J F) :
    F.atomicProjection = F := by
  have he := (resolve_zero J hz).normalize_erased_of_full hsafe.normalizes
  exact (Option.some.inj (hsafe.normalizes.symm.trans he)).symm

/-- The erased safety certificate follows automatically from the given full
certificate and zero weight, rather than being another assumed completion field. -/
theorem erased_safe (J : MixedJ Clock Var) (hz : pendingWeight J = 0)
    {F : Section3.TransitionForm Clock Var} (hsafe : SafeNormalization J F) :
    SafeNormalization J F.atomicProjection := by
  rw [projection_fixed J hz hsafe]
  exact hsafe

theorem zero_completion (J : MixedJ Clock Var) (hz : pendingWeight J = 0)
    {F : Section3.TransitionForm Clock Var} (hsafe : SafeNormalization J F) :
    Nonempty (Resolve J J J) ∧ F.atomicProjection = F ∧ SafeNormalization J F.atomicProjection :=
  ⟨nonempty_resolve_zero J hz,projection_fixed J hz hsafe,erased_safe J hz hsafe⟩

end STLTableau.Section4.Finiteness.PendingCompletionBase
