import STLTableaux.Finiteness.Derivation.Derivation
import STLTableaux.Syntax.FaithfulNormalizedSyntax

/-! Purely syntactic readiness propagation through finite resolution trees.
This concerns normalized formula grammar and distinct bounded endpoint names;
it assumes no satisfaction or semantic admission criterion. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

theorem RawBranch.ready [DecidableEq Clock] {p : Predicate Clock Var}
    {B : MixedJ Clock Var} (h : RawBranch p B) (hp : p.Ready) : B.Ready := by
  cases h with
  | finite rule member => exact ConcreteFinite.raw_ready rule hp member
  | infinite rule member => exact ConcreteInfinite.raw_ready rule hp member
  | opening c m kind a φ =>
      cases kind <;>
        simpa [Predicate.Ready,UnboundedClocked.formula,UnboundedClocked.opening,
          Judgement.ofUnbounded,Judgement.Ready,Predicate.ofUnbounded] using hp

theorem ACIdem.ready_iff {J K : MixedJ Clock Var} (h : ACIdem J K) : J.Ready ↔ K.Ready := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig
  | assoc => exact and_assoc
  | comm => exact and_comm
  | idem => exact and_self_iff
  | conj h g ih ig => exact and_congr ih ig
  | reset R h ih => exact ih
  | resetDistrib R J K => rfl
  | resetUnused R J hd => rfl
  | resetNested R S J => rfl

theorem withBoundaryGuard_ready (c : Clock) (b : Marker) (Γ : MixedJ Clock Var) :
    (withBoundaryGuard c b Γ).Ready ↔ Γ.Ready := by
  cases b <;> simp [withBoundaryGuard,Judgement.Ready]

/-- Ready input grammar propagates to both the retained full output and the
atomic/next leaves, through actual branches and exact boundary patterns. -/
theorem Resolve.ready [DecidableEq Clock] {J H A : MixedJ Clock Var}
    (D : Resolve J H A) (hi : J.Ready) : H.Ready ∧ A.Ready := by
  induction D with
  | leaf h => exact ⟨hi,hi⟩
  | conj D E ih ig =>
      obtain ⟨hH,hA⟩ := ih hi.1
      obtain ⟨hG,hB⟩ := ig hi.2
      exact ⟨⟨hH,hG⟩,⟨hA,hB⟩⟩
  | reset R D ih => exact ih hi
  | structural h D ih => exact ih (h.ready_iff.1 hi)
  | expandCtx hb hn hf D ih =>
      obtain ⟨hH,hA⟩ := ih ⟨hb.ready hi.1,hi.2⟩
      exact ⟨⟨hi.1,hH⟩,hA⟩
  | expandSolo hb hn hf D ih =>
      obtain ⟨hH,hA⟩ := ih (hb.ready hi)
      exact ⟨⟨hi,hH⟩,hA⟩
  | boundaryRequired frozen hdΓ D ih =>
      exact ih ⟨hi.1.1.2,trivial,(withBoundaryGuard_ready _ _ _).2 hi.2.2⟩
  | boundaryOptional frozen hdΓ D ih =>
      exact ih ⟨hi.1.2,trivial,(withBoundaryGuard_ready _ _ _).2 hi.2.2⟩
  | unusedReset d v hdJ hdH D ih => exact ih hi

end STLTableau.Section4.Finiteness
