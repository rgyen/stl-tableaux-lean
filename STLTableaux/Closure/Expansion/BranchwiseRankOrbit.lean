import STLTableaux.Closure.Expansion.BranchwiseRename
import STLTableaux.Closure.Expansion.BranchwiseRank

/-! Definition 4.18 compares current labels modulo clock permutations
fixing the initial transition form. Every exact one-step family is
already invariant under these permutations, so its quotient rank equals
the literal rank. -/
namespace STLTableau.Section3.ConcreteContextual

open BranchwiseExpansion
open STLTableau.Section4.Finiteness
variable {Clock Var : Type*}

private theorem fixes_inverse (F : TransitionForm Clock Var) (e : Equiv.Perm Clock)
    (h : ∀ c ∈ F.allClocks, e c = c) :
    ∀ c ∈ F.allClocks, e.symm c = c := by
  intro c hc
  exact e.symm_apply_eq.mpr (h c hc).symm

theorem alphaBranchwiseExpansionLevel_rename [DecidableEq Clock]
    (F : TransitionForm Clock Var) (e : Equiv.Perm Clock)
    (hfix : ∀ c ∈ F.allClocks, e c = c) (i : ℕ)
    {G : TransitionForm Clock Var} (h : G ∈ alphaBranchwiseExpansionLevel F i) :
    renameTransition e G ∈ alphaBranchwiseExpansionLevel F i := by
  induction i generalizing G with
  | zero =>
    have he : G = F := h
    exact he ▸ renameTransition_eq_of_fixes e F hfix
  | succ i ih =>
    obtain ⟨A, hA, p, hp, hs⟩ := mem_level_succ.mp h
    exact ⟨renameTransition e A, ih hA, p.rename e,
      (branchwiseCurrent_rename_iff e A p).mpr hp, hs.rename e⟩

theorem alphaBranchwiseExpansionLevel_rename_iff [DecidableEq Clock]
    (F : TransitionForm Clock Var) (e : Equiv.Perm Clock)
    (hfix : ∀ c ∈ F.allClocks, e c = c) (i : ℕ) (G : TransitionForm Clock Var) :
    renameTransition e G ∈ alphaBranchwiseExpansionLevel F i ↔
      G ∈ alphaBranchwiseExpansionLevel F i := by
  constructor
  · intro h
    simpa only [renameTransition_inverse] using
      alphaBranchwiseExpansionLevel_rename F e.symm (fixes_inverse F e hfix) i h
  · exact alphaBranchwiseExpansionLevel_rename F e hfix i

abbrev branchwiseLabels [DecidableEq Clock] (F : TransitionForm Clock Var) (i : ℕ) :
    Set (Predicate Clock Var) :=
  labels AlphaBranchwisePExpansion branchwiseCurrent F i

private theorem branchwiseLabels_rename [DecidableEq Clock]
    (F : TransitionForm Clock Var) (e : Equiv.Perm Clock)
    (hfix : ∀ c ∈ F.allClocks, e c = c) (i : ℕ)
    {p : Predicate Clock Var} (h : p ∈ branchwiseLabels F i) :
    p.rename e ∈ branchwiseLabels F i := by
  obtain ⟨G, hG, hp⟩ := mem_labels.mp h
  exact ⟨renameTransition e G, alphaBranchwiseExpansionLevel_rename F e hfix i hG,
    (branchwiseCurrent_rename_iff e G p).mpr hp⟩

theorem branchwiseLabels_rename_iff [DecidableEq Clock]
    (F : TransitionForm Clock Var) (e : Equiv.Perm Clock)
    (hfix : ∀ c ∈ F.allClocks, e c = c) (i : ℕ) (p : Predicate Clock Var) :
    p.rename e ∈ branchwiseLabels F i ↔ p ∈ branchwiseLabels F i := by
  constructor
  · intro h
    simpa only [predicate_rename_inverse] using
      branchwiseLabels_rename F e.symm (fixes_inverse F e hfix) i h
  · exact branchwiseLabels_rename F e hfix i

/-- The relative clock-renaming equivalence; all initial free and
bound names are fixed. It is applied to current predicates only. -/
def rootClockOrbit (F : TransitionForm Clock Var) : Setoid (Predicate Clock Var) where
  r p q := ∃ e : Equiv.Perm Clock, (∀ c ∈ F.allClocks, e c = c) ∧ p.rename e = q
  iseqv := {
    refl := fun p => ⟨Equiv.refl _, fun _ _ => rfl, predicate_rename_refl p⟩
    symm := by
      rintro p q ⟨e, hf, rfl⟩
      exact ⟨e.symm, fixes_inverse F e hf, predicate_rename_inverse e p⟩
    trans := by
      rintro p q r ⟨e, he, rfl⟩ ⟨f, hf, rfl⟩
      exact ⟨e.trans f, fun c hc => by change f (e c) = c; rw [he c hc, hf c hc],
        (predicate_rename_trans e f p).symm⟩ }

private theorem orbit_mem_iff [DecidableEq Clock] {F : TransitionForm Clock Var}
    {p q : Predicate Clock Var} (h : (rootClockOrbit F).r p q) (i : ℕ) :
    p ∈ branchwiseLabels F i ↔ q ∈ branchwiseLabels F i := by
  obtain ⟨e, hf, rfl⟩ := h
  exact (branchwiseLabels_rename_iff F e hf i p).symm

def orbitBranchwiseLabels [DecidableEq Clock] (F : TransitionForm Clock Var) (i : ℕ) :
    Set (Quotient (rootClockOrbit F)) :=
  Quotient.mk (rootClockOrbit F) '' branchwiseLabels F i

def orbitBranchwiseFresh [DecidableEq Clock] (F : TransitionForm Clock Var) :
    ℕ → Set (Quotient (rootClockOrbit F))
  | 0 => orbitBranchwiseLabels F 0
  | i + 1 => orbitBranchwiseLabels F (i + 1) \ orbitBranchwiseLabels F i

def orbitComplexity (F : TransitionForm Clock Var) (p : Quotient (rootClockOrbit F)) : ℕ :=
  Quotient.liftOn p Predicate.complexity (by
    intro p q h
    obtain ⟨e, _, rfl⟩ := h
    exact (Predicate.complexity_rename p e).symm)

noncomputable def orbitBranchwiseLevelRank [DecidableEq Clock]
    (F : TransitionForm Clock Var) (i : ℕ) : ℕ :=
  sSup (orbitComplexity F '' orbitBranchwiseFresh F i)

theorem orbitBranchwiseFresh_eq_image [DecidableEq Clock] (F : TransitionForm Clock Var) (i : ℕ) :
    orbitBranchwiseFresh F i = Quotient.mk (rootClockOrbit F) ''
      fresh AlphaBranchwisePExpansion branchwiseCurrent F i := by
  cases i with
  | zero => rfl
  | succ i =>
    ext z
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hprev⟩
      exact ⟨p, ⟨hp, fun hold => hprev ⟨p, hold, rfl⟩⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hold⟩, rfl⟩
      refine ⟨⟨p, hp, rfl⟩, ?_⟩
      rintro ⟨q, hq, he⟩
      exact hold ((orbit_mem_iff (Quotient.exact he) i).mp hq)

/-- In particular, the first zero of the rank in C.15 is unchanged by
passing to the relative clock-name quotient. -/
theorem orbitBranchwiseLevelRank_eq [DecidableEq Clock] (F : TransitionForm Clock Var) (i : ℕ) :
    orbitBranchwiseLevelRank F i = alphaBranchwiseLevelRank F i := by
  unfold orbitBranchwiseLevelRank alphaBranchwiseLevelRank rank
  rw [orbitBranchwiseFresh_eq_image, Set.image_image]
  rfl

end STLTableau.Section3.ConcreteContextual
