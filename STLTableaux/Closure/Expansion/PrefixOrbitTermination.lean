import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Logic.Function.Basic
import Mathlib.Order.KonigLemma
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push

/-! A finitely branching prefix-orbit argument. Index-dependent steps allow
the transition rule to change after a fixed number of initial steps. -/
namespace STLTableau.PrefixOrbitTermination

variable {State G : Type*}

def Valid (step : ℕ → State → State → Prop) (root : State)
    (n : ℕ) (xs : ℕ → State) : Prop :=
  xs 0 = root ∧ ∀ i < n, step i (xs i) (xs (i + 1))

/-- The same group element renames every state in the prefix. If both
prefixes start at the root, this element necessarily fixes the root. -/
def SamePrefixOrbit [SMul G State] (n : ℕ) (xs ys : ℕ → State) : Prop :=
  ∃ g : G, ∀ i ≤ n, g • xs i = ys i

private abbrev Prefix (step : ℕ → State → State → Prop) (root : State) (n : ℕ) :=
  {xs : ℕ → State // Valid step root n xs}

private def orbitSetoid [Group G] [MulAction G State]
    (step : ℕ → State → State → Prop) (root : State) (n : ℕ) :
    Setoid (Prefix step root n) where
  r xs ys := SamePrefixOrbit (G := G) n xs.val ys.val
  iseqv := {
    refl := fun _ => ⟨1, fun _ _ => one_smul G _⟩
    symm := by
      rintro xs ys ⟨g, hg⟩
      refine ⟨g⁻¹, fun i hi => ?_⟩
      rw [← hg i hi, ← mul_smul, inv_mul_cancel, one_smul]
    trans := by
      rintro xs ys zs ⟨g, hg⟩ ⟨h, hh⟩
      exact ⟨h * g, fun i hi => by rw [mul_smul, hg i hi, hh i hi]⟩ }

private abbrev PrefixOrbit [Group G] [MulAction G State]
    (step : ℕ → State → State → Prop) (root : State) (n : ℕ) :=
  Quotient (orbitSetoid (G := G) step root n)

private def truncate {step : ℕ → State → State → Prop} {root : State} {i j : ℕ}
    (hij : i ≤ j) (xs : Prefix step root j) : Prefix step root i :=
  ⟨xs.val, xs.property.1, fun k hk => xs.property.2 k (hk.trans_le hij)⟩

private def proj [Group G] [MulAction G State]
    {step : ℕ → State → State → Prop} {root : State} {i j : ℕ} (hij : i ≤ j) :
    PrefixOrbit (G := G) step root j → PrefixOrbit (G := G) step root i :=
  Quotient.map' (truncate hij) (by
    rintro _ _ ⟨g, hg⟩
    exact ⟨g, fun k hk => hg k (hk.trans hij)⟩)

private noncomputable def append {step : ℕ → State → State → Prop} {root : State} {n : ℕ}
    (a : Prefix step root n) (y : State) (hy : step n (a.val n) y) :
    Prefix step root (n + 1) := by
  let xs := Function.update a.val (n + 1) y
  refine ⟨xs, ?_, ?_⟩
  · exact (Function.update_of_ne (show 0 ≠ n + 1 by omega) y a.val).trans a.property.1
  · intro i hi
    by_cases he : i = n
    · subst i
      simpa only [xs, Function.update_self,
        Function.update_of_ne (show n ≠ n + 1 by omega)] using hy
    · have h₀ : i ≠ n + 1 := by omega
      have h₁ : i + 1 ≠ n + 1 := by omega
      simpa only [xs, Function.update_of_ne h₀, Function.update_of_ne h₁]
        using a.property.2 i (by omega)

/-! A sequence of representatives of compatible prefix orbits can be aligned
one prefix at a time. The aligned prefixes have the same diagonal as a
single infinite concrete path. -/
theorem lift_prefix_orbits [Group G] [MulAction G State]
    (step : ℕ → State → State → Prop) (root : State)
    (equivariant : ∀ (g : G) i {a b : State}, step i a b → step i (g • a) (g • b))
    (reps : ℕ → ℕ → State)
    (valid : ∀ n, Valid step root n (reps n))
    (coherent : ∀ n, SamePrefixOrbit (G := G) n (reps (n + 1)) (reps n)) :
    ∃ xs : ℕ → State, xs 0 = root ∧ ∀ i, step i (xs i) (xs (i + 1)) := by
  classical
  unfold SamePrefixOrbit at coherent
  choose align halign using coherent
  let g : ℕ → G := Nat.rec 1 fun n acc => acc * align n
  let xs : ℕ → State := fun i => g i • reps i i
  refine ⟨xs, ?_, ?_⟩
  · exact (one_smul G _).trans (valid 0).1
  · intro i
    have here := equivariant (g (i + 1)) i ((valid (i + 1)).2 i (Nat.lt_succ_self i))
    have join : g (i + 1) • reps (i + 1) i = xs i := by
      change (g i * align i) • reps (i + 1) i = g i • reps i i
      rw [mul_smul, halign i i le_rfl]
    rw [join] at here
    exact here

theorem common_length_bound [Group G] [MulAction G State]
    (step : ℕ → State → State → Prop) (root : State)
    (equivariant : ∀ (g : G) i {a b : State}, step i a b → step i (g • a) (g • b))
    (finite_cover : ∀ n (xs : ℕ → State), Valid step root n xs →
      ∃ reps : Finset State, ∀ y, step n (xs n) y →
        ∃ g : G, (∀ i ≤ n, g • xs i = xs i) ∧ g • y ∈ reps)
    (no_infinite : ¬ ∃ xs : ℕ → State, xs 0 = root ∧ ∀ i, step i (xs i) (xs (i + 1))) :
    ∃ D, ∀ n xs, Valid step root n xs → n ≤ D := by
  classical
  by_contra h
  push Not at h
  let P := PrefixOrbit (G := G) step root
  letI : Subsingleton (P 0) :=
    ⟨fun a b => Quotient.inductionOn₂ a b fun a b =>
      Quotient.sound ⟨1, fun i hi => by
        have he : i = 0 := Nat.eq_zero_of_le_zero hi
        subst i
        rw [one_smul, a.property.1, b.property.1]⟩⟩
  letI : ∀ i, Nonempty (P i) := fun i => by
    obtain ⟨n, xs, hv, hn⟩ := h i
    exact ⟨Quotient.mk _ (truncate hn.le ⟨xs, hv⟩)⟩
  have finite_fiber (i : ℕ) (q : P i) :
      {z : P (i + 1) | proj (Nat.le_add_right i 1) z = q}.Finite := by
    induction q using Quotient.inductionOn with
    | _ a =>
      obtain ⟨reps, cover⟩ := finite_cover i a.val a.property
      let S : Set State := {y | y ∈ reps ∧ step i (a.val i) y}
      have hS : S.Finite := reps.finite_toSet.subset (fun _ h => h.1)
      letI : Finite S := hS.to_subtype
      let extend (y : S) : P (i + 1) := Quotient.mk _ (append a y.val y.property.2)
      apply (Set.finite_range extend).subset
      intro z
      induction z using Quotient.inductionOn with
      | _ b =>
        intro hb
        have hab : Quotient.mk (orbitSetoid (G := G) step root i)
              (truncate (Nat.le_add_right i 1) b) =
            Quotient.mk (orbitSetoid (G := G) step root i) a := hb
        obtain ⟨v, hv⟩ := Quotient.exact hab
        change ∀ j ≤ i, v • b.val j = a.val j at hv
        have hs := equivariant v i (b.property.2 i (Nat.lt_succ_self i))
        rw [hv i le_rfl] at hs
        obtain ⟨g, hg, hm⟩ := cover _ hs
        have hstep := equivariant g i hs
        rw [hg i le_rfl] at hstep
        let y : S := ⟨g • (v • b.val (i + 1)), hm, hstep⟩
        refine ⟨y, Quotient.sound ⟨(g * v)⁻¹, fun j hj => ?_⟩⟩
        have he : (g * v) • b.val j = (append a y.val y.property.2).val j := by
          rw [mul_smul]
          change g • (v • b.val j) = Function.update a.val (i + 1) y.val j
          by_cases hji : j = i + 1
          · subst j
            rw [Function.update_self]
          · have hle : j ≤ i := by omega
            rw [Function.update_of_ne hji, hv j hle, hg j hle]
        change (g * v)⁻¹ • (append a y.val y.property.2).val j = b.val j
        rw [← he, ← mul_smul, inv_mul_cancel, one_smul]
  obtain ⟨f, coherent⟩ := exists_seq_forall_proj_of_forall_finite
    (α := P) (fun {_ _} h => proj h)
    (by intro i a; exact Quotient.inductionOn a fun _ => rfl)
    (by intro i j k hij hjk a; exact Quotient.inductionOn a fun _ => rfl) finite_fiber
  let reps (n : ℕ) : Prefix step root n := Quotient.out (f n)
  have repr (n : ℕ) : Quotient.mk (orbitSetoid (G := G) step root n) (reps n) = f n :=
    Quotient.out_eq _
  apply no_infinite (lift_prefix_orbits step root equivariant
    (fun n => (reps n).val) (fun n => (reps n).property) ?_)
  intro n
  apply @Quotient.exact _ (orbitSetoid (G := G) step root n)
    (truncate (Nat.le_add_right n 1) (reps (n + 1))) (reps n)
  change proj (Nat.le_add_right n 1) (Quotient.mk _ (reps (n + 1))) =
    Quotient.mk _ (reps n)
  rw [repr, repr]
  exact coherent _

end STLTableau.PrefixOrbitTermination
