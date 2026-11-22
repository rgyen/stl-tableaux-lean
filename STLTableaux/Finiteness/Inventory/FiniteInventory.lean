import STLTableaux.Closure.Subsumption.FaithfulClosureOrder
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card

/-! Sparse formula-specific inventories for actual Section 3 transition forms.
This file counts forms satisfying the inventory. It does not assert that a
satisfied accepting path has a representative satisfying that inventory. -/
namespace STLTableau.Section4.Finiteness.FiniteInventory
open Section3
variable {Clock Var Slot : Type*}

/-- The temporal formula is fixed by the slot, as are its three clock names. -/
structure Triple (Clock Var : Type*) where
  left : Clock
  right₀ : Clock
  right₁ : Clock
  kind : TemporalKind
  interval : TimeInterval
  body : Formula Var

/-- Zero and finite interval endpoints; an infinite upper endpoint contributes
another copy of the lower endpoint, never an infinite numeric reset value. -/
def endpoint (I : TimeInterval) (i : Fin 3) : NNReal :=
  if i = 0 then 0 else match I with
  | .bounded J => if i = 1 then ⟨J.lower,J.lower_nonnegative⟩
      else ⟨J.upper,le_trans J.lower_nonnegative (le_of_lt J.nonSingular)⟩
  | .unbounded a => a

def mark (b : Bool) : Marker := if b then .open else .closed

def clockAt (t : Triple Clock Var) (i : Fin 3) : Clock :=
  if i = 0 then t.left else if i = 1 then t.right₀ else t.right₁

abbrev LocalTag := Bool ⊕ (Bool × Bool × Bool)

def slotLocal (t : Triple Clock Var) : LocalTag → Local Clock Var
  | .inl b => .predicate (.upper t.left (mark b) t.kind t.interval t.body)
  | .inr (r,b,q) => .predicate (.bounded t.left
      (if r then t.right₁ else t.right₀) (mark b) (mark q) t.kind t.interval t.body)

def relationAt (i : Fin 5) : ClockRelation :=
  if i = 0 then .ge else if i = 1 then .gt else if i = 2 then .eq
    else if i = 3 then .lt else .le

variable [Fintype Slot]

noncomputable def clocks (t : Slot → Triple Clock Var) : Finset Clock := by
  classical
  exact Finset.univ.image (fun x : Slot × Fin 3 => clockAt (t x.1) x.2)

theorem clocks_card_le (t : Slot → Triple Clock Var) :
    (clocks t).card ≤ 3 * Fintype.card Slot := by
  classical
  unfold clocks
  exact (Finset.card_image_le).trans_eq (by simp; omega)

noncomputable def locals (P : Finset (Formula Var)) (t : Slot → Triple Clock Var) :
    Finset (Local Clock Var) := by
  classical
  exact (Finset.univ.image (fun b : Option Bool => match b with
      | none => Local.terminal | some b => Local.marker (mark b))) ∪
    P.image (fun φ => Local.predicate (.plain φ)) ∪
    Finset.univ.image (fun x : Slot × LocalTag => slotLocal (t x.1) x.2)

/-- An atom in the local inventory comes from its inventory of formulas in unclocked predicates. -/
theorem atom_mem_plain_inventory (P : Finset (Formula Var)) (t : Slot → Triple Clock Var)
    (a : AtomicProposition Var)
    (ha : Local.predicate (.plain (.atom a)) ∈ locals P t) :
    Formula.atom a ∈ P := by
  classical
  rcases Finset.mem_union.mp ha with ha | ha
  · rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨b, _, hb⟩ := Finset.mem_image.mp ha
      cases b with
      | none => cases hb
      | some b => cases hb
    · obtain ⟨φ, hφ, he⟩ := Finset.mem_image.mp ha
      cases he
      exact hφ
  · obtain ⟨⟨s, tag⟩, _, he⟩ := Finset.mem_image.mp ha
    rcases tag with b | ⟨r, b, q⟩ <;> cases he

noncomputable def guards (t : Slot → Triple Clock Var) : Finset (Guard Clock) := by
  classical
  exact Finset.univ.image (fun x : Slot × Fin 3 × Fin 5 × Fin 3 =>
    ⟨clockAt (t x.1) x.2.1,relationAt x.2.2.1,endpoint (t x.1).interval x.2.2.2⟩)

noncomputable def resets (t : Slot → Triple Clock Var) : Finset (Clock × NNReal) := by
  classical
  exact Finset.univ.image (fun x : Slot × Fin 3 × Fin 3 =>
    (clockAt (t x.1) x.2.1,endpoint (t x.1).interval x.2.2))

theorem locals_card_le (P : Finset (Formula Var)) (t : Slot → Triple Clock Var) :
    (locals P t).card ≤ P.card + 3 + 10 * Fintype.card Slot := by
  classical
  unfold locals
  have h := Finset.card_union_le
    ((Finset.univ.image (fun b : Option Bool => match b with
      | none => Local.terminal | some b => Local.marker (mark b))) ∪
      P.image (fun φ => Local.predicate (.plain φ)))
    (Finset.univ.image (fun x : Slot × LocalTag => slotLocal (t x.1) x.2))
  have h₁ := Finset.card_union_le
    (Finset.univ.image (fun b : Option Bool => match b with
      | none => (Local.terminal : Local Clock Var) | some b => Local.marker (mark b)))
    (P.image (fun φ => (Local.predicate (.plain φ) : Local Clock Var)))
  have h₂ := Finset.card_image_le (s := (Finset.univ : Finset (Option Bool)))
    (f := fun b => match b with
      | none => (Local.terminal : Local Clock Var) | some b => Local.marker (mark b))
  have h₃ := Finset.card_image_le (s := P)
    (f := fun φ => (Local.predicate (.plain φ) : Local Clock Var))
  have h₄ : (Finset.univ.image (fun x : Slot × LocalTag => slotLocal (t x.1) x.2)).card ≤
      Fintype.card Slot * 10 := by
    calc
      _ ≤ (Finset.univ : Finset (Slot × LocalTag)).card := Finset.card_image_le
      _ = _ := by simp [LocalTag]
  simp only [Finset.card_univ,Fintype.card_option,Fintype.card_bool] at h₂
  omega

theorem guards_card_le (t : Slot → Triple Clock Var) :
    (guards t).card ≤ 45 * Fintype.card Slot := by
  classical
  unfold guards
  exact (Finset.card_image_le).trans_eq (by simp; omega)

theorem resets_card_le (t : Slot → Triple Clock Var) :
    (resets t).card ≤ 9 * Fintype.card Slot := by
  classical
  unfold resets
  exact (Finset.card_image_le).trans_eq (by simp; omega)

/-- Reset functionality is inherited from actual StateForm syntax. Encoding its
finite graph avoids allowing every clock to choose every formula's endpoints. -/
def Within (L : Finset (Local Clock Var)) (G : Finset (Guard Clock))
    (R : Finset (Clock × NNReal)) (S : Section3.StateForm Clock Var) : Prop :=
  S.locals ⊆ (L : Set _) ∧ S.guards ⊆ (G : Set _) ∧
    ∀ c a, S.resets.value c = some a → (c,a) ∈ R

abbrev Code (L : Finset (Local Clock Var)) (G : Finset (Guard Clock))
    (R : Finset (Clock × NNReal)) := Set ↥L × Set ↥G × Set ↥R

noncomputable def encode (L : Finset (Local Clock Var)) (G : Finset (Guard Clock))
    (R : Finset (Clock × NNReal)) (S : {S // Within L G R S}) : Code L G R :=
  ({l | l.val ∈ S.val.locals},{g | g.val ∈ S.val.guards},
    {r | S.val.resets.value r.val.1 = some r.val.2})

theorem encode_injective (L : Finset (Local Clock Var)) (G : Finset (Guard Clock))
    (R : Finset (Clock × NNReal)) : Function.Injective (encode L G R) := by
  intro S T he
  have hl : S.val.locals = T.val.locals := by
    ext l
    constructor
    · intro hm
      exact Eq.mp (congrArg (fun x : Code L G R => (⟨l,S.property.1 hm⟩ : ↥L) ∈ x.1) he) hm
    · intro hm
      exact Eq.mpr (congrArg (fun x : Code L G R => (⟨l,T.property.1 hm⟩ : ↥L) ∈ x.1) he) hm
  have hg : S.val.guards = T.val.guards := by
    ext g
    constructor
    · intro hm
      exact Eq.mp (congrArg (fun x : Code L G R => (⟨g,S.property.2.1 hm⟩ : ↥G) ∈ x.2.1) he) hm
    · intro hm
      exact Eq.mpr (congrArg (fun x : Code L G R => (⟨g,T.property.2.1 hm⟩ : ↥G) ∈ x.2.1) he) hm
  have hr : S.val.resets = T.val.resets := by
    have hv : S.val.resets.value = T.val.resets.value := by
      funext c
      have hh : ∀ a, S.val.resets.value c = some a ↔ T.val.resets.value c = some a := by
        intro a
        constructor
        · intro ha
          exact Eq.mp (congrArg (fun x : Code L G R =>
            (⟨(c,a),S.property.2.2 c a ha⟩ : ↥R) ∈ x.2.2) he) ha
        · intro ha
          exact Eq.mpr (congrArg (fun x : Code L G R =>
            (⟨(c,a),T.property.2.2 c a ha⟩ : ↥R) ∈ x.2.2) he) ha
      cases hs : S.val.resets.value c with
      | none =>
        cases ht : T.val.resets.value c with
        | none => rfl
        | some b =>
          have hb := (hh b).mpr ht
          rw [hs] at hb
          contradiction
      | some a => exact ((hh a).mp hs).symm
    cases hS : S.val.resets with
    | mk sv sf =>
      cases hT : T.val.resets with
      | mk tv tf =>
        simp only [hS,hT] at hv ⊢
        cases hv
        rfl
  exact Subtype.ext (Section3.StateForm.ext_components hg hr hl)

def TransitionWithin (L : Finset (Local Clock Var)) (G : Finset (Guard Clock))
    (R : Finset (Clock × NNReal)) (S : Section3.TransitionForm Clock Var) : Prop :=
  Within L G R S.current ∧ ∀ N, S.nextPart = some N → Within L G R N

abbrev TransitionCode (L : Finset (Local Clock Var)) (G : Finset (Guard Clock))
    (R : Finset (Clock × NNReal)) := Code L G R × Option (Code L G R)

noncomputable def encodeTransition (L : Finset (Local Clock Var))
    (G : Finset (Guard Clock)) (R : Finset (Clock × NNReal))
    (S : {S // TransitionWithin L G R S}) : TransitionCode L G R :=
  (encode L G R ⟨S.val.current,S.property.1⟩,
    match h : S.val.nextPart with
    | none => none
    | some N => some (encode L G R ⟨N,S.property.2 N h⟩))

theorem encodeTransition_injective (L : Finset (Local Clock Var))
    (G : Finset (Guard Clock)) (R : Finset (Clock × NNReal)) :
    Function.Injective (encodeTransition L G R) := by
  intro S T he
  have hc := encode_injective L G R (congrArg Prod.fst he)
  have hn : S.val.nextPart = T.val.nextPart := by
    have hh := congrArg Prod.snd he
    unfold encodeTransition at hh
    split at hh <;> split at hh
    · simp_all
    · contradiction
    · contradiction
    · have hh' := encode_injective L G R (Option.some.inj hh)
      have hv := congrArg Subtype.val hh'
      simp_all
  exact Subtype.ext (congrArg₂ Section3.TransitionForm.mk (congrArg Subtype.val hc) hn)

theorem transition_finite (L : Finset (Local Clock Var))
    (G : Finset (Guard Clock)) (R : Finset (Clock × NNReal)) :
    {S : Section3.TransitionForm Clock Var | TransitionWithin L G R S}.Finite := by
  classical
  haveI : Finite {S // TransitionWithin L G R S} :=
    Finite.of_injective _ (encodeTransition_injective L G R)
  apply Set.finite_coe_iff.mp
  change Finite {S // TransitionWithin L G R S}
  infer_instance

theorem code_card (L : Finset (Local Clock Var)) (G : Finset (Guard Clock))
    (R : Finset (Clock × NNReal)) : Nat.card (Code L G R) = 2 ^ (L.card + G.card + R.card) := by
  classical
  simp [Code,Nat.card_eq_fintype_card,Fintype.card_set,pow_add,Nat.mul_assoc]

theorem transition_card_le (L : Finset (Local Clock Var))
    (G : Finset (Guard Clock)) (R : Finset (Clock × NNReal)) :
    Nat.card {S // TransitionWithin L G R S} ≤
      2 ^ (2 * (L.card + G.card + R.card) + 1) := by
  classical
  have h := Nat.card_le_card_of_injective _ (encodeTransition_injective L G R)
  have hc : Nat.card (TransitionCode L G R) =
      2 ^ (L.card + G.card + R.card) * (2 ^ (L.card + G.card + R.card) + 1) := by
    change Nat.card (Code L G R × Option (Code L G R)) = _
    rw [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_option,
      ← Nat.card_eq_fintype_card,code_card]
  rw [hc] at h
  apply h.trans
  let a := L.card + G.card + R.card
  have hp : 1 ≤ 2 ^ a := Nat.one_le_pow _ _ (by omega)
  change 2 ^ a * (2 ^ a + 1) ≤ 2 ^ (2 * a + 1)
  have he : 2 ^ (2 * a + 1) = 2 ^ a * 2 ^ a * 2 := by
    rw [show 2 * a + 1 = a + a + 1 by omega,pow_add,pow_add]
    rfl
  rw [he]
  nlinarith

/-- Concrete exponential bound for the formula-specific sparse inventory of
actual mixed transition-form judgements, with consistent reset maps built in. -/
theorem sparse_transition_card_le (P : Finset (Formula Var))
    (t : Slot → Triple Clock Var) :
    Nat.card {S // TransitionWithin (locals P t) (guards t) (resets t) S} ≤
      2 ^ (2 * (P.card + 3 + 64 * Fintype.card Slot) + 1) := by
  apply (transition_card_le _ _ _).trans
  apply Nat.pow_le_pow_right (by omega)
  have hl := locals_card_le P t
  have hg := guards_card_le t
  have hr := resets_card_le t
  omega

theorem sparse_transition_finite (P : Finset (Formula Var))
    (t : Slot → Triple Clock Var) :
    {S : Section3.TransitionForm Clock Var |
      TransitionWithin (locals P t) (guards t) (resets t) S}.Finite :=
  transition_finite _ _ _

end STLTableau.Section4.Finiteness.FiniteInventory
