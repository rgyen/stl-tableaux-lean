import STLTableaux.Finiteness.Derivation.Pending.PendingOwnership

/-! Folds pending judgements into an optional conjunction, with `none` for
the empty list. Permuting the judgements preserves their occurrence weights
and changes the conjunction only by associativity and commutativity. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

private inductive OptionalStructural : Option (MixedJ Clock Var) → Option (MixedJ Clock Var) → Prop
  | none : OptionalStructural none none
  | some {J K} : StructuralEq J K → OptionalStructural (some J) (some K)

private theorem optional_refl (J : Option (MixedJ Clock Var)) : OptionalStructural J J := by
  cases J with
  | none => exact .none
  | some J => exact .some (.refl J)

private theorem optional_trans {J K L : Option (MixedJ Clock Var)}
    (h : OptionalStructural J K) (g : OptionalStructural K L) : OptionalStructural J L := by
  cases h with
  | none => cases g; exact .none
  | some h => cases g with | some g => exact .some (.trans h g)

private theorem optional_cons (A : MixedJ Clock Var) {J K : Option (MixedJ Clock Var)}
    (h : OptionalStructural J K) :
    OptionalStructural (some (prependCurrent A J)) (some (prependCurrent A K)) := by
  cases h with
  | none => exact .some (.refl A)
  | some h => exact .some (.conj (.refl A) h)

private theorem optional_assoc (A B C : Option (MixedJ Clock Var)) :
    OptionalStructural (optionalConj (optionalConj A B) C) (optionalConj A (optionalConj B C)) := by
  cases A <;> cases B <;> cases C <;>
    first | exact .none | exact .some (.refl _) | exact .some (.assoc _ _ _)

private theorem optional_left (A : Option (MixedJ Clock Var))
    {B C : Option (MixedJ Clock Var)} (h : OptionalStructural B C) :
    OptionalStructural (optionalConj A B) (optionalConj A C) := by
  cases h with
  | none => exact optional_refl _
  | some h =>
    cases A with
    | none => exact .some h
    | some A => exact .some (.conj (.refl A) h)

private theorem fold_perm {X Y : List (MixedJ Clock Var)} (h : X.Perm Y) :
    OptionalStructural (foldCurrent X) (foldCurrent Y) := by
  induction h with
  | nil => exact .none
  | cons A h ih =>
    rw [foldCurrent_cons,foldCurrent_cons]
    exact optional_cons A ih
  | swap A B X =>
    cases hx : foldCurrent X with
    | none =>
      simpa only [foldCurrent_cons,hx,prependCurrent] using
        (OptionalStructural.some (ACIdem.comm B A))
    | some J =>
      have hs : StructuralEq (.conj B (.conj A J)) (.conj A (.conj B J)) :=
        .trans (.symm (.assoc B A J)) (.trans (.conj (.comm B A) (.refl J)) (.assoc A B J))
      simpa only [foldCurrent_cons,hx,prependCurrent] using OptionalStructural.some hs
  | trans h g ih ig => exact optional_trans ih ig

private theorem fold_append (X Y : List (MixedJ Clock Var)) :
    OptionalStructural (optionalConj (foldCurrent X) (foldCurrent Y)) (foldCurrent (X ++ Y)) := by
  induction X with
  | nil => exact optional_refl _
  | cons A X ih =>
    change OptionalStructural
      (optionalConj (optionalConj (some A) (foldCurrent X)) (foldCurrent Y))
      (optionalConj (some A) (foldCurrent (X ++ Y)))
    exact optional_trans (optional_assoc _ _ _) (optional_left _ ih)

private theorem fold_cons_weight (A : MixedJ Clock Var) (X : List (MixedJ Clock Var)) :
    optionalWeight (foldCurrent (A :: X)) = pendingWeight A + optionalWeight (foldCurrent X) := by
  cases hx : foldCurrent X <;> simp [foldCurrent,hx,optionalConj,optionalWeight,pendingWeight]

private theorem fold_perm_weight {X Y : List (MixedJ Clock Var)} (h : X.Perm Y) :
    optionalWeight (foldCurrent X) = optionalWeight (foldCurrent Y) := by
  induction h with
  | nil => rfl
  | cons A h ih => simp only [fold_cons_weight,ih]
  | swap A B X => simp only [fold_cons_weight]; omega
  | trans h g ih ig => exact ih.trans ig

private theorem fold_append_weight (X Y : List (MixedJ Clock Var)) :
    optionalWeight (foldCurrent (X ++ Y)) =
      optionalWeight (foldCurrent X) + optionalWeight (foldCurrent Y) := by
  induction X with
  | nil => simp [foldCurrent,optionalWeight]
  | cons A X ih => simp only [List.cons_append,fold_cons_weight]; omega

 theorem foldCurrent_perm {X Y : List (MixedJ Clock Var)} (h : X.Perm Y)
    {J K : MixedJ Clock Var} (hX : foldCurrent X = some J) (hY : foldCurrent Y = some K) :
    StructuralEq J K := by
  have hp := fold_perm h
  rw [hX,hY] at hp
  cases hp with | some hp => exact hp

 theorem foldCurrent_perm_weight {X Y : List (MixedJ Clock Var)} (h : X.Perm Y)
    {J K : MixedJ Clock Var} (hX : foldCurrent X = some J) (hY : foldCurrent Y = some K) :
    pendingWeight J = pendingWeight K := by
  simpa only [hX,hY,optionalWeight] using fold_perm_weight h

 theorem foldCurrent_append {X Y : List (MixedJ Clock Var)} {J K L : MixedJ Clock Var}
    (hX : foldCurrent X = some J) (hY : foldCurrent Y = some K)
    (hXY : foldCurrent (X ++ Y) = some L) : StructuralEq (.conj J K) L := by
  have hp := fold_append X Y
  rw [hX,hY,hXY] at hp
  cases hp with | some hp => exact hp

 theorem foldCurrent_append_weight {X Y : List (MixedJ Clock Var)} {J K L : MixedJ Clock Var}
    (hX : foldCurrent X = some J) (hY : foldCurrent Y = some K)
    (hXY : foldCurrent (X ++ Y) = some L) :
    pendingWeight L = pendingWeight J + pendingWeight K := by
  simpa only [hX,hY,hXY,optionalWeight] using fold_append_weight X Y

end STLTableau.Section4.Finiteness
