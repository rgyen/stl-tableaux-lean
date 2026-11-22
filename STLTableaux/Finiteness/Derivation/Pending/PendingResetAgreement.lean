import STLTableaux.Finiteness.Derivation.Pending.PendingFixedGuardSupport

/-! Ordinary child common resets preserve every residual active assignment.
Residual source clocks are not required to avoid the retained protection set. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

theorem remaining_active_subset_budget
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (p : Predicate Clock Var)
    (left right : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate p :: right) :
    activeSupport (left ++ right) ⊆ W := by
  rintro c ⟨q,hq,hc⟩
  have hm : Local.predicate q ∈ owned.locals := by
    rw [hsplit]
    rcases List.mem_append.mp hq with hl | hr
    · exact List.mem_append_left _ hl
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  exact owned.covers_input (Or.inl (Or.inr (canonical_local_support owned.shape hm hc)))

/-- Fresh canonical branch resets cannot shadow any inherited binding owned
by a residual current source. This needs no protectedActive assertion. -/
theorem ordinary_child_common_reset_agrees
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (p : Predicate Clock Var)
    (left right : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate p :: right)
    (Rb : ClockResetSet Clock) (hRb : Disjoint Rb.clocks W) :
    ∀ c ∈ activeSupport (left ++ right),
      (Rb.union (copyActiveResets R (left ++ right))).value c = R.value c := by
  classical
  intro c hc
  have hcW := remaining_active_subset_budget owned p left right hsplit hc
  have hr : Rb.value c = none := by
    cases h : Rb.value c with
    | none => rfl
    | some a => exact False.elim (Set.disjoint_left.1 hRb ⟨a,h⟩ hcW)
  change (match Rb.value c with
    | some a => some a
    | none => if c ∈ activeSupport (left ++ right) then R.value c else none) = R.value c
  rw [hr,if_pos hc]

/-- Reattaching the original inherited map preserves every old assignment,
including names no longer active. Actual fresh branch resets avoid all of W;
the copied residual map is absorbed by the inherited map exactly. -/
theorem ordinary_child_inherited_reset_agrees
    (R Rb : ClockResetSet Clock) (remaining : List (Local Clock Var))
    (W : Set Clock) (hRb : Disjoint Rb.clocks W) :
    ∀ c ∈ W, ((Rb.union (copyActiveResets R remaining)).union R).value c = R.value c := by
  intro c hcW
  have hr : Rb.value c = none := by
    cases h : Rb.value c with
    | none => rfl
    | some a => exact False.elim (Set.disjoint_left.1 hRb ⟨a,h⟩ hcW)
  have hcopy := congrArg (fun S : ClockResetSet Clock => S.value c)
    (copyActiveResets_absorb R remaining)
  change (match (match Rb.value c with
    | some a => some a | none => (copyActiveResets R remaining).value c) with
    | some a => some a | none => R.value c) = R.value c
  rw [hr]
  exact hcopy

end STLTableau.Section4.Finiteness
