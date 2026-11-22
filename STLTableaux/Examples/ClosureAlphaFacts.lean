import STLTableaux.Closure.Normalization.FaithfulAlphaNormalization

namespace STLTableau.Section3
variable {Clock Var : Type*}

private theorem reset_rename_empty (Λ : ClockResetSet Clock) (e : Equiv.Perm Clock) :
    (Λ.rename e).clocks = ∅ ↔ Λ.clocks = ∅ := by
  rw [ClockResetSet.clocks_rename]
  exact Set.image_eq_empty

namespace TransitionForm.AlphaEquivalent

/-- Alpha-equivalence preserves any property of the current state form
that is invariant under renaming its reset clocks. -/
theorem current_state_observation {F G : TransitionForm Clock Var}
    (h : F.AlphaEquivalent G) (q : StateForm Clock Var → Prop)
    (hq : ∀ S e, q (S.alphaReset e) ↔ q S) : q F.current ↔ q G.current := by
  induction h with
  | refl => rfl
  | outer F e hf => exact hq F.current e
  | next => rfl
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig

theorem current_reset_empty {F G : TransitionForm Clock Var} (h : F.AlphaEquivalent G) :
    F.current.resets.clocks = ∅ ↔ G.current.resets.clocks = ∅ := by
  induction h with
  | refl => rfl
  | outer F e hf => exact reset_rename_empty _ _
  | next => rfl
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig

theorem next_none {F G : TransitionForm Clock Var} (h : F.AlphaEquivalent G) :
    F.nextPart = none ↔ G.nextPart = none := by
  induction h with
  | refl => rfl
  | outer F e hf => simp [TransitionForm.alphaOuter]
  | next F e hf => simp [TransitionForm.alphaNext]
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig

private theorem locals_observation (S : StateForm Clock Var) (e : Equiv.Perm Clock)
    (q : Local Clock Var → Prop) (hq : ∀ l, q (l.rename e) ↔ q l) :
    (∃ l ∈ (S.rename e).locals, q l) ↔ ∃ l ∈ S.locals, q l := by
  simp only [StateForm.rename, Set.mem_image]
  aesop

theorem current_local_observation {F G : TransitionForm Clock Var}
    (h : F.AlphaEquivalent G) (q : Local Clock Var → Prop)
    (hq : ∀ e l, q (l.rename e) ↔ q l) :
    (∃ l ∈ F.current.locals, q l) ↔ ∃ l ∈ G.current.locals, q l := by
  induction h with
  | refl => rfl
  | outer F e hf => exact locals_observation _ _ q (hq e)
  | next => rfl
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig

theorem next_local_observation {F G : TransitionForm Clock Var}
    (h : F.AlphaEquivalent G) (q : Local Clock Var → Prop)
    (hq : ∀ e l, q (l.rename e) ↔ q l) :
    (∃ N, F.nextPart = some N ∧ ∃ l ∈ N.locals, q l) ↔
      ∃ N, G.nextPart = some N ∧ ∃ l ∈ N.locals, q l := by
  induction h with
  | refl => rfl
  | outer F e hf =>
      cases hn : F.nextPart with
      | none => simp [TransitionForm.alphaOuter, hn]
      | some N => simpa [TransitionForm.alphaOuter, hn] using locals_observation N e q (hq e)
  | next F e hf =>
      cases hn : F.nextPart with
      | none => simp [TransitionForm.alphaNext, hn]
      | some N => simpa [TransitionForm.alphaNext, hn, StateForm.alphaReset] using
          locals_observation N e q (hq e)
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig

theorem current_plain {F G : TransitionForm Clock Var} (h : F.AlphaEquivalent G)
    (φ : Formula Var) :
    Local.predicate (.plain φ) ∈ F.current.locals ↔
      Local.predicate (.plain φ) ∈ G.current.locals := by
  have hh := current_local_observation h
    (fun l => l = .predicate (.plain φ)) (by
      intro e l; cases l with
      | terminal => simp [Local.rename]
      | marker m => simp [Local.rename]
      | predicate p => cases p <;> simp [Local.rename, Predicate.rename])
  simpa using hh

theorem next_terminal {F G : TransitionForm Clock Var} (h : F.AlphaEquivalent G) :
    (∃ N, F.nextPart = some N ∧ Local.terminal ∈ N.locals) ↔
      ∃ N, G.nextPart = some N ∧ Local.terminal ∈ N.locals := by
  simpa using next_local_observation h (fun l => l = .terminal) (by
    intro e l; cases l <;> simp [Local.rename])

theorem next_predicate {F G : TransitionForm Clock Var} (h : F.AlphaEquivalent G) :
    (∃ N, F.nextPart = some N ∧ ∃ p, Local.predicate p ∈ N.locals) ↔
      ∃ N, G.nextPart = some N ∧ ∃ p, Local.predicate p ∈ N.locals := by
  have hh := next_local_observation h
    (fun l => ∃ p, l = .predicate p) (by
      intro e l; cases l <;> simp [Local.rename])
  constructor
  · rintro ⟨N,hN,p,hp⟩
    obtain ⟨M,hM,l,hl,q,rfl⟩ := hh.mp ⟨N,hN,.predicate p,hp,p,rfl⟩
    exact ⟨M,hM,q,hl⟩
  · rintro ⟨N,hN,p,hp⟩
    obtain ⟨M,hM,l,hl,q,rfl⟩ := hh.mpr ⟨N,hN,.predicate p,hp,p,rfl⟩
    exact ⟨M,hM,q,hl⟩

theorem next_guards_of_current_reset_empty {F G : TransitionForm Clock Var}
    (h : F.AlphaEquivalent G) (hempty : F.current.resets.clocks = ∅)
    (g : Guard Clock) :
    (∃ N, F.nextPart = some N ∧ g ∈ N.guards) ↔
      ∃ N, G.nextPart = some N ∧ g ∈ N.guards := by
  induction h with
  | refl => rfl
  | outer F e hf =>
      have he : F.current.resets.clocks = ∅ := (reset_rename_empty _ _).mp hempty
      cases hn : F.nextPart with
      | none => simp [TransitionForm.alphaOuter, hn]
      | some N =>
          have hfix : ∀ x ∈ N.guards, x.rename e = x := by
            intro x hx
            have hc : e x.clock = x.clock := hf x.clock ⟨Or.inr (by
              simp only [hn]
              exact Or.inl ⟨x,hx,rfl⟩), by simp [he]⟩
            cases x
            simp_all [Guard.rename]
          have hguards : Guard.rename e '' N.guards = N.guards := by
            ext x; constructor
            · rintro ⟨y,hy,rfl⟩; simpa [hfix y hy] using hy
            · intro hx; exact ⟨x,hx,hfix x hx⟩
          simp [TransitionForm.alphaOuter, hn, StateForm.rename, hguards]
  | next F e hf =>
      cases hn : F.nextPart <;> simp [TransitionForm.alphaNext, hn, StateForm.alphaReset]
  | symm h ih =>
      exact (ih ((current_reset_empty h).mpr hempty)).symm
  | trans h g ih ig =>
      exact (ih hempty).trans (ig ((current_reset_empty h).mp hempty))

end TransitionForm.AlphaEquivalent
end STLTableau.Section3

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[
      ``STLTableau.Section3.TransitionForm.AlphaEquivalent.current_state_observation,
      ``STLTableau.Section3.TransitionForm.AlphaEquivalent.current_reset_empty,
      ``STLTableau.Section3.TransitionForm.AlphaEquivalent.next_none,
      ``STLTableau.Section3.TransitionForm.AlphaEquivalent.current_local_observation,
      ``STLTableau.Section3.TransitionForm.AlphaEquivalent.next_local_observation,
      ``STLTableau.Section3.TransitionForm.AlphaEquivalent.current_plain,
      ``STLTableau.Section3.TransitionForm.AlphaEquivalent.next_terminal,
      ``STLTableau.Section3.TransitionForm.AlphaEquivalent.next_predicate,
      ``STLTableau.Section3.TransitionForm.AlphaEquivalent.next_guards_of_current_reset_empty
      ] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
