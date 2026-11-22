import STLTableaux.Finiteness.ClockAllocation.SelectedAlphaStep
import STLTableaux.Finiteness.Correctness.UniformRootPath

/-! Constructs a path over a fixed clock set by extending the clock assignment
at each step. Each input inherits the renaming of the preceding next state. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

def FreeDerives (N : Section3.StateForm Clock Var) (F : Section3.TransitionForm Clock Var) : Prop :=
  Derives N F ∧ F.freeClocks ⊆ N.freeClocks

/-- Records a resolution and safe normalizations of its input, full output, and erased output. -/
structure ResolvedCertificate (N : Section3.StateForm Clock Var) (F : Section3.TransitionForm Clock Var) where
  input : MixedJ Clock Var
  full : MixedJ Clock Var
  erased : MixedJ Clock Var
  resolves : Resolve input full erased
  input_safe : SafeNormalization input (.ofState N)
  full_safe : SafeNormalization full F
  erased_safe : SafeNormalization erased F.atomicProjection

theorem ResolvedCertificate.freeDerives {N : Section3.StateForm Clock Var}
    {F : Section3.TransitionForm Clock Var} (C : ResolvedCertificate N F) : FreeDerives N F :=
  ⟨.resolved C.resolves C.input_safe C.full_safe C.erased_safe,
    selected_resolution_free_subset C.resolves C.input_safe C.full_safe⟩

theorem ResolvedCertificate.rename_freeDerives {N : Section3.StateForm Clock Var}
    {F : Section3.TransitionForm Clock Var} (C : ResolvedCertificate N F) (e : Equiv.Perm Clock) :
    FreeDerives (N.rename e) (renameTransition e F) := by
  exact (ResolvedCertificate.mk (renameJudgement e C.input) (renameJudgement e C.full)
    (renameJudgement e C.erased) (C.resolves.rename e)
    (by simpa only [rename_ofState] using C.input_safe.rename e)
    (C.full_safe.rename e)
    (by simpa only [rename_atomicProjection] using C.erased_safe.rename e)).freeDerives

omit [DecidableEq Clock] in
/-- Extend only the current finite interface, preserving its actual incoming
permutation; no injection on historical names is requested. -/
theorem extend_supported_permutation (E U Q : Finset Clock) (hEU : E ⊆ U)
    (hcard : U.card ≤ Q.card) (e0 : Equiv.Perm Clock)
    (h0 : ∀ c∈E,e0 c∈Q) :
    ∃ e : Equiv.Perm Clock, (∀ c∈U,e c∈Q) ∧ ∀ c∈E,e c=e0 c := by
  classical
  let q : Q ≃ Fin Q.card := by simpa using (Fintype.equivFin Q)
  let f : E → Fin Q.card := fun c=>q ⟨e0 c.val,h0 c.val c.property⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply e0.injective
    exact congrArg Subtype.val (q.injective h)
  obtain ⟨g,hg,he⟩ := extend_clock_names hEU hcard f hf
  obtain ⟨e,hh⟩ := supported_clock_permutation U Q (fun u=>q.symm (g u)) (q.symm.injective.comp hg)
  refine ⟨e,?_,?_⟩
  · intro c hc
    rw [hh ⟨c,hc⟩]
    exact (q.symm (g ⟨c,hc⟩)).property
  · intro c hc
    rw [hh ⟨c,hEU hc⟩,he ⟨c,hc⟩]
    exact congrArg Subtype.val (q.symm_apply_apply ⟨e0 c,h0 c hc⟩)

omit [DecidableEq Clock] in
theorem ofState_support (N : Section3.StateForm Clock Var) :
    (Section3.TransitionForm.ofState N).allClocks=stateClockSupport N := by
  rw [transition_support_eq]
  exact Set.union_empty _

omit [DecidableEq Clock] in
theorem next_whole_support {F : Section3.TransitionForm Clock Var}
    {M : Section3.StateForm Clock Var} (hn : F.nextPart=some M) :
    (Section3.TransitionForm.ofState M).allClocks ⊆ F.allClocks := by
  rw [ofState_support,transition_support_eq,hn]
  exact Set.subset_union_right

omit [DecidableEq Clock] in
theorem renamed_whole_support (e : Equiv.Perm Clock) (F : Section3.TransitionForm Clock Var) :
    (renameTransition e F).allClocks=e '' F.allClocks := by
  have hs (N : Section3.StateForm Clock Var) : stateClockSupport (N.rename e)=e '' stateClockSupport N := by
    unfold stateClockSupport
    rw [guardClocks_rename,Section3.StateForm.localClocks_rename]
    change e '' N.guardClocks ∪ e '' N.localClocks ∪ (N.resets.rename e).clocks = _
    rw [ClockResetSet.clocks_rename,Set.image_union,Set.image_union]
  rw [transition_support_eq,transition_support_eq]
  cases hn : F.nextPart <;> simp [renameTransition,hn,hs,Set.image_union]

omit [DecidableEq Clock] in
theorem local_rename_injective (e : Equiv.Perm Clock) :
    Function.Injective (fun l : Local Clock Var=>l.rename e) := by
  have inv (l : Local Clock Var) : (l.rename e).rename e.symm=l := by
    cases l with
    | terminal => rfl
    | marker => rfl
    | predicate p => cases p <;> simp [Local.rename,Predicate.rename]
  intro a b h
  exact (inv a).symm.trans ((congrArg (fun l=>l.rename e.symm) h).trans (inv b))

omit [DecidableEq Clock] in
theorem renamed_local_card (e : Equiv.Perm Clock) (F : Section3.TransitionForm Clock Var) :
    (renameTransition e F).current.locals_finite.toFinset.card=F.current.locals_finite.toFinset.card := by
  classical
  have hh : (renameTransition e F).current.locals_finite.toFinset=
      F.current.locals_finite.toFinset.image (fun l=>l.rename e) := by
    ext l
    simp only [Set.Finite.mem_toFinset,Finset.mem_image]
    rfl
  rw [hh,Finset.card_image_of_injective _ (local_rename_injective e)]



/-- Finite-partition recursion with the actual input injection carried across
successors. The caller supplies actual resolved steps, not a chosen path. -/
theorem allocated_path_of_resolved_steps
    (X : Set Var) (Q : Finset Clock) (L : ℕ)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (Inv : ClockValuation Clock → STLTableau.Judgement.Position P → Section3.StateForm Clock Var → Prop)
    (select : ∀ α k N, Inv α k N →
      ∃ (F : Section3.TransitionForm Clock Var) (U : Finset Clock) (C : ResolvedCertificate N F),
        F.holds σ P α k ∧ F.current.locals_finite.toFinset.card ≤ L ∧
        (Section3.TransitionForm.ofState N).allClocks_finite.toFinset ⊆ U ∧
        F.allClocks ⊆ (U : Set Clock) ∧ U.card ≤ Q.card ∧
        ∀ M, F.nextPart=some M → ∀hk : k.1<P.size,
          Inv (ClockResetSet.elapse (F.current.resets.apply α)
            (STLTableau.Judgement.duration P ⟨k.1,hk⟩)) ⟨k.1+1,by omega⟩ M)
    (α β : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (N : Section3.StateForm Clock Var) (hInv : Inv α k N)
    (e0 : Equiv.Perm Clock)
    (hMap : ∀ c∈(Section3.TransitionForm.ofState N).allClocks,e0 c∈Q)
    (hAgree : ∀ c∈N.freeClocks,β (e0 c)=α c) :
    ∃ p : Path Clock (Section3.TransitionForm Clock Var),
      p.run (JudgementTableau.tableau X (Q : Set Clock) (N.rename e0) FreeDerives) ∧
      p.accepting (JudgementTableau.tableau X (Q : Set Clock) (N.rename e0) FreeDerives) ∧
      (JudgementTableau.fullTrace p).holds σ P β k ∧
      Subgraph.AllStates {F | F.allClocks ⊆ (Q : Set Clock) ∧
        F.current.locals_finite.toFinset.card ≤ L} p := by
  classical
  let root := N.rename e0
  have main : ∀n : ℕ, ∀ (j : STLTableau.Judgement.Position P)
      (a b : ClockValuation Clock) (M : Section3.StateForm Clock Var),
      P.size-j.1=n → Inv a j M → ∀e0 : Equiv.Perm Clock,
      (∀c∈(Section3.TransitionForm.ofState M).allClocks,e0 c∈Q) →
      (∀c∈M.freeClocks,b (e0 c)=a c) →
      ∃ p : Path Clock (Section3.TransitionForm Clock Var),
        FreeDerives (M.rename e0) p.firstState ∧ p.firstIncoming=JudgementTableau.incoming p.firstState ∧
        p.accepting (JudgementTableau.tableau X (Q : Set Clock) root FreeDerives) ∧
        (JudgementTableau.fullTrace p).holds σ P b j ∧
        Subgraph.AllStates {F | F.allClocks ⊆ (Q : Set Clock) ∧
          F.current.locals_finite.toFinset.card ≤ L} p := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j a b M hn hI e0 hm ha
      obtain ⟨F,U,C,hF,hL,hU,hFU,hCard,hNext⟩ := select a j M hI
      obtain ⟨e,he,he0⟩ := extend_supported_permutation
        (Section3.TransitionForm.ofState M).allClocks_finite.toFinset U Q hU hCard e0
        (fun c hc=>hm c ((Set.Finite.mem_toFinset _).1 hc))
      have hEq : M.rename e=M.rename e0 := by
        apply state_rename_congr
        intro c hc
        apply he0 c
        exact (Set.Finite.mem_toFinset _).2 (by rw [ofState_support]; exact hc)
      have ha' : ∀c∈M.freeClocks,b (e c)=a c := by
        intro c hc
        have hs : c∈stateClockSupport M := by
          rcases hc with hg | ⟨hl,_⟩
          · exact Or.inl (Or.inl hg)
          · exact Or.inl (Or.inr hl)
        have heq := he0 c ((Set.Finite.mem_toFinset _).2 (by rw [ofState_support]; exact hs))
        rw [heq]
        exact ha c hc
      let G := renameTransition e F
      have hD : FreeDerives (M.rename e0) G := by rw [←hEq]; exact C.rename_freeDerives e
      have hG : G.holds σ P b j := resolved_rename_holds C.resolves C.input_safe C.full_safe e σ P a b j ha' hF
      have hGood : G.allClocks⊆(Q : Set Clock) ∧ G.current.locals_finite.toFinset.card≤L := by
        constructor
        · rw [renamed_whole_support]
          rintro c ⟨d,hd,rfl⟩
          exact he d (hFU hd)
        · rw [renamed_local_card]
          exact hL
      cases hnext : F.nextPart with
      | none =>
          have hg : G.nextPart=none := by simp [G,renameTransition,hnext]
          refine ⟨.last (JudgementTableau.incoming G) G,hD,rfl,?_,?_,hGood⟩
          · exact ⟨⟨M.rename e0,hD⟩,hg⟩
          · exact hG.1
      | some M' =>
          have hj : j.1<P.size := by
            by_contra hnot
            have hh := hF.2
            simp only [hnext,dif_neg hnot] at hh
          let j' : STLTableau.Judgement.Position P := ⟨j.1+1,by omega⟩
          let a' := ClockResetSet.elapse (F.current.resets.apply a) (STLTableau.Judgement.duration P ⟨j.1,hj⟩)
          let b' := ClockResetSet.elapse (G.current.resets.apply b) (STLTableau.Judgement.duration P ⟨j.1,hj⟩)
          have hm' : ∀c∈(Section3.TransitionForm.ofState M').allClocks,e c∈Q := by
            intro c hc
            exact he c (hFU (next_whole_support hnext hc))
          have ha'' : ∀c∈M'.freeClocks,b' (e c)=a' c :=
            renamed_successor_agreement hnext C.freeDerives.2 e e a b _ ha' (fun _ _=>rfl)
          obtain ⟨tail,htD,htIn,htA,htTrace,htGood⟩ :=
            ih (P.size-j'.1) (by dsimp [j']; omega) j' a' b' M' rfl
              (hNext M' hnext hj) e hm' ha''
          have hg : G.nextPart=some (M'.rename e) := by simp [G,renameTransition,hnext]
          refine ⟨.step (JudgementTableau.incoming G) G tail,hD,rfl,?_,?_,hGood,htGood⟩
          · refine ⟨⟨⟨M.rename e0,hD⟩,htA.1,?_⟩,htA.2⟩
            exact ⟨⟨M.rename e0,hD⟩,⟨M'.rename e,htD⟩,M'.rename e,hg,htD,htIn⟩
          · change G.current.holds σ P b j ∧ (if hk : j.1<P.size then _ else False)
            exact ⟨hG.1,by simpa only [dif_pos hj,JudgementTableau.fullTrace,Path.trace,Trace.holds,JudgementTableau.incoming,b',j'] using htTrace⟩
  obtain ⟨p,hD,hIn,hA,hTrace,hGood⟩ := main (P.size-k.1) k α β N rfl hInv e0 hMap hAgree
  refine ⟨p,⟨hA.1,?_⟩,hA,hTrace,hGood⟩
  exact ⟨hD,hIn⟩
end STLTableau.Section4.Finiteness
