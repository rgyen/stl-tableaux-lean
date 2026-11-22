import STLTableaux.Automata.Translation.PrelimForward
import STLTableaux.Automata.Translation.PrelimStateGoalForward
import STLTableaux.Automata.Translation.EndPositionTranslation
import STLTableaux.Automata.Translation.LocalClosureGraph
import STLTableaux.Automata.Recognition.ForwardWellBehaved
import STLTableaux.Tableau.Construction.Tableau
import STLTableaux.Semantics.Partitions.BoundaryPartition
import STLTableaux.Automata.Translation.RootAutomata
import STLTableaux.Finiteness.Derivation.DerivationRelation
import STLTableaux.Automata.Translation.TypedTableauAutomata

/-! A horizon-guard example where changing an earlier reset time allows
the last jump on the same signal and tableau graph. -/

/- EqualityInventory -/
namespace STLTableau.Section4.Finiteness.EqualityAudit
open Section3
namespace Inv
variable {Clock Var : Type*} {L : Finset (Local Clock Var)} {G : Finset (Guard Clock)}
    {R : Finset (Clock × NNReal)}
local notation "W" => FiniteInventory.Within L G R
local notation "TW" => FiniteInventory.TransitionWithin L G R

theorem nilW : W (Section3.StateForm.empty : Section3.StateForm Clock Var) := by
  exact ⟨Set.empty_subset _,Set.empty_subset _,fun _ _ he => by cases he⟩
theorem locW {l : Local Clock Var} (hl : l ∈ L) : W (Section3.StateForm.ofLocal l) := by
  exact ⟨Set.singleton_subset_iff.mpr hl,Set.empty_subset _,fun _ _ he => by cases he⟩
theorem guardW {g : Guard Clock} (hg : g ∈ G) : W (Section3.StateForm.ofGuard g) := by
  exact ⟨Set.empty_subset _,Set.singleton_subset_iff.mpr hg,fun _ _ he => by cases he⟩
theorem unionW {S K : Section3.StateForm Clock Var} (hs : W S) (hk : W K) : W (S.union K) := by
  refine ⟨Set.union_subset hs.1 hk.1,Set.union_subset hs.2.1 hk.2.1,?_⟩
  intro c a he
  change (match S.resets.value c with | some b => some b | none => K.resets.value c) = some a at he
  split at he
  next b hb => exact hs.2.2 c a (hb.trans he)
  next => exact hk.2.2 c a he
theorem stateW {S : Section3.StateForm Clock Var} (hs : W S) : TW (.ofState S) :=
  ⟨hs,fun _ he => by cases he⟩
theorem nextW {S : Section3.StateForm Clock Var} (hs : W S) : TW (.ofNextState S) :=
  ⟨nilW, fun _ he => Option.some.inj he ▸ hs⟩
theorem unionTW {F K : Section3.TransitionForm Clock Var} (hf : TW F) (hk : TW K) :
    TW (F.union K) := by
  refine ⟨unionW hf.1 hk.1,?_⟩
  intro N h
  change Section3.TransitionForm.unionNext F.nextPart K.nextPart = some N at h
  cases he : F.nextPart <;> cases hg : K.nextPart <;> rw [he,hg] at h
  · cases h
  · exact Option.some.inj h ▸ hk.2 _ hg
  · exact Option.some.inj h ▸ hf.2 _ he
  · exact Option.some.inj h ▸ unionW (hf.2 _ he) (hk.2 _ hg)
theorem resetTW {F : Section3.TransitionForm Clock Var} (hf : TW F) (c : Clock) (b : NNReal)
    [DecidableEq Clock] (hc : (c,b) ∈ R) : TW (F.underReset (ClockResetSet.singleton c b)) := by
  refine ⟨⟨hf.1.1,hf.1.2.1,?_⟩,hf.2⟩
  intro d a he
  change (match F.current.resets.value d with
    | some v => some v
    | none => (if d = c then some b else none)) = some a at he
  split at he
  next v h => exact hf.1.2.2 d a (h.trans he)
  next =>
    split_ifs at he with hd
    · subst d; cases he; exact hc

variable {Slot : Type*} [Fintype Slot] (P : Finset (Formula Var))
  (t : Slot → FiniteInventory.Triple Clock Var)
theorem memPlain {p : Formula Var} (hp : p ∈ P) :
    Local.predicate (.plain p) ∈ FiniteInventory.locals P t := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩))
theorem memClosed : Local.marker ● ∈ FiniteInventory.locals P t := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨some false,by simp,rfl⟩))
theorem memSlot (s : Slot) (tag : FiniteInventory.LocalTag) :
    FiniteInventory.slotLocal (t s) tag ∈ FiniteInventory.locals P t := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(s,tag),by simp,rfl⟩)
theorem memGuard (s : Slot) (c : Fin 3) (r : Fin 5) (e : Fin 3) :
    (⟨FiniteInventory.clockAt (t s) c,FiniteInventory.relationAt r,
      FiniteInventory.endpoint (t s).interval e⟩ : Guard Clock) ∈ FiniteInventory.guards t := by
  classical
  exact Finset.mem_image.mpr ⟨(s,c,r,e),by simp,rfl⟩
theorem memReset (s : Slot) (c e : Fin 3) :
    (FiniteInventory.clockAt (t s) c,FiniteInventory.endpoint (t s).interval e) ∈
      FiniteInventory.resets t := by
  classical
  exact Finset.mem_image.mpr ⟨(s,c,e),by simp,rfl⟩
end Inv
end STLTableau.Section4.Finiteness.EqualityAudit

/- ForwardWitnessTiming -/
namespace STLTableau.Section4.EqualityTiming
open Section3
variable {Var : Type*}
def startFrame (c : Nat) : Section3.StateForm Nat Var :=
  ⟨∅,Set.finite_empty,ClockResetSet.singleton c 0,{.marker ●},Set.finite_singleton _⟩
def middleFrame (c d : Nat) (p : Formula Var) : Section3.StateForm Nat Var :=
  ⟨{⟨c,.le,2⟩},Set.finite_singleton _,ClockResetSet.singleton d 0,
    {.predicate (.plain p),.marker ●},by simp⟩
def finishFrame (d : Nat) : Section3.StateForm Nat Var :=
  ⟨{⟨d,.ge,1⟩},Set.finite_singleton _,ClockResetSet.empty,{.marker ●},Set.finite_singleton _⟩

def trace (c d : Nat) (p : Formula Var) : Trace Nat Var :=
  .step (startFrame c) (.step (middleFrame c d p) (.last (finishFrame d)))

def horizonTimes : Fin 3 → ℝ := ![0,1,2]
noncomputable def earlyTimes : Fin 4 → ℝ := ![0,1/2,3/2,2]
def horizonPartition (σ : FiniteSignal Var) (hh : σ.horizon = 2) :
    IntervalPartition σ.domain :=
  let P := IntervalPartition.ofBoundaries horizonTimes (by
    intro i j hij; fin_cases i <;> fin_cases j <;> norm_num [horizonTimes] at *)
  {P with covers := P.covers.trans (by simp [FiniteSignal.domain,horizonTimes,hh])}
noncomputable def earlyPartition (σ : FiniteSignal Var) (hh : σ.horizon = 2) :
    IntervalPartition σ.domain :=
  let P := IntervalPartition.ofBoundaries earlyTimes (by
    intro i j hij; fin_cases i <;> fin_cases j <;> norm_num [earlyTimes] at *)
  {P with covers := P.covers.trans (by simp [FiniteSignal.domain,earlyTimes,hh])}

theorem trace_holds_at (c d : Nat) (p : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (hn : 2 ≤ P.size)
    (hm : ∀ i : Fin P.size, (P.interval i).leftBoundary = ●)
    (h0 : (STLTableau.Judgement.duration P ⟨0,by omega⟩ : ℝ) ≤ 2)
    (h1 : 1 ≤ (STLTableau.Judgement.duration P ⟨1,by omega⟩ : ℝ))
    (hp : ∀ t : σ.Time, σ.Satisfies p t) (α : ClockValuation Nat) :
    (trace c d p).holds σ P α ⟨0,by omega⟩ := by
  have mark (k : STLTableau.Judgement.Position P) (β : ClockValuation Nat) :
      (Local.marker ● : Local Nat Var).holds σ P β k := by
    by_cases hk : k.val < P.size <;>
      simp [Local.holds,Local.toJudgement,Section3.Judgement.holds,hk,hm]
  simp only [trace,Trace.holds,Trace.holdsWith,
    dif_pos (show 0 < P.size by omega),dif_pos (show 0+1 < P.size by omega)]
  refine ⟨⟨by simp [startFrame],?_⟩,⟨⟨?_,?_⟩,⟨?_,?_⟩⟩⟩
  · intro l hl; obtain rfl := Set.mem_singleton_iff.mp hl; apply mark
  · intro g hg; obtain rfl := Set.mem_singleton_iff.mp hg
    change (_ : ℝ) ≤ 2
    simpa [startFrame,ClockResetSet.elapse] using h0
  · intro l hl
    rcases Set.mem_insert_iff.mp hl with rfl | hl
    · simpa [Local.holds,Local.toJudgement,Section3.Judgement.holds,
        show 1 < P.size by omega,Predicate.holds,predicateSatisfies] using
        (fun (t : σ.Time) (_ : t.val ∈ (P.interval ⟨1,by omega⟩).carrier) => hp t)
    · obtain rfl := Set.mem_singleton_iff.mp hl; apply mark
  · intro g hg; obtain rfl := Set.mem_singleton_iff.mp hg
    change 1 ≤ (_ : ℝ)
    simpa [middleFrame,ClockResetSet.elapse] using h1
  · intro l hl; obtain rfl := Set.mem_singleton_iff.mp hl; apply mark

theorem on_horizon (c d : Nat) (p : Formula Var) (σ : FiniteSignal Var)
    (hh : σ.horizon = 2) (hp : ∀ t : σ.Time, σ.Satisfies p t) (α : ClockValuation Nat) :
    (trace c d p).holds σ (horizonPartition σ hh) α ⟨0,by change 0 < 3; decide⟩ := by
  apply trace_holds_at _ _ _ _ _ (by change 2 ≤ 2; decide) (by intro i; rfl) _ _ hp
  · change (1 : ℝ) - 0 ≤ 2
    norm_num
  · change (1 : ℝ) ≤ 2 - 1
    norm_num

theorem on_early (c d : Nat) (p : Formula Var) (σ : FiniteSignal Var)
    (hh : σ.horizon = 2) (hp : ∀ t : σ.Time, σ.Satisfies p t) (α : ClockValuation Nat) :
    (trace c d p).holds σ (earlyPartition σ hh) α ⟨0,by change 0 < 4; decide⟩ := by
  apply trace_holds_at _ _ _ _ _ (by change 2 ≤ 3; decide) (by intro i; rfl) _ _ hp
  · change (1/2 : ℝ) - 0 ≤ 2
    norm_num
  · change (1 : ℝ) ≤ 3/2 - 1/2
    norm_num

end STLTableau.Section4.EqualityTiming

/- EqualityDerivation -/
namespace STLTableau.Section4.Finiteness.EqualityAudit
open Section3
def I : BoundedTimeInterval := ⟨1,2,by norm_num,by norm_num⟩
def atom : AtomicProposition Unit := ⟨1,fun _ => (),fun v => v 0,.ge⟩
def p : Formula Unit := .atom atom
def root : Formula Unit := .eventually I p
noncomputable def slot : RootSlot root :=
  ⟨⟨(.eventually, I, p), (Finiteness.mem_rootTemporalSignatures_iff root .eventually I p).mpr (.refl _)⟩,
    ⟨0, by omega⟩⟩
noncomputable def c : Nat := (rootSlotTriples root slot).left
noncomputable def d : Nat := (rootSlotTriples root slot).right₀
theorem cd : c ≠ d := by
  intro he
  have he' := (rootSlotClock (Clock := Nat) root).injective he
  have : (0 : Fin 3) = 1 := congrArg Prod.snd he'
  simp at this
noncomputable abbrev up : Predicate Nat Unit := .upper c ● .eventually I p
noncomputable abbrev bd : Predicate Nat Unit := .bounded c d ● ○ .eventually I p
noncomputable abbrev Rc := ClockResetSet.singleton c 0
noncomputable abbrev Rd := ClockResetSet.singleton d 0
abbrev J := MixedJ Nat Unit
abbrev F := Section3.TransitionForm Nat Unit
abbrev S := Section3.StateForm Nat Unit
abbrev leaf (l : Local Nat Unit) : F := .ofState (.ofLocal l)
noncomputable abbrev G1 : S := Section3.StateForm.ofGuard ⟨c,.le,2⟩
noncomputable abbrev G2 : S := Section3.StateForm.ofGuard ⟨d,.ge,1⟩
noncomputable abbrev j1 : J := .conj (.clock c .le 2)
    (.reset Rd (.conj (.predicate bd) (.marker ●)))
noncomputable abbrev j2 : J := .conj (.clock d .ge 1) (.marker ●)
noncomputable abbrev N1 : S := ((.ofState G1 : F).union
  (((leaf (.predicate bd)).union (leaf (.marker ●))).underReset Rd)).current
noncomputable abbrev N2 : S := G2.union (.ofLocal (.marker ●))
noncomputable abbrev F0 : F := (leaf (.predicate (.plain root))).union
  ((((leaf (.predicate up)).union (.ofNextState N1)).union (leaf (.marker ●))).underReset Rc)
noncomputable abbrev F1 : F := (.ofState G1 : F).union
  ((((leaf (.predicate bd)).union ((leaf (.predicate (.plain p))).union (.ofNextState N2))).union
    (leaf (.marker ●))).underReset Rd)
noncomputable abbrev F2 : F := .ofState N2
noncomputable abbrev H0 : J := .conj (.predicate (.plain root))
    (.reset Rc (.conj (.conj (.predicate up) (.next j1)) (.marker ●)))
noncomputable abbrev A0 : J := .reset Rc (.conj (.next j1) (.marker ●))
noncomputable abbrev H1 : J := .conj (.clock c .le 2)
  (.reset Rd (.conj (.conj (.predicate bd) (.conj (.predicate (.plain p)) (.next j2))) (.marker ●)))
noncomputable abbrev A1 : J := .conj (.clock c .le 2)
  (.reset Rd (.conj (.conj (.predicate (.plain p)) (.next j2)) (.marker ●)))

noncomputable def resolveUp : Resolve (.predicate up) (.conj (.predicate up) (.next j1)) (.next j1) := by
  refine .expandSolo (.finite (.upperEventually c d ● I p cd)
    (B := ExpansionRule.upperEventually_defer c d ● ● I p) ?_) ?_ ?_ (.leaf (.next _))
  · simp [ExpansionRule.upperEventually]
  · simp [Predicate.IsAtomic]
  · exact Set.disjoint_sdiff_left

noncomputable def resolve0 : Resolve (.predicate (.plain root)) H0 A0 := by
  refine .expandSolo (.finite (.openEventually c I p)
    (B := .reset Rc (.conj (.predicate (.upper c ● .eventually I p)) (.leftMarker ●))) ?_)
    ?_ ?_ (.reset Rc (.conj resolveUp (.leaf (.marker ●))))
  · simp [ExpansionRule.openEventually]
  · simp [Predicate.IsAtomic,root,Formula.eventually]
  · exact Set.disjoint_sdiff_left

noncomputable def resolveBd : Resolve (.predicate bd)
    (.conj (.predicate bd) (.conj (.predicate (.plain p)) (.next j2)))
    (.conj (.predicate (.plain p)) (.next j2)) := by
  refine .expandSolo (.finite (.boundedEventually c d ● ○ I p cd)
    (B := ExpansionRule.boundedEventually_finish d ○ ● I p) ?_) ?_ ?_
    (.conj (.leaf (.atomic _ (by trivial))) (.leaf (.next _)))
  · simp [ExpansionRule.boundedEventually]
  · simp [Predicate.IsAtomic]
  · exact Set.disjoint_sdiff_left

noncomputable def resolve1 : Resolve j1 H1 A1 :=
  .conj (.leaf (.clock _ _ _)) (.reset Rd (.conj resolveBd (.leaf (.marker ●))))

set_option linter.unusedSimpArgs false
set_option maxRecDepth 6000
set_option maxHeartbeats 2400000

macro "eq_simp" : tactic => `(tactic|
  simp [-ENNReal.none_eq_top, -ENNReal.some_eq_coe,
    G1,G2,N1,N2,leaf,up,bd,Rc,Rd,
    Section3.TransitionForm.boundClocks,Section3.TransitionForm.allClocks,
    Section3.TransitionForm.freeClocks,Section3.TransitionForm.bodyFreeClocks,
    Section3.TransitionForm.union,Section3.TransitionForm.unionNext,Section3.TransitionForm.underReset,
    Section3.TransitionForm.ofState,Section3.TransitionForm.ofNextState,Section3.StateForm.empty,
    Section3.StateForm.ofGuard,Section3.StateForm.ofLocal,Section3.StateForm.union,
    Section3.StateForm.guardClocks,Section3.StateForm.localClocks,Section3.StateForm.freeClocks,
    Local.freeClocks,Local.toJudgement,Section3.Judgement.freeClocks,
    ClockResetSet.clocks_union,ClockResetSet.clocks,ClockResetSet.union,ClockResetSet.empty,
    ClockResetSet.singleton,Set.disjoint_left,cd,Ne.symm cd])
macro "sjoin" x:term:max y:term:max : term =>
  `(SafeNormalization.conj $x $y (by apply Section3.TransitionForm.unionCompatible_of_boundFresh <;> eq_simp))
macro "sreset" x:term:max y:term:max : term =>
  `(SafeNormalization.reset $x $y (by eq_simp))

theorem safen1 : SafeNormalization j1 (.ofState N1) :=
  sjoin (.clock c .le 2) (sreset Rd (sjoin (.predicate bd) (.marker ●)))
theorem safen2 : SafeNormalization j2 (.ofState N2) :=
  sjoin (.clock d .ge 1) (.marker ●)
theorem safeh0 : SafeNormalization H0 F0 :=
  sjoin (.predicate (.plain root)) (sreset Rc
    (sjoin (sjoin (.predicate up) (.next safen1 rfl)) (.marker ●)))
theorem safeh1 : SafeNormalization H1 F1 :=
  sjoin (.clock c .le 2) (sreset Rd
    (sjoin (sjoin (.predicate bd) (sjoin (.predicate (.plain p)) (.next safen2 rfl))) (.marker ●)))

private theorem erasedFrom {J H A : MixedJ Nat Unit} {F G : Section3.TransitionForm Nat Unit}
    (D : Resolve J H A) (hF : SafeNormalization H F) (hG : SafeNormalization A G) :
    SafeNormalization A F.atomicProjection := by
  have he : some G = some F.atomicProjection := by
    rw [← hG.normalizes,D.normalize_erased_eq_projection,hF.normalizes]
    rfl
  exact Option.some.inj he ▸ hG
theorem derives0 : Derives (.ofLocal (.predicate (.plain root))) F0 :=
  .resolved resolve0 (.predicate _) safeh0 (erasedFrom resolve0 safeh0
    (sreset Rc (sjoin (.next safen1 rfl) (.marker ●))))
theorem derives1 : Derives N1 F1 :=
  .resolved resolve1 safen1 safeh1 (erasedFrom resolve1 safeh1
    (sjoin (.clock c .le 2) (sreset Rd (sjoin
      (sjoin (.predicate (.plain p)) (.next safen2 rfl)) (.marker ●)))))
theorem derives2 : Derives N2 F2 := by
  let D : Resolve j2 j2 j2 := .conj (.leaf (.clock d .ge 1)) (.leaf (.marker ●))
  exact .resolved D safen2 safen2 (erasedFrom D safen2 safen2)

noncomputable def actualPath : Path Nat F :=
  .step (JudgementTableau.incoming F0) F0
    (.step (JudgementTableau.incoming F1) F1 (.last (JudgementTableau.incoming F2) F2))
noncomputable abbrev rawGraph := JudgementTableau.tableau (Set.univ : Set Unit)
  (Set.univ : Set Nat) (.ofLocal (.predicate (.plain root))) Derives
theorem actualPath_raw_accepting : actualPath.run rawGraph ∧ actualPath.accepting rawGraph := by
  have hv : actualPath.valid rawGraph :=
    ⟨⟨_,derives0⟩, ⟨⟨_,derives1⟩,⟨_,derives2⟩,⟨_,derives1⟩,⟨_,derives2⟩,_,rfl,derives2,rfl⟩,
      ⟨_,derives0⟩,⟨_,derives1⟩,_,rfl,derives1,rfl⟩
  exact ⟨⟨hv,derives0,rfl⟩,hv,rfl⟩

macro "framesimp" : tactic => `(tactic|
  simp [F0,F1,F2,N1,N2,G1,G2,leaf,Rc,Rd,JudgementTableau.labels,
    Section3.TransitionForm.union,Section3.TransitionForm.underReset,
    Section3.TransitionForm.ofState,Section3.TransitionForm.ofNextState,
    Section3.StateForm.empty,Section3.StateForm.ofGuard,Section3.StateForm.ofLocal,
    Section3.StateForm.union,ClockResetSet.union,ClockResetSet.empty,ClockResetSet.singleton,
    Section3.TransitionForm.KeepAtomic,Predicate.IsAtomic,root,p,
    Formula.eventually,up,bd])
theorem currentGuards0 : F0.current.guards = ∅ := by framesimp
theorem currentGuards1 : F1.current.guards = {⟨c,.le,2⟩} := by framesimp
theorem currentGuards2 : F2.current.guards = {⟨d,.ge,1⟩} := by framesimp
theorem currentResets0 : F0.current.resets = Rc := by rfl
theorem currentResets1 : F1.current.resets = Rd := by rfl
theorem currentResets2 : F2.current.resets = ClockResetSet.empty := by rfl
theorem labels0 : JudgementTableau.labels F0 = {.marker ●} := by
  ext l
  cases l <;> framesimp
  rintro (rfl | rfl) <;> exact id
theorem labels1 : JudgementTableau.labels F1 = {.predicate (.plain p),.marker ●} := by
  ext l
  cases l <;> framesimp
  constructor
  · rintro ⟨rfl | rfl, h⟩
    · rfl
    · exact False.elim h
  · rintro rfl
    exact ⟨Or.inl rfl,trivial⟩
theorem labels2 : JudgementTableau.labels F2 = {.marker ●} := by
  ext l
  cases l <;> framesimp

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[``derives0,``derives1,``derives2,``actualPath_raw_accepting,
     ``labels0,``labels1,``labels2] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do throwError "{n} uses unexpected axiom {ax}"

end STLTableau.Section4.Finiteness.EqualityAudit

/- EqualityAdmission -/
namespace STLTableau.Section4.Finiteness.EqualityAudit
open Section3 Inv

noncomputable abbrev slots := rootSlotTriples (Clock := Nat) root
noncomputable abbrev locals := FiniteInventory.locals (Finiteness.rootPlainFormulas root) slots
noncomputable abbrev guards := FiniteInventory.guards slots
noncomputable abbrev resets := FiniteInventory.resets slots
noncomputable abbrev admissible := FiniteInventory.TransitionWithin locals guards resets
noncomputable abbrev admissibleS := FiniteInventory.Within locals guards resets

theorem memroot : Local.predicate (.plain root) ∈ locals :=
  Inv.memPlain _ _ (Finiteness.root_mem_rootPlainFormulas _)
theorem memp : Local.predicate (.plain p) ∈ locals :=
  Inv.memPlain _ _ (by simp [root,Formula.eventually,Finiteness.rootPlainFormulas,p])
theorem memup : Local.predicate up ∈ locals :=
  Inv.memSlot _ slots slot (.inl false)
theorem membd : Local.predicate bd ∈ locals :=
  Inv.memSlot _ slots slot (.inr (false,false,true))
theorem memm : Local.marker ● ∈ locals := Inv.memClosed _ _
theorem memgc : (⟨c,.le,2⟩ : Guard Nat) ∈ guards :=
  Inv.memGuard slots slot 0 4 2
theorem memgd : (⟨d,.ge,1⟩ : Guard Nat) ∈ guards :=
  Inv.memGuard slots slot 1 0 1
theorem memrc : (c,(0 : NNReal)) ∈ resets := Inv.memReset slots slot 0 0
theorem memrd : (d,(0 : NNReal)) ∈ resets := Inv.memReset slots slot 1 0

private theorem leafW {l} (hl : l ∈ locals) : admissible (leaf l) :=
  Inv.stateW (Inv.locW hl)
private theorem N1W : admissibleS N1 :=
  (Inv.unionTW (Inv.stateW (Inv.guardW memgc))
    (Inv.resetTW (Inv.unionTW (leafW membd) (leafW memm)) d 0 memrd)).1
private theorem N2W : admissibleS N2 := Inv.unionW (Inv.guardW memgd) (Inv.locW memm)

theorem F0W : admissible F0 :=
  Inv.unionTW (leafW memroot)
    (Inv.resetTW (Inv.unionTW (Inv.unionTW (leafW memup) (Inv.nextW N1W))
      (leafW memm)) c 0 memrc)
theorem F1W : admissible F1 :=
  Inv.unionTW (Inv.stateW (Inv.guardW memgc))
    (Inv.resetTW (Inv.unionTW (Inv.unionTW (leafW membd)
        (Inv.unionTW (leafW memp) (Inv.nextW N2W))) (leafW memm)) d 0 memrd)
theorem F2W : admissible F2 := Inv.stateW N2W

abbrev input : Formula.NormalizedInput Unit := ⟨root,.eventually _ (.atom _)⟩
local notation "T" => (inputTableau (Clock := Nat) (Set.univ : Set Unit) input)
local notation "U" => (localClosureGraph (Clock := Nat) (Set.univ : Set Unit) input)
theorem mem0 : F0 ∈ (T).states := ⟨⟨_,derives0⟩,F0W⟩
theorem mem1 : F1 ∈ (T).states := ⟨⟨_,derives1⟩,F1W⟩
theorem mem2 : F2 ∈ (T).states := ⟨⟨_,derives2⟩,F2W⟩

private theorem consistent_of_no_star (F : Section3.TransitionForm Nat Unit)
    (hc : Local.terminal ∉ F.current.locals)
    (hn : ∀ N ∈ F.nextPart, Local.terminal ∉ N.locals) : ConsistentClosure F :=
  ⟨fun h => (hc h).elim,fun N h ht => (hn N h ht).elim⟩
local macro "listsimp" : tactic => `(tactic| simp [F0,F1,F2,N1,N2,G1,G2,leaf,
    Section3.TransitionForm.union,Section3.TransitionForm.unionNext,
    Section3.TransitionForm.underReset,Section3.TransitionForm.ofState,
    Section3.TransitionForm.ofNextState,Section3.StateForm.union,Section3.StateForm.empty,
    Section3.StateForm.ofLocal,Section3.StateForm.ofGuard])
theorem consistent0 : ConsistentClosure F0 := by
  apply consistent_of_no_star
  · listsimp
  · intro N hN
    change some N1 = some N at hN
    obtain rfl := Option.some.inj hN
    listsimp
theorem consistent1 : ConsistentClosure F1 := by
  apply consistent_of_no_star
  · listsimp
  · intro N hN
    change some N2 = some N at hN
    obtain rfl := Option.some.inj hN
    listsimp
theorem consistent2 : ConsistentClosure F2 := by
  apply consistent_of_no_star
  · listsimp
  · intro N hN; cases hN

theorem local_mem0 : F0 ∈ (U).states := ⟨Or.inr mem0,consistent0⟩
theorem local_mem1 : F1 ∈ (U).states := ⟨Or.inr mem1,consistent1⟩
theorem local_mem2 : F2 ∈ (U).states := ⟨Or.inr mem2,consistent2⟩

theorem local_init : (JudgementTableau.incoming F0,F0) ∈ (U).initial :=
  ⟨⟨⟨derives0,rfl⟩,mem0⟩,local_mem0⟩
theorem local_edge01 : (F0,JudgementTableau.incoming F1,F1) ∈ (U).edges :=
  ⟨Or.inl ⟨⟨mem0.1,mem1.1,N1,rfl,derives1,rfl⟩,mem0,mem1⟩,local_mem0,local_mem1⟩
theorem local_edge12 : (F1,JudgementTableau.incoming F2,F2) ∈ (U).edges :=
  ⟨Or.inl ⟨⟨mem1.1,mem2.1,N2,rfl,derives2,rfl⟩,mem1,mem2⟩,local_mem1,local_mem2⟩
theorem local_final2 : F2 ∈ (U).final := ⟨Or.inr ⟨rfl,mem2⟩,local_mem2⟩
theorem local_not_final1 : F1 ∉ (U).final := by
  rintro ⟨h,_⟩
  rcases h with h | h
  · have hx := congrArg Section3.TransitionForm.nextPart h
    change some N2 = none at hx
    contradiction
  · have hx : F1.nextPart = none := h.1
    cases hx

noncomputable abbrev π : Path Nat F := .step (JudgementTableau.incoming F0) F0
  (.step (JudgementTableau.incoming F1) F1 (.last (JudgementTableau.incoming F2) F2))
theorem actual_path : π.run U ∧ π.accepting U := by
  have hv : π.valid U := ⟨local_mem0,⟨local_mem1,local_mem2,local_edge12⟩,local_edge01⟩
  exact ⟨⟨hv,local_init⟩,hv,local_final2⟩

local macro "frame_components" : tactic => `(tactic| simp [JudgementTableau.labels,
    F0,F1,F2,N1,N2,G1,G2,leaf,JudgementTableau.incoming,
    Section3.TransitionForm.KeepAtomic,Predicate.IsAtomic,root,Formula.eventually,p,
    Section3.TransitionForm.union,Section3.TransitionForm.unionNext,
    Section3.TransitionForm.underReset,Section3.TransitionForm.ofState,
    Section3.TransitionForm.ofNextState,Section3.StateForm.union,Section3.StateForm.empty,
    Section3.StateForm.ofLocal,Section3.StateForm.ofGuard,up,bd,Set.ext_iff])
theorem label0 : JudgementTableau.labels F0 = {Local.marker ●} := by
  ext l
  cases l with
  | marker _ | terminal => frame_components
  | predicate pp => cases pp with
    | plain φ => cases φ <;> frame_components
    | upper | bounded => frame_components
theorem label1 : JudgementTableau.labels F1 = {Local.predicate (.plain p),Local.marker ●} := by
  ext l
  cases l with
  | marker _ | terminal => frame_components
  | predicate pp => cases pp with
    | plain φ => cases φ <;> frame_components
    | upper | bounded => frame_components
theorem label2 : JudgementTableau.labels F2 = {Local.marker ●} := by
  ext l
  cases l <;> frame_components
theorem guards0 : (JudgementTableau.incoming F0).guards = ∅ := by frame_components
theorem guards1 : (JudgementTableau.incoming F1).guards = {⟨c,.le,2⟩} := by frame_components
theorem guards2 : (JudgementTableau.incoming F2).guards = {⟨d,.ge,1⟩} := by frame_components
theorem resets0 : (JudgementTableau.incoming F0).resets = Rc := by
  rfl
theorem resets1 : (JudgementTableau.incoming F1).resets = Rd := by
  rfl
theorem resets2 : (JudgementTableau.incoming F2).resets = ClockResetSet.empty := by
  rfl

/-- No other edge from the middle state to F₂ evades this guard. -/
theorem edge12_label {l : EdgeLabel Nat} (he : (F1,l,F2) ∈ (U).edges) :
    l = JudgementTableau.incoming F2 := by
  rcases he.1 with old | extra
  · obtain ⟨_,_,_,_,_,hl⟩ := old.1
    exact hl
  · have hn : F1.nextPart = none := extra.1.1
    cases hn

/-- From a split at time 1 (d reset there), the middle-to-final
jump is impossible at every time: its guard forces global time ≥2,
while its non-star target forces time <2. -/
theorem no_jump_after_unit_split (h : (U).TranslationReady)
    {s s' : ((U).typedAutomaton h 2).State}
    (hq : s.val.1.val = F1) (hq' : s'.val.1.val = F2)
    (hd : ∀ hc : d ∈ (U).clocks,
      s.val.2 (.inl (.inr (.inl ⟨d,hc⟩))) =
        s.val.2 (.inl (U).globalClock) - 1) :
    ¬ ((U).typedAutomaton h 2).DiscreteStep s s' := by
  rintro ⟨edge,hs,ht,_,_,hguard,_,hglobal,_,hterminal,_⟩
  have he : (F1,edge.val.2.1,F2) ∈ (U).edges := by
    rw [← hq,← hq',← hs,← ht]
    exact edge.property
  have hg : (⟨d,.ge,1⟩ : Guard Nat) ∈ edge.val.2.1.guards := by
    rw [edge12_label he,guards2]
    exact Set.mem_singleton _
  obtain ⟨hc,hcmp⟩ := hguard _ hg
  change s.val.2 (.inl (.inr (.inl ⟨d,hc⟩))) ≥ 1 at hcmp
  rw [hd hc] at hcmp
  have ht' : s'.val.1 ∈ (U).terminalModes := hterminal.mpr (by linarith)
  change Local.terminal ∈ JudgementTableau.labels s'.val.1.val at ht'
  rw [hq',label2] at ht'
  cases ht'

run_elab do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for n in #[``actual_path,``local_not_final1,``label0,``label1,``label2,``no_jump_after_unit_split] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do throwError "{n} uses unexpected axiom {ax}"
end STLTableau.Section4.Finiteness.EqualityAudit

/- EqualityBridge -/
namespace STLTableau.Section4.Finiteness.EqualityAudit
open Section3
noncomputable abbrev observed (K : F) : S :=
  ⟨K.current.guards,K.current.guards_finite,K.current.resets,
    JudgementTableau.labels K,JudgementTableau.labels_finite K⟩
theorem frame0 : observed F0 = EqualityTiming.startFrame c :=
  Section3.StateForm.ext_components currentGuards0 currentResets0 labels0
theorem frame1 : observed F1 = EqualityTiming.middleFrame c d p :=
  Section3.StateForm.ext_components currentGuards1 currentResets1 labels1
theorem frame2 : observed F2 = EqualityTiming.finishFrame d :=
  Section3.StateForm.ext_components currentGuards2 currentResets2 labels2
theorem actual_trace_eq : actualPath.trace JudgementTableau.labels JudgementTableau.labels_finite =
    EqualityTiming.trace c d p := by
  change Trace.step (observed F0) (.step (observed F1) (.last (observed F2))) = _
  rw [frame0,frame1,frame2]
  rfl
theorem actual_horizon (σ : FiniteSignal Unit) (hh : σ.horizon = 2)
    (hp : ∀ t : σ.Time, σ.Satisfies p t) (α : ClockValuation Nat) :
    (actualPath.trace JudgementTableau.labels JudgementTableau.labels_finite).holds
      σ (EqualityTiming.horizonPartition σ hh) α ⟨0,by omega⟩ := by
  rw [actual_trace_eq]
  exact EqualityTiming.on_horizon c d p σ hh hp α
theorem actual_early (σ : FiniteSignal Unit) (hh : σ.horizon = 2)
    (hp : ∀ t : σ.Time, σ.Satisfies p t) (α : ClockValuation Nat) :
    (actualPath.trace JudgementTableau.labels JudgementTableau.labels_finite).holds
      σ (EqualityTiming.earlyPartition σ hh) α ⟨0,by omega⟩ := by
  rw [actual_trace_eq]
  exact EqualityTiming.on_early c d p σ hh hp α
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[``actual_trace_eq,``actual_horizon,``actual_early] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do throwError "{n} uses unexpected axiom {ax}"
end STLTableau.Section4.Finiteness.EqualityAudit

/- RetimedConcreteExecution -/
namespace STLTableau.Section4.Tableau.Retimed
open Section3
variable {Var State : Type*} (T : Tableau ℕ Var State)
noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
def bounds (i : Fin 4) : ℝ := if i.val = 0 then 0 else if i.val = 1 then 1/2 else if i.val = 2 then 3/2 else 2
def dt : Fin 3 → NNReal := ![1/2,1,1/2]
private theorem diff (i : Fin 3) : (dt i : ℝ) = bounds i.succ - bounds i.castSucc := by
  fin_cases i <;> norm_num [bounds,dt,Fin.succ]

def value (d : ℕ) (i : Fin 3) (u : ℝ) : T.TypedVar → ℝ
  | .inl (.inl _) => 0
  | .inl (.inr (.inl k)) => bounds i.castSucc + u - (if k.val = d ∧ i.val ≠ 0 then 1/2 else 0)
  | .inl (.inr (.inr _)) => bounds i.castSucc + u
  | .inr false => u
  | .inr true => 1

def signal (d : ℕ) : FiniteSignal T.TypedVar :=
  ⟨2,by norm_num,fun t => if t.val < 1/2 then value T d 0 t.val
    else if t.val < 3/2 then value T d 1 (t.val-1/2) else value T d 2 (t.val-3/2)⟩

def initL (c : ℕ) : EdgeLabel ℕ := ⟨∅,Set.finite_empty,.singleton c 0⟩
def waitL (c d : ℕ) : EdgeLabel ℕ := ⟨{⟨c,.le,2⟩},Set.finite_singleton _,.singleton d 0⟩
def endL (d : ℕ) : EdgeLabel ℕ := ⟨{⟨d,.ge,1⟩},Set.finite_singleton _,.empty⟩

structure Admitted (c d : ℕ) (q : Fin 3 → T.states) : Prop where
  init : (initL c,(q 0).val) ∈ T.initial
  first : ((q 0).val,waitL c d,(q 1).val) ∈ T.edges
  second : ((q 1).val,endL d,(q 2).val) ∈ T.edges
  ordinary : ∀ i, q i ∉ T.terminalModes
  mark : ∀ i m, Local.marker m ∈ T.label (q i).val → m = ●
  atoms : ∀ i a, Local.predicate (.plain (.atom a)) ∈ T.label (q i).val → a.Holds (fun _ => 0)
  goal : q 2 ∈ T.goalModes

variable {c d : ℕ} {q : Fin 3 → T.states} (h : T.TranslationReady) (g : Admitted T c d q)
local notation "H" => (T.typedAutomaton h 2)
include g
private theorem inv (i : Fin 3) (u : ℝ) (hu : 0 ≤ u ∧ u ≤ dt i) :
    ((q i),value T d i u) ∈ (H).invariant := by
  refine ⟨Or.inr rfl,?_,?_,?_⟩
  · intro _
    change bounds i.castSucc + u ≤ 2
    fin_cases i <;> norm_num [bounds,dt] at hu ⊢ <;> linarith
  · intro a ha
    exact (T.atomHolds_iff _ _ (fun _ => 0) (h.atom_variables _ (q i).property a ha)
      (fun _ => rfl)).mpr (g.atoms i a ha)
  · intro m hm
    exact ⟨fun _ => rfl,fun _ => g.mark i m hm⟩

private def st (i : Fin 3) (u : Set.Icc (0 : ℝ) (dt i)) : (H).State :=
  ⟨⟨q i,value T d i u.val⟩,inv T h g i u.val u.property⟩

private theorem flowing (i : Fin 3) :
    (H).ContinuousStep (st T h g i ⟨0,by simp⟩) (st T h g i ⟨dt i,by simp⟩)
      (dt i) (fun u => value T d i u.val) := by
  refine ⟨rfl,rfl,rfl,fun u => ⟨⟨?_,?_,?_,rfl⟩,inv T h g _ _ u.property⟩⟩
  · intro k
    simp only [st,value,add_zero]
    change (bounds i.castSucc + u.val - _) = (bounds i.castSucc - _) + u.val
    ring
  · change bounds i.castSucc + u.val = (bounds i.castSucc + 0) + u.val
    ring
  · change u.val = 0 + u.val
    ring

private theorem initial : (st T h g 0 ⟨0,by simp⟩).val ∈ (H).initial := by
  refine ⟨initL c,g.init,(fun _ => 0),fun k hk => hk.elim,?_,rfl,rfl⟩
  funext k
  cases k with
  | inl x => rfl
  | inr k =>
    cases k with
    | inr z => norm_num [old,value,globalClock,initialReset,bounds,st]
    | inl k =>
      by_cases hk : k.val = c <;> norm_num [old,value,initialReset,reset,initL,ClockResetSet.singleton,st,bounds,hk] <;> rfl

private theorem jump01 :
    (H).DiscreteStep (st T h g 0 ⟨dt 0,by simp⟩) (st T h g 1 ⟨0,by simp⟩) := by
  refine ⟨⟨(q 0,waitL c d,q 1),g.first⟩,rfl,rfl,rfl,rfl,?_,?_,?_,rfl,?_,?_,?_⟩
  · intro j hj
    have hj' := Set.mem_singleton_iff.mp hj
    subst j
    refine ⟨h.edge_guards _ g.first _ (Set.mem_singleton _),?_⟩
    norm_num [st,old,value,bounds,dt,realComparison]
  · intro k
    by_cases hk : k.val = d <;>
      norm_num [st,old,value,reset,waitL,ClockResetSet.singleton,hk,bounds,dt] <;> rfl
  · norm_num [st,value,globalClock,dt,bounds]
  · change q 1 ∈ T.terminalModes ↔ _
    simp [g.ordinary 1,st,value,globalClock,bounds]
    norm_num
  · intro hz
    norm_num [st,value,dwell,dt] at hz
  · intro hz
    norm_num [st,value,bit] at hz

private theorem jump12 :
    (H).DiscreteStep (st T h g 1 ⟨dt 1,by simp⟩) (st T h g 2 ⟨0,by simp⟩) := by
  refine ⟨⟨(q 1,endL d,q 2),g.second⟩,rfl,rfl,rfl,rfl,?_,?_,?_,rfl,?_,?_,?_⟩
  · intro j hj
    have hj' := Set.mem_singleton_iff.mp hj
    subst j
    refine ⟨h.edge_guards _ g.second _ (Set.mem_singleton _),?_⟩
    norm_num [st,old,value,bounds,dt,realComparison]
  · intro k
    by_cases hk : k.val = d <;>
      norm_num [st,old,value,reset,endL,ClockResetSet.empty,hk,bounds,dt] <;> rfl
  · norm_num [st,value,globalClock,dt,bounds]
  · change q 2 ∈ T.terminalModes ↔ _
    simp [g.ordinary 2,st,value,globalClock,bounds]
    norm_num
  · intro hz
    norm_num [st,value,dwell,dt] at hz
  · intro hz
    norm_num [st,value,bit] at hz

def execution : (H).Execution (signal T d) where
  count := 3
  nonempty := by decide
  initialState := st T h g 0 ⟨0,by simp⟩
  initial_mem := initial T h g
  initial_signal_eq := by simp [signal, value, st, bounds]
  start := fun i => st T h g i ⟨0,by simp⟩
  finish := fun i => st T h g i ⟨dt i,by simp⟩
  boundary := bounds
  first_zero := rfl
  increasing := by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num [bounds] at *
  last_le_horizon := by norm_num [bounds,signal]
  duration := dt
  duration_eq := diff
  curve := fun i t => value T d i t.val
  continuousStep := flowing T h g
  initialSteps := .refl
  discreteSteps := by
    intro i hi
    fin_cases i
    · exact .single (jump01 T h g)
    · exact .single (jump12 T h g)
    · norm_num at hi
  finalState := st T h g 2 ⟨dt 2,by simp⟩
  finalSteps := .refl
  final_signal_eq := by intro t ht; have := t.property.2; norm_num [signal,bounds] at *; linarith
  signal_eq := by
    intro i t ht positive
    fin_cases i <;> norm_num [bounds] at ht ⊢
    · simp only [signal,if_pos ht.2]
    · simp only [signal,if_neg (not_lt.mpr ht.1),if_pos ht.2]
    · simp only [signal,if_neg (not_lt.mpr (show (1/2 : ℝ) ≤ t.val by linarith [ht.1])),if_neg (not_lt.mpr ht.1)]
      rfl

theorem reaches : (H).Reaches (signal T d) T.goalModes := ⟨execution T h g,g.goal⟩

omit g in
theorem original_constant (t : (signal T d).Time) (x : T.realVariables) :
    (signal T d).value t (.inl (.inl x)) = 0 := by
  simp only [signal]
  split <;> rename_i h
  · rfl
  · split <;> rfl

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``execution, ``reaches, ``original_constant] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do throwError "{name} uses unapproved axiom {ax}"

end
end STLTableau.Section4.Tableau.Retimed

/- EqualityExecution -/
namespace STLTableau.Section4.Finiteness.EqualityAudit
open Section3 Tableau.Retimed
noncomputable section
local notation "U" => (localClosureGraph (Clock := Nat) (Set.univ : Set Unit) input)

theorem ready : (U).TranslationReady :=
  localClosure_ready _ _ (finiteRootTableau_translationReady _ Set.finite_univ _ (by simp))

def modes : Fin 3 → (U).states :=
  ![⟨F0,local_mem0⟩,⟨F1,local_mem1⟩,⟨F2,local_mem2⟩]

private theorem label_ext (a b : EdgeLabel ℕ) (hg : a.guards = b.guards)
    (hr : a.resets = b.resets) : a = b := by cases a; cases b; simp_all

theorem admitted : Admitted U c d modes := by
  have h0 : JudgementTableau.incoming F0 = initL c :=
    label_ext _ _ currentGuards0 currentResets0
  have h1 : JudgementTableau.incoming F1 = waitL c d :=
    label_ext _ _ currentGuards1 currentResets1
  have h2 : JudgementTableau.incoming F2 = endL d :=
    label_ext _ _ currentGuards2 currentResets2
  refine ⟨h0 ▸ local_init,h1 ▸ local_edge01,h2 ▸ local_edge12,?_,?_,?_,local_final2⟩
  · intro i ht
    fin_cases i
    · change Local.terminal ∈ JudgementTableau.labels F0 at ht
      simp [labels0] at ht
    · change Local.terminal ∈ JudgementTableau.labels F1 at ht
      simp [labels1] at ht
    · change Local.terminal ∈ JudgementTableau.labels F2 at ht
      simp [labels2] at ht
  · intro i m hm
    fin_cases i
    · change Local.marker m ∈ JudgementTableau.labels F0 at hm
      simpa [labels0] using hm
    · change Local.marker m ∈ JudgementTableau.labels F1 at hm
      simpa [labels1] using hm
    · change Local.marker m ∈ JudgementTableau.labels F2 at hm
      simpa [labels2] using hm
  · intro i a ha
    fin_cases i
    · change Local.predicate (.plain (.atom a)) ∈ JudgementTableau.labels F0 at ha
      simp [labels0] at ha
    · change Local.predicate (.plain (.atom a)) ∈ JudgementTableau.labels F1 at ha
      have he : a = atom := by simpa [labels1,p] using ha
      subst a
      exact le_rfl
    · change Local.predicate (.plain (.atom a)) ∈ JudgementTableau.labels F2 at ha
      simp [labels2] at ha

theorem retimed_reaches :
    ((U).typedAutomaton ready 2).Reaches (signal U d) (U).goalModes :=
  reaches U ready admitted

def underlying : FiniteSignal Unit := ⟨2,by norm_num,fun _ _ => 0⟩
theorem projects_zero : (U).TypedProjectsTo (signal U d) underlying :=
  ⟨rfl,fun t _ _ x => original_constant U t x⟩

theorem underlying_well_behaved : SignalAtomRightContinuous underlying root := by
  intro a _ t
  change ContinuousWithinAt (fun _ : underlying.Time => a.function (fun _ => (0 : ℝ)))
    (Set.Ici t) t
  exact continuousWithinAt_const

/-- The original signal is recognized on the horizon partition. The retimed
execution projects to that signal and reaches a goal mode. -/
theorem equality_witness :
    SignalAtomRightContinuous underlying root ∧
    (U).recognizes JudgementTableau.labels_finite underlying
      (EqualityTiming.horizonPartition underlying rfl) ∧
    F1 ∉ (U).final ∧
    (U).TypedProjectsTo (signal U d) underlying ∧
    ((U).typedAutomaton ready 2).Reaches (signal U d) (U).goalModes := by
  refine ⟨underlying_well_behaved,⟨π,actual_path.1,actual_path.2,?_⟩,
    local_not_final1,projects_zero,retimed_reaches⟩
  exact actual_horizon underlying rfl (fun _ => le_rfl)

theorem no_final_jump_at_two {a b : ((U).typedAutomaton ready 2).State}
    (hcg : a.val.2 (.inl (U).globalClock) = 2) (hb : b.val.1.val = F2) :
    ¬ ((U).typedAutomaton ready 2).DiscreteStep a b := by
  intro hj
  have ht := (U).typed_horizon_jump_target ready 2 hj hcg
  change Local.terminal ∈ JudgementTableau.labels b.val.1.val at ht
  simp [hb,labels2] at ht

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``retimed_reaches, ``equality_witness, ``projects_zero, ``no_final_jump_at_two] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do throwError "{name} uses unapproved axiom {ax}"

end
end STLTableau.Section4.Finiteness.EqualityAudit

namespace STLTableau.Section4.Tableau.EndRegression
open Section3 Retimed
variable {Var State : Type*} (T : Tableau ℕ Var State)
noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
def bounds (i : Fin 4) : ℝ := if i.val = 0 then 0 else if i.val = 1 then 1 else 2
def dt : Fin 3 → NNReal := ![1,1,0]
private theorem diff (i : Fin 3) : (dt i : ℝ) = bounds i.succ - bounds i.castSucc := by
  fin_cases i <;> norm_num [bounds,dt,Fin.succ]

def value (d : ℕ) (i : Fin 3) (u : ℝ) : T.TypedVar → ℝ
  | .inl (.inl _) => 0
  | .inl (.inr (.inl k)) => bounds i.castSucc + u - (if k.val = d ∧ i.val ≠ 0 then 1 else 0)
  | .inl (.inr (.inr _)) => bounds i.castSucc + u
  | .inr false => u
  | .inr true => 1

def signal (d : ℕ) : FiniteSignal T.TypedVar :=
  ⟨2,by norm_num,fun t => if t.val < 1 then value T d 0 t.val else value T d 1 (t.val-1)⟩

variable {c d : ℕ} {q : Fin 3 → T.states} (h : T.TranslationReady) (g : Admitted T c d q)
local notation "H" => (T.endPositionAutomaton h 2)
include g
private theorem inv (i : Fin 3) (u : ℝ) (hu : 0 ≤ u ∧ u ≤ dt i) :
    ((q i),value T d i u) ∈ (H).invariant := by
  refine ⟨Or.inr rfl,?_,?_,?_⟩
  · intro _
    change bounds i.castSucc + u ≤ 2
    fin_cases i <;> norm_num [bounds,dt] at hu ⊢ <;> linarith
  · intro a ha
    exact (T.atomHolds_iff _ _ (fun _ => 0) (h.atom_variables _ (q i).property a ha)
      (fun _ => rfl)).mpr (g.atoms i a ha)
  · intro m hm
    exact ⟨fun _ => rfl,fun _ => g.mark i m hm⟩

private def st (i : Fin 3) (u : Set.Icc (0 : ℝ) (dt i)) : (H).State :=
  ⟨⟨q i,value T d i u.val⟩,inv T h g i u.val u.property⟩

private theorem flowing (i : Fin 3) :
    (H).ContinuousStep (st T h g i ⟨0,by simp⟩) (st T h g i ⟨dt i,by simp⟩)
      (dt i) (fun u => value T d i u.val) := by
  refine ⟨rfl,rfl,rfl,fun u => ⟨⟨?_,?_,?_,rfl⟩,inv T h g _ _ u.property⟩⟩
  · intro k
    simp only [st,value,add_zero]
    change (bounds i.castSucc + u.val - _) = (bounds i.castSucc - _) + u.val
    ring
  · change bounds i.castSucc + u.val = (bounds i.castSucc + 0) + u.val
    ring
  · change u.val = 0 + u.val
    ring

private theorem initial : (st T h g 0 ⟨0,by simp⟩).val ∈ (H).initial := by
  refine ⟨initL c,g.init,(fun _ => 0),fun k hk => hk.elim,?_,rfl,rfl⟩
  funext k
  cases k with
  | inl x => rfl
  | inr k =>
    cases k with
    | inr z => norm_num [old,value,globalClock,initialReset,bounds,st]
    | inl k =>
      by_cases hk : k.val = c <;>
        norm_num [old,value,initialReset,reset,initL,ClockResetSet.singleton,st,bounds,hk] <;> rfl

private theorem jump01 :
    (H).DiscreteStep (st T h g 0 ⟨dt 0,by simp⟩) (st T h g 1 ⟨0,by simp⟩) := by
  refine ⟨⟨(q 0,waitL c d,q 1),g.first⟩,rfl,rfl,rfl,rfl,?_,?_,?_,rfl,?_,?_,?_⟩
  · intro j hj
    have hj' := Set.mem_singleton_iff.mp hj
    subst j
    refine ⟨h.edge_guards _ g.first _ (Set.mem_singleton _),?_⟩
    norm_num [st,old,value,bounds,dt,realComparison]
  · intro k
    by_cases hk : k.val = d <;>
      norm_num [st,old,value,reset,waitL,ClockResetSet.singleton,hk,bounds,dt] <;> rfl
  · norm_num [st,value,globalClock,dt,bounds]
  · exact Or.inl ⟨by norm_num [st,value,globalClock,bounds],g.ordinary 1⟩
  · intro hz
    norm_num [st,value,dwell,dt] at hz
  · intro hz
    norm_num [st,value,bit] at hz

private theorem jump12 (endGoal : T.EndGoal (q 2)) :
    (H).DiscreteStep (st T h g 1 ⟨dt 1,by simp⟩) (st T h g 2 ⟨0,by simp⟩) := by
  refine ⟨⟨(q 1,endL d,q 2),g.second⟩,rfl,rfl,rfl,rfl,?_,?_,?_,rfl,?_,?_,?_⟩
  · intro j hj
    have hj' := Set.mem_singleton_iff.mp hj
    subst j
    refine ⟨h.edge_guards _ g.second _ (Set.mem_singleton _),?_⟩
    norm_num [st,old,value,bounds,dt,realComparison]
  · intro k
    by_cases hk : k.val = d <;>
      norm_num [st,old,value,reset,endL,ClockResetSet.empty,hk,bounds,dt] <;> rfl
  · norm_num [st,value,globalClock,dt,bounds]
  · exact Or.inr ⟨by norm_num [st,value,globalClock,bounds],by norm_num [st,value,dwell,dt],endGoal⟩
  · intro hz
    norm_num [st,value,dwell,dt] at hz
  · intro hz
    norm_num [st,value,bit] at hz


def execution (endGoal : T.EndGoal (q 2)) : (H).Execution (signal T d) where
  count := 2
  nonempty := by decide
  initialState := st T h g 0 ⟨0,by simp⟩
  initial_mem := initial T h g
  initial_signal_eq := by simp [signal, value, st, bounds]
  start := fun i => st T h g i.castSucc ⟨0,by simp⟩
  finish := fun i => st T h g i.castSucc ⟨dt i.castSucc,by simp⟩
  boundary := fun i => bounds i.castSucc
  first_zero := rfl
  increasing := by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num [bounds] at *
  last_le_horizon := by norm_num [bounds,signal]
  duration := fun i => dt i.castSucc
  duration_eq := fun i => diff i.castSucc
  curve := fun i t => value T d i.castSucc t.val
  continuousStep := fun i => flowing T h g i.castSucc
  initialSteps := .refl
  discreteSteps := by
    intro i hi
    fin_cases i
    · exact .single (jump01 T h g)
    · norm_num at hi
  finalState := st T h g 2 ⟨0,by simp⟩
  finalSteps := Relation.ReflTransGen.single (jump12 T h g endGoal)
  final_signal_eq := by intro t ht; have := t.property.2; norm_num [signal,bounds] at *; linarith
  signal_eq := by
    intro i t ht positive
    fin_cases i <;> norm_num [bounds] at ht ⊢
    · simp only [signal,if_pos ht.2]
    · simp only [signal,if_neg (not_lt.mpr ht.1)]

omit g in
theorem original_constant (t : (signal T d).Time) (x : T.realVariables) :
    (signal T d).value t (.inl (.inl x)) = 0 := by simp [signal,value]; split <;> rfl

end
end STLTableau.Section4.Tableau.EndRegression

namespace STLTableau.Section4.Finiteness.EqualityAudit
open Section3
noncomputable section
local notation "U" => (localClosureGraph (Clock := Nat) (Set.univ : Set Unit) input)
local notation "H" => (Tableau.endPositionAutomaton U ready 2)

theorem markerOnlyEndGoal : (U).EndGoal (modes 2) := by
  refine ⟨local_final2,?_⟩
  intro l hl
  change l ∈ JudgementTableau.labels F2 at hl
  rw [label2] at hl
  exact Or.inr (Set.mem_singleton_iff.mp hl)

def originalExecution : (H).Execution (Tableau.EndRegression.signal U d) :=
  Tableau.EndRegression.execution U ready admitted markerOnlyEndGoal

theorem original_schedule :
    originalExecution.count = 2 ∧
    originalExecution.boundary 0 = 0 ∧ originalExecution.boundary 1 = 1 ∧
    originalExecution.boundary 2 = 2 ∧ originalExecution.duration ⟨0,by decide +kernel⟩ = 1 ∧
    originalExecution.duration ⟨1,by decide +kernel⟩ = 1 ∧
    originalExecution.finalState.val.1.val = F2 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem originalEndClock (hc : d ∈ (U).clocks) :
    (originalExecution.finish ⟨1,by decide +kernel⟩).val.2 (.inl (.inr (.inl ⟨d,hc⟩))) = 1 := by
  change (Tableau.EndRegression.value U d 1 1) (.inl (.inr (.inl ⟨d,hc⟩))) = 1
  norm_num [Tableau.EndRegression.value,Tableau.EndRegression.bounds]

theorem originalEndClockMember : d ∈ (U).clocks :=
  ready.edge_guards _ admitted.second _ (Set.mem_singleton _)

theorem originalEndJump :
    (H).DiscreteStep (originalExecution.finish ⟨1,by decide +kernel⟩) originalExecution.finalState :=
  Tableau.EndRegression.jump12 U ready admitted markerOnlyEndGoal

theorem originalEndTiming :
    (originalExecution.finish ⟨1,by decide +kernel⟩).val.2
        (.inl (.inr (.inl ⟨d,originalEndClockMember⟩))) = 1 ∧
    (originalExecution.finish ⟨1,by decide +kernel⟩).val.2 (U).dwell = 1 ∧
    originalExecution.finalState.val.2 (.inl (U).globalClock) = 2 ∧
    originalExecution.finalState.val.2 (U).dwell = 0 :=
  by
    refine ⟨originalEndClock _,rfl,?_,rfl⟩
    change (Tableau.EndRegression.bounds (2 : Fin 3).castSucc + 0) = 2
    norm_num [Tableau.EndRegression.bounds]

theorem original_reaches :
    (H).Reaches (Tableau.EndRegression.signal U d) (U).goalModes := ⟨originalExecution,local_final2⟩

theorem original_projects :
    (U).TypedProjectsTo (Tableau.EndRegression.signal U d) underlying :=
  ⟨rfl,fun t _ _ x => Tableau.EndRegression.original_constant U t x⟩

run_elab do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for n in #[``original_schedule,``originalEndJump,``originalEndTiming,``original_reaches,``original_projects] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do throwError "{n} uses unexpected axiom {ax}"
end
end STLTableau.Section4.Finiteness.EqualityAudit

namespace STLTableau.Section4.Finiteness.EqualityAudit
open Section3
local notation "U" => (localClosureGraph (Clock := Nat) (Set.univ : Set Unit) input)

/-- The generated run on the early partition reaches a goal in a
flow-ending execution. -/
theorem actual_prelim_forward :
    ∃ aug, (U).TypedProjectsTo aug underlying ∧
      ((U).prelimAutomaton ready 2).PrelimReaches aug (U).goalModes := by
  refine local_prelim_forward_of_interval_run (Set.univ : Set Unit) input ready underlying
    underlying_well_behaved ?_ (EqualityTiming.earlyPartition underlying rfl) π
    actual_path.1 actual_path.2 (actual_early underlying rfl (fun _ => le_rfl)) ?_
  · intro a ha
    change Formula.IsSubformula (.atom a) root at ha
    cases ha with
    | until_left h => cases h
    | until_right h => cases h; rfl
  · change 3 ≤ 3
    decide

run_elab do
  for ax in ← Lean.collectAxioms ``actual_prelim_forward do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "unexpected axiom {ax}"
end STLTableau.Section4.Finiteness.EqualityAudit

/- CurrentStateGoalRegression -/
namespace STLTableau.Section4.Finiteness.EqualityAudit
open Section3
local notation "U" => (withEmptyContinuation (Clock := Nat) (Set.univ : Set Unit) input)

theorem unfiltered_ready : (U).TranslationReady :=
  withEmptyContinuation_ready (Set.univ : Set Unit) input
    (finiteRootTableau_translationReady (Set.univ : Set Unit) Set.finite_univ input.val
      (fun _ _ => Set.mem_univ _))

theorem unfiltered_actual_path : π.run U ∧ π.accepting U :=
  ⟨((Subgraph.run_iff _ _ π).mp actual_path.1).1,
    ((Subgraph.accepting_iff _ _ π).mp actual_path.2).1⟩

/-- The run on the horizon partition reaches the alternative state goal
using a horizon certificate. -/
theorem actual_horizon_prelim_stateGoal_forward :
    ∃ aug, (U).TypedProjectsTo aug underlying ∧
      ((U).prelimAutomaton unfiltered_ready 2).PrelimReachesState aug
        ((U).prelimGoal unfiltered_ready 2) := by
  refine empty_prelim_stateGoal_forward (Set.univ : Set Unit) input unfiltered_ready underlying
    underlying_well_behaved ?_ (EqualityTiming.horizonPartition underlying rfl) ?_
  · intro a ha
    change Formula.IsSubformula (.atom a) root at ha
    cases ha with
    | until_left h => cases h
    | until_right h => cases h; rfl
  · exact ⟨π, unfiltered_actual_path.1, unfiltered_actual_path.2,
      actual_horizon underlying rfl (fun _ => le_rfl)⟩

/-- The state-goal construction also applies to the early partition. -/
theorem actual_early_prelim_stateGoal_forward :
    ∃ aug, (U).TypedProjectsTo aug underlying ∧
      ((U).prelimAutomaton unfiltered_ready 2).PrelimReachesState aug
        ((U).prelimGoal unfiltered_ready 2) := by
  refine empty_prelim_stateGoal_forward (Set.univ : Set Unit) input unfiltered_ready underlying
    underlying_well_behaved ?_ (EqualityTiming.earlyPartition underlying rfl) ?_
  · intro a ha
    change Formula.IsSubformula (.atom a) root at ha
    cases ha with
    | until_left h => cases h
    | until_right h => cases h; rfl
  · exact ⟨π, unfiltered_actual_path.1, unfiltered_actual_path.2,
      actual_early underlying rfl (fun _ => le_rfl)⟩

run_elab do
  for n in #[``unfiltered_ready, ``unfiltered_actual_path,
      ``actual_horizon_prelim_stateGoal_forward,
      ``actual_early_prelim_stateGoal_forward] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{n} uses unexpected axiom {ax}"
end STLTableau.Section4.Finiteness.EqualityAudit
