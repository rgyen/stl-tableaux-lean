import STLTableaux.Finiteness.Derivation.Selection.SelectedPathOrigins
import STLTableaux.Finiteness.Derivation.Branches.RawBranchUpperShape

/-! Traces the left clock of each clocked branch to the input or to a timed
opening in the same derivation. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

def ClockedLeft (p : Predicate Clock Var) (c : Clock)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) : Prop :=
  (∃m,p=.upper c m kind I φ) ∨ (∃d m r,p=.bounded c d m r kind I φ)

def incomingClockedLeft (L : List (Local Clock Var)) (c : Clock)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) : Prop :=
  ∃p,Local.predicate p∈L ∧ClockedLeft p c kind I φ

def ledgerOpeningLeft (L : List (RawLedgerEntry (Clock := Clock) (Var := Var)))
    (c : Clock) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) : Prop :=
  ∃e∈L,∃m,e.source=.plain (timedFormula kind I φ) ∧
    Predicate.upper c m kind I φ∈e.body.currentPredicates

private theorem opening_cons {L : List (RawLedgerEntry (Clock := Clock) (Var := Var))}
    (a : RawLedgerEntry (Clock := Clock) (Var := Var))
    {c : Clock} {kind : TemporalKind} {I : TimeInterval} {φ : Formula Var}
    (h : ledgerOpeningLeft L c kind I φ) : ledgerOpeningLeft (a::L) c kind I φ := by
  obtain ⟨e,he,m,hs,hp⟩ := h
  exact ⟨e,List.mem_cons_of_mem _ he,m,hs,hp⟩

private theorem ordinary_left
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (choice : OrdinaryChoice E owned)
    (c : Clock) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (h : incomingClockedLeft choice.child.locals c kind I φ) :
    incomingClockedLeft owned.locals c kind I φ ∨
      ledgerOpeningLeft [⟨choice.p,choice.B,choice.branch⟩] c kind I φ := by
  obtain ⟨q,hq,hqLeft⟩ := h
  rcases (ordinary_child_current owned choice q).1 hq with hnew | hold
  · rcases hqLeft with ⟨m,rfl⟩ | ⟨d,m,r,rfl⟩
    · have ho := choice.branch.current_upper_opening c m kind I φ hnew
      exact Or.inr ⟨⟨choice.p,choice.B,choice.branch⟩,by simp,m,ho.1,hnew⟩
    · exact False.elim (choice.branch.no_current_bounded c d m r kind I φ hnew)
  · exact Or.inl ⟨q,ordinary_rest_subset owned choice hold,hqLeft⟩

private theorem boundary_left
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) {required : Bool} (choice : BoundaryChoice E owned required)
    (c : Clock) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (h : incomingClockedLeft choice.child.locals c kind I φ) :
    incomingClockedLeft owned.locals c kind I φ := by
  obtain ⟨q,hq,hqLeft⟩ := h
  rcases (boundary_child_current owned choice q).1 hq with hupper | hold
  · subst q
    rcases hqLeft with ⟨m,he⟩ | ⟨d,m,r,he⟩
    · have heq := Predicate.upper.inj he
      rcases heq with ⟨hc,_,hk,hI,hφ⟩
      subst c; subst kind; subst I; subst φ
      refine ⟨.bounded choice.c choice.d choice.m (Marker.complement choice.ell) choice.kind choice.I choice.phi,?_,Or.inr ?_⟩
      · rw [choice.split]; simp
      · exact ⟨choice.d,choice.m,Marker.complement choice.ell,rfl⟩
    · cases he
  · exact ⟨q,boundary_rest_subset owned choice hold,hqLeft⟩

/-- Every actual clocked ledger event has either an incoming left owner or an
actual timed opening in this SAME selected ledger, preserving the full family. -/
theorem SelectedTree.clocked_ledger_left_origin
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    (e : RawLedgerEntry (Clock := Clock) (Var := Var)) (he : e∈T.rawLedger)
    (c : Clock) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hc : ClockedLeft e.source c kind I φ) :
    incomingClockedLeft owned.locals c kind I φ ∨ ledgerOpeningLeft T.rawLedger c kind I φ := by
  induction T with
  | zero => cases he
  | ordinary owned choice tail ih =>
    rcases List.mem_cons.mp he with rfl | ht
    · exact Or.inl ⟨choice.p,by rw [choice.split];simp,hc⟩
    · rcases ih ht with hold | hopen
      · rcases ordinary_left owned choice c kind I φ hold with hold | hopen
        · exact Or.inl hold
        · obtain ⟨a,ha,m,hs,hp⟩ := hopen
          have heq : a=⟨choice.p,choice.B,choice.branch⟩ := by simpa using ha
          subst a
          exact Or.inr ⟨_,by simp [SelectedTree.rawLedger],m,hs,hp⟩
      · exact Or.inr (opening_cons _ hopen)
  | required owned choice tail ih =>
    rcases ih he with hold | hopen
    · exact Or.inl (boundary_left owned choice c kind I φ hold)
    · exact Or.inr hopen
  | optional owned choice upper forced tail ih =>
    rcases List.mem_cons.mp he with rfl | ht
    · exact Or.inl (boundary_left owned choice c kind I φ ⟨upper.p,by rw [upper.split];simp,hc⟩)
    · rcases ih ht with hold | hopen
      · rcases ordinary_left choice.child upper c kind I φ hold with hold | hopen
        · exact Or.inl (boundary_left owned choice c kind I φ hold)
        · obtain ⟨a,ha,m,hs,hp⟩ := hopen
          have heq : a=⟨upper.p,upper.B,upper.branch⟩ := by simpa using ha
          subst a
          exact Or.inr ⟨_,by simp [SelectedTree.rawLedger],m,hs,hp⟩
      · exact Or.inr (opening_cons _ hopen)

def incomingUpperLeft (L : List (Local Clock Var)) (c : Clock)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) : Prop :=
  ∃m,Local.predicate (.upper c m kind I φ)∈L

def boundaryConsumedLeft (L : List (Predicate Clock Var×Bool)) (c : Clock)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) : Prop :=
  ∃p b,(p,b)∈L ∧ClockedLeft p c kind I φ

private theorem ordinary_upper_left
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (choice : OrdinaryChoice E owned)
    (c : Clock) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (h : incomingUpperLeft choice.child.locals c kind I φ) :
    incomingUpperLeft owned.locals c kind I φ ∨ledgerOpeningLeft [⟨choice.p,choice.B,choice.branch⟩] c kind I φ := by
  obtain ⟨m,hm⟩ := h
  rcases (ordinary_child_current owned choice _).1 hm with hnew | hold
  · exact Or.inr ⟨⟨choice.p,choice.B,choice.branch⟩,by simp,m,(choice.branch.current_upper_opening c m kind I φ hnew).1,hnew⟩
  · exact Or.inl ⟨m,ordinary_rest_subset owned choice hold⟩

private theorem boundary_upper_left
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) {required : Bool} (choice : BoundaryChoice E owned required)
    (c : Clock) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (h : incomingUpperLeft choice.child.locals c kind I φ) :
    incomingUpperLeft owned.locals c kind I φ ∨
      boundaryConsumedLeft [(.bounded choice.c choice.d choice.m (Marker.complement choice.ell) choice.kind choice.I choice.phi,required)] c kind I φ := by
  obtain ⟨m,hm⟩ := h
  rcases (boundary_child_current owned choice _).1 hm with he | hold
  · obtain ⟨rfl,_,rfl,rfl,rfl⟩ := Predicate.upper.inj he
    exact Or.inr ⟨_,required,by simp,Or.inr ⟨choice.d,choice.m,Marker.complement choice.ell,rfl⟩⟩
  · exact Or.inl ⟨m,boundary_rest_subset owned choice hold⟩

omit [DecidableEq Clock] in
private theorem boundary_cons {L : List (Predicate Clock Var×Bool)}
    (a : Predicate Clock Var×Bool) {c : Clock} {kind : TemporalKind} {I : TimeInterval} {φ : Formula Var}
    (h : boundaryConsumedLeft L c kind I φ) : boundaryConsumedLeft (a::L) c kind I φ := by
  obtain ⟨p,b,hp,hc⟩ := h
  exact ⟨p,b,List.mem_cons_of_mem _ hp,hc⟩

/-- Upper events arise from an actual opening, an actual boundary replacement,
or an upper already present in the given input. -/
theorem SelectedTree.upper_ledger_left_trace
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    (e : RawLedgerEntry (Clock := Clock) (Var := Var)) (he : e∈T.rawLedger)
    (c : Clock) (m : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hs : e.source=.upper c m kind I φ) :
    incomingUpperLeft owned.locals c kind I φ ∨ledgerOpeningLeft T.rawLedger c kind I φ ∨
      boundaryConsumedLeft T.boundaryConsumed c kind I φ := by
  induction T with
  | zero => cases he
  | ordinary owned choice tail ih =>
    rcases List.mem_cons.mp he with rfl | ht
    · exact Or.inl ⟨m,by
        have hs' : choice.p=.upper c m kind I φ := hs
        rw [choice.split,hs'];simp⟩
    · rcases ih ht with hold | hopen | hbound
      · rcases ordinary_upper_left owned choice c kind I φ hold with hold | hopen
        · exact Or.inl hold
        · obtain ⟨a,ha,b,hp,hq⟩ := hopen
          have heq : a=⟨choice.p,choice.B,choice.branch⟩ := by simpa using ha
          subst a
          exact Or.inr (Or.inl ⟨_,by simp [SelectedTree.rawLedger],b,hp,hq⟩)
      · exact Or.inr (Or.inl (opening_cons _ hopen))
      · exact Or.inr (Or.inr hbound)
  | required owned choice tail ih =>
    rcases ih he with hold | hopen | hbound
    · rcases boundary_upper_left owned choice c kind I φ hold with hold | hbound
      · exact Or.inl hold
      · obtain ⟨p,b,hp,hc⟩ := hbound
        have heq : (p,b)=(.bounded choice.c choice.d choice.m (Marker.complement choice.ell) choice.kind choice.I choice.phi,true) := by simpa using hp
        exact Or.inr (Or.inr ⟨p,b,List.mem_cons.mpr (Or.inl heq),hc⟩)
    · exact Or.inr (Or.inl hopen)
    · exact Or.inr (Or.inr (boundary_cons _ hbound))
  | optional owned choice upper forced tail ih =>
    have liftBoundary : incomingUpperLeft choice.child.locals c kind I φ →
        incomingUpperLeft owned.locals c kind I φ ∨boundaryConsumedLeft
          (SelectedTree.optional owned choice upper forced tail).boundaryConsumed c kind I φ := by
      intro h
      rcases boundary_upper_left owned choice c kind I φ h with hold | hbound
      · exact Or.inl hold
      · obtain ⟨p,b,hp,hc⟩ := hbound
        have heq : (p,b)=(.bounded choice.c choice.d choice.m (Marker.complement choice.ell) choice.kind choice.I choice.phi,false) := by simpa using hp
        exact Or.inr ⟨p,b,List.mem_cons.mpr (Or.inl heq),hc⟩
    rcases List.mem_cons.mp he with rfl | ht
    · rcases liftBoundary ⟨m,by
        have hs' : upper.p=.upper c m kind I φ := hs
        rw [upper.split,hs'];simp⟩ with hold | hbound
      · exact Or.inl hold
      · exact Or.inr (Or.inr hbound)
    · rcases ih ht with hold | hopen | hbound
      · rcases ordinary_upper_left choice.child upper c kind I φ hold with hold | hopen
        · rcases liftBoundary hold with hold | hbound
          · exact Or.inl hold
          · exact Or.inr (Or.inr hbound)
        · obtain ⟨a,ha,b,hp,hq⟩ := hopen
          have heq : a=⟨upper.p,upper.B,upper.branch⟩ := by simpa using ha
          subst a
          exact Or.inr (Or.inl ⟨_,by simp [SelectedTree.rawLedger],b,hp,hq⟩)
      · exact Or.inr (Or.inl (opening_cons _ hopen))
      · exact Or.inr (Or.inr (boundary_cons _ hbound))

/-- The left clock of a predicate in the `↑` form comes from an eligible
input predicate in the `↑↓` form or an opening branch. -/
theorem SelectedTree.upper_ledger_left_origin
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}
    {N : Section3.StateForm Clock Var} (O : InputOrigins σ P α k N)
    {J : MixedJ Clock Var} {W : Set Clock} {owned : OwnedPending J N.resets W}
    {H Er : MixedJ Clock Var} (T : SelectedTree O.eligible O.strictClocks owned H Er)
    (hLocal : ∀l,l∈owned.locals↔l∈N.locals)
    (e : RawLedgerEntry (Clock := Clock) (Var := Var)) (he : e∈T.rawLedger)
    (c : Clock) (m : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hs : e.source=.upper c m kind I φ) :
    (∃d b r,Local.predicate (.bounded c d b r kind I φ)∈N.locals ∧
      Predicate.bounded c d b r kind I φ∈O.eligible) ∨
      ledgerOpeningLeft T.rawLedger c kind I φ := by
  rcases T.upper_ledger_left_trace e he c m kind I φ hs with hold | hopen | hbound
  · obtain ⟨b,hb⟩ := hold
    exact False.elim (O.no_upper c b kind I φ ((hLocal _).1 hb))
  · exact Or.inr hopen
  · obtain ⟨p,b,hp,hc⟩ := hbound
    obtain ⟨hb,hE,hin⟩ := T.boundary_consumed_origin hp
    rcases hc with ⟨a,rfl⟩ | ⟨d,a,r,rfl⟩
    · cases hb
    · exact Or.inl ⟨d,a,r,(hLocal _).1 hin,hE⟩

end STLTableau.Section4.Finiteness
