import STLTableaux.Automata.Recognition.TypedTerminalPartition

namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
variable (h : T.TranslationReady) (τ : ℝ)
local notation "𝓗" => (T.typedAutomaton h τ)
local notation "V" => TimedVisit T h τ
variable {σ : FiniteSignal T.TypedVar}

def VisitAtoms (σ : FiniteSignal T.TypedVar) (v : V) (next : Marker) : Prop :=
  ∀ t : σ.Time, v.left ≤ t.val →
    (t.val = v.left → T.visitMarker h τ v.state = ●) →
    (t.val < v.right ∨ (t.val = v.right ∧ next = ○)) →
      T.atomsAt v.state.val.1 (σ.value t)

theorem flowInteriorAtoms (e : (𝓗).Execution σ) (i : Fin e.count) (t : σ.Time)
    (ht : e.boundary i.castSucc ≤ t.val ∧ t.val < e.boundary i.succ)
    (owned : t.val = e.boundary i.castSucc → T.visitMarker h τ (e.start i) = ●) :
    T.atomsAt (e.start i).val.1 (σ.value t) := by
  by_cases positive : 0 < t.val
  · rw [e.signal_eq i t ht positive]
    exact (((e.continuousStep i).2.2.2 _).2).2.2.1
  · have zero : t.val = 0 := le_antisymm (le_of_not_gt positive) t.property.1
    have boundary : e.boundary i.castSucc = 0 := by
      have lower := e.increasing.monotone (Fin.zero_le i.castSucc)
      have first : e.boundary 0 = 0 := e.first_zero
      rw [first] at lower
      linarith [ht.1]
    have index : i = ⟨0, e.nonempty⟩ := by
      apply Fin.ext
      change i.val = 0
      have equal : i.castSucc = (0 : Fin (e.count + 1)) :=
        e.increasing.injective (boundary.trans e.first_zero.symm)
      simpa using congrArg Fin.val equal
    have closed := owned (zero.trans boundary.symm)
    subst i
    have same : e.initialState = e.start ⟨0, e.nonempty⟩ := by
      rcases T.typed_initial_visits h τ e with same | jump
      · exact same
      · obtain ⟨_, _, _, _, _, hz, _⟩ := e.initial_mem
        have markers := T.zero_jump_markers h τ jump hz
        have impossible : (● : Marker) = ○ := closed.symm.trans markers.2
        cases impossible
    have time : t = ⟨0, le_rfl, σ.horizon_pos⟩ := Subtype.ext zero
    rw [time, e.initial_signal_eq, same]
    exact (e.start ⟨0, e.nonempty⟩).property.2.2.1

private theorem pointAtoms (e : (𝓗).Execution σ) (i : Fin e.count) (a : (𝓗).State)
    (hj : (𝓗).DiscreteStep a (e.start i))
    (initial : i.val = 0 → a = e.initialState) :
    T.VisitAtoms h τ σ ⟨a,e.boundary i.castSucc,e.boundary i.castSucc⟩
      (T.visitMarker h τ (e.start i)) := by
  intro t hl _ hr
  rcases hr with hlt | ⟨he,ho⟩
  · exact (not_lt_of_ge hl hlt).elim
  · have eq : t = e.startTime i := Subtype.ext he
    rw [eq]
    by_cases positive : 0 < (e.startTime i).val
    · exact T.typed_open_entry_source_atoms h τ e i hj ho positive
    · have boundary : e.boundary i.castSucc = 0 := by
        have lower := e.increasing.monotone (Fin.zero_le i.castSucc)
        have first : e.boundary 0 = 0 := e.first_zero
        rw [first] at lower
        exact le_antisymm (le_of_not_gt positive) lower
      have index : i.val = 0 := by
        have same : i.castSucc = (0 : Fin (e.count + 1)) :=
          e.increasing.injective (boundary.trans e.first_zero.symm)
        simpa using congrArg Fin.val same
      have time : e.startTime i = ⟨0, le_rfl, σ.horizon_pos⟩ := Subtype.ext boundary
      rw [time, e.initial_signal_eq, initial index]
      exact e.initialState.property.2.2.1

/-- Each visit is checked using the marker of its actual successor. -/
inductive AtomSeq (T : Tableau Clock Var State) (h : T.TranslationReady) (τ : ℝ)
    (σ : FiniteSignal T.TypedVar) : List (TimedVisit T h τ) → Marker → Prop where
  | nil m : AtomSeq T h τ σ [] m
  | snoc {xs m} (v : TimedVisit T h τ)
      (pre : AtomSeq T h τ σ xs (T.visitMarker h τ v.state))
      (hv : T.VisitAtoms h τ σ v m) : AtomSeq T h τ σ (xs ++ [v]) m

theorem beforeFlow_atoms (e : (𝓗).Execution σ) {i xs} (hp : BeforeFlow T h τ e i xs) :
    AtomSeq T h τ σ xs (T.visitMarker h τ (e.start i)) := by
  induction hp with
  | initial => exact .nil _
  | initialJump hj =>
    apply AtomSeq.snoc _ (.nil _)
    have hz : e.boundary 0 = 0 := e.first_zero
    simpa [hz, Fin.castSucc_mk] using
      T.pointAtoms h τ e ⟨0,e.nonempty⟩ e.initialState hj (fun _ => rfl)
  | @direct i j xs hn pre step ih =>
    apply AtomSeq.snoc _ ih
    intro t hl owned hr
    rcases hr with hi | ⟨he,ho⟩
    · exact T.flowInteriorAtoms h τ e i t ⟨hl,hi⟩ owned
    · have hb : i.succ = j.castSucc := Fin.ext hn
      have eq : t = e.startTime j := Subtype.ext (he.trans (congrArg e.boundary hb))
      rw [eq, (e.continuousStep i).1]
      have positive : 0 < (e.startTime j).val := by
        have pos := e.increasing (show (0 : Fin (e.count + 1)) < j.castSucc by
          change 0 < j.val; omega)
        have first : e.boundary 0 = 0 := e.first_zero
        change 0 < e.boundary j.castSucc
        rw [← first]
        exact pos
      exact T.typed_open_entry_source_atoms h τ e j step ho positive
  | @viaPoint i j xs hn pre s enter leave ih =>
    have hm := T.zero_jump_markers h τ leave (T.typed_jump_dwell_zero h τ enter)
    have preAtoms : AtomSeq T h τ σ
        (xs ++ [⟨e.start i,e.boundary i.castSucc,e.boundary i.succ⟩]) (T.visitMarker h τ s) := by
      apply AtomSeq.snoc _ ih
      intro t hl owned hr
      rcases hr with hi | ⟨_,ho⟩
      · exact T.flowInteriorAtoms h τ e i t ⟨hl,hi⟩ owned
      · exact Marker.noConfusion (hm.1.symm.trans ho)
    have hb : i.succ = j.castSucc := Fin.ext hn
    have hs := T.pointAtoms h τ e j s leave (fun zero => by omega)
    rw [← hb] at hs
    simpa only [List.append_assoc,List.singleton_append] using AtomSeq.snoc _ preAtoms hs

/-- Last observed piece ends open, whether at an early cut or at τ. -/
theorem cut_visit_atoms (e : (𝓗).Execution σ) {i xs} (hp : BeforeFlow T h τ e i xs)
    {cut : ℝ} (hc : cut ≤ e.boundary i.succ) :
    AtomSeq T h τ σ (xs ++ [⟨e.start i,e.boundary i.castSucc,cut⟩]) ● := by
  apply AtomSeq.snoc _ (T.beforeFlow_atoms h τ e hp)
  intro t hl owned hr
  rcases hr with hi | ⟨_,ho⟩
  · exact T.flowInteriorAtoms h τ e i t ⟨hl,hi.trans_le hc⟩ owned
  · exact Marker.noConfusion ho

private noncomputable def nextBit (xs : List V) (z : Marker) (k : ℕ) : Marker :=
  (xs[k]?.map (fun v => T.visitMarker h τ v.state)).getD z

private theorem seq_at {xs z} (hs : AtomSeq T h τ σ xs z) :
    ∀ k (hk : k < xs.length), T.VisitAtoms h τ σ xs[k] (T.nextBit h τ xs z (k+1)) := by
  induction hs with
  | nil => simp
  | @snoc xs z v pre hv ih =>
    intro k hk
    by_cases hi : k < xs.length
    · rw [List.getElem_append_left hi]
      have hn : T.nextBit h τ (xs ++ [v]) z (k+1) =
          T.nextBit h τ xs (T.visitMarker h τ v.state) (k+1) := by
        rcases lt_or_eq_of_le (Nat.succ_le_of_lt hi) with hl | he
        · simp [nextBit,List.getElem?_append_left hl,List.getElem?_eq_getElem hl]
        · change k+1 = xs.length at he
          simp [nextBit,he]
      rw [hn]
      exact ih k hi
    · have he : k = xs.length := by simp at hk; omega
      subst k
      simpa [nextBit,List.getElem_append_right,List.getElem?_eq_none] using hv

/-- On the partition built from these visits, every owned signal time
satisfies every numerical atom of the corresponding visited mode. -/
theorem cut_partition_atoms (e : (𝓗).Execution σ) {i xs} (hp : BeforeFlow T h τ e i xs)
    {cut : ℝ} (hl : e.boundary i.castSucc < cut) (hr : cut ≤ e.boundary i.succ) :
    let vs := xs ++ [⟨e.start i,e.boundary i.castSucc,cut⟩]
    ∃ (P : IntervalPartition (Set.Ico 0 cut)) (hn : P.size = vs.length),
      ∀ j : Fin vs.length, let J := P.interval ⟨j.val,hn.symm ▸ j.isLt⟩
        J.left = vs[j.val].left ∧ J.right = vs[j.val].right ∧
        J.leftBoundary = T.visitMarker h τ vs[j.val].state ∧
        ∀ t : σ.Time, t.val ∈ J → T.atomsAt vs[j.val].state.val.1 (σ.value t) := by
  let vs := xs ++ [⟨e.start i,e.boundary i.castSucc,cut⟩]
  have times : VisitTimes T h τ vs cut := .snoc (T.beforeFlow_times h τ e hp) _ hl.le
  have marks : VisitMarks T h τ ● vs ● :=
    .snoc _ (T.beforeFlow_marks h τ e hp) rfl (fun eq => (hl.ne eq).elim)
  obtain ⟨P,hn,hs⟩ := T.visitPartition h τ times marks
  have atoms := T.cut_visit_atoms h τ e hp hr
  refine ⟨P,hn,?_⟩
  intro j
  change (P.interval _).left = _ ∧ _
  rw [hs j]
  refine ⟨rfl,rfl,rfl,?_⟩
  intro t ht
  apply T.seq_at h τ atoms j.val j.isLt t (MarkedInterval.left_le_of_mem ht)
  · intro equal
    change (vs[j.val].left < t.val ∨
      vs[j.val].left = t.val ∧ (T.visitMarker h τ vs[j.val].state).Includes) ∧ _ at ht
    rcases ht.1 with strict | ⟨_, included⟩
    · exact (strict.ne equal.symm).elim
    · cases marker : T.visitMarker h τ vs[j.val].state <;> simp_all [Marker.Includes]
  · change _ ∧ (t.val < vs[j.val].right ∨
      t.val = vs[j.val].right ∧ (T.nextBit h τ vs ● (j.val+1)).complement.Includes) at ht
    rcases ht.2 with hlt | ⟨he,hinc⟩
    · exact Or.inl hlt
    · refine Or.inr ⟨he,?_⟩
      cases h : T.nextBit h τ vs ● (j.val+1) <;> simp_all [Marker.Includes]

end STLTableau.Section4.Tableau
