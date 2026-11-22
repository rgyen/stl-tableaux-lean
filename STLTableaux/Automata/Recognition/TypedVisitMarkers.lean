import STLTableaux.Automata.Recognition.TypedVisitSequence
import STLTableaux.Automata.Recognition.TypedResidencePartition

namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
variable (h : T.TranslationReady) (τ : ℝ)
local notation "V" => TimedVisit T h τ
local notation "𝓗" => (T.typedAutomaton h τ)

/-- Boundary markers of an actual visit sequence, including its right sentinel. -/
inductive VisitMarks (T : Tableau Clock Var State) (h : T.TranslationReady) (τ : ℝ) :
    Marker → List (TimedVisit T h τ) → Marker → Prop where
  | nil (m) : VisitMarks T h τ m [] m
  | snoc {m w n xs} (v : TimedVisit T h τ) (pre : VisitMarks T h τ m xs w)
      (left : T.visitMarker h τ v.state = w)
      (point : v.left = v.right → w = ● ∧ n = ○) :
      VisitMarks T h τ m (xs ++ [v]) n

theorem beforeFlow_marks {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ)
    {i xs} (hp : BeforeFlow T h τ e i xs) :
    VisitMarks T h τ ● xs (T.visitMarker h τ (e.start i)) := by
  induction hp with
  | initial same =>
    rw [← same, T.execution_first_closed h τ e]
    exact .nil _
  | initialJump step =>
    obtain ⟨_, _, _, _, _, hz, _⟩ := e.initial_mem
    have hm := T.zero_jump_markers h τ step hz
    exact .snoc _ (.nil _) hm.1 (fun _ => ⟨rfl, hm.2⟩)
  | @direct i j xs hn pre step ih =>
    exact .snoc _ ih rfl (fun he => (e.increasing Fin.castSucc_lt_succ).ne he |>.elim)
  | @viaPoint i j xs hn pre s enter leave ih =>
    have hm := T.zero_jump_markers h τ leave (T.typed_jump_dwell_zero h τ enter)
    have hp : VisitMarks T h τ ●
        (xs ++ [⟨e.start i,e.boundary i.castSucc,e.boundary i.succ⟩])
        (T.visitMarker h τ s) :=
      .snoc _ ih rfl (fun he => (e.increasing Fin.castSucc_lt_succ).ne he |>.elim)
    simpa only [List.append_assoc, List.singleton_append] using
      (VisitMarks.snoc (n := T.visitMarker h τ (e.start j))
        (⟨s,e.boundary i.succ,e.boundary i.succ⟩ : V) hp rfl (fun _ => hm))

theorem ordinary_cut_times_marks {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ)
    (i : Fin e.count) (t : ℝ) (ht : e.boundary i.castSucc < t) (he : t ≤ e.boundary i.succ)
    (hg : (e.start i).val.1 ∈ T.goalModes) (ho : (e.start i).val.1 ∉ T.terminalModes) :
    ∃ xs, BeforeFlow T h τ e i xs ∧
      let vs := xs ++ [⟨e.start i,e.boundary i.castSucc,t⟩]
      VisitTimes T h τ vs t ∧ VisitMarks T h τ ● vs ● := by
  obtain ⟨xs,hp,hv⟩ := T.exists_ordinary_cut_visits h τ e i t ht he hg ho
  exact ⟨xs,hp,hv,.snoc _ (T.beforeFlow_marks h τ e hp) rfl (fun eq => (ht.ne eq).elim)⟩

private def readAt {A B : Type*} (f : A → B) (xs : List A) (z : B) (k : ℕ) : B :=
  (xs[k]?.map f).getD z

private theorem read_snoc {A B : Type*} (f : A → B) (xs : List A) (v : A)
    (z : B) (k : ℕ) (hk : k ≤ xs.length) :
    readAt f (xs ++ [v]) z k = readAt f xs (f v) k := by
  rcases lt_or_eq_of_le hk with hl | rfl
  · simp [readAt,List.getElem?_append_left hl,List.getElem?_eq_getElem hl]
  · simp [readAt]

private structure Indexed {A B : Type*} (f : A → B) (test : A → B → Prop)
    (s : B) (xs : List A) (z : B) : Prop where
  first : readAt f xs z 0 = s
  step : ∀ k (hk : k < xs.length), test xs[k] (readAt f xs z (k+1))

private theorem indexedNil {A B : Type*} (f : A → B) (test : A → B → Prop) (s : B) :
    Indexed f test s [] s := ⟨rfl, by simp⟩

private theorem indexedSnoc {A B : Type*} {f : A → B} {test : A → B → Prop}
    {s z : B} {xs : List A} {v : A} (hp : Indexed f test s xs (f v)) (hv : test v z) :
    Indexed f test s (xs ++ [v]) z := by
  constructor
  · exact (read_snoc f xs v z 0 (Nat.zero_le _)).trans hp.first
  · intro k hk
    by_cases hi : k < xs.length
    · rw [List.getElem_append_left hi,read_snoc _ _ _ _ _ (by omega)]
      exact hp.step k hi
    · have he : k = xs.length := by simp at hk; omega
      subst k
      simpa [List.getElem_append_right,readAt,List.getElem?_eq_none] using hv

private theorem timeIndex {xs t} (hp : VisitTimes T h τ xs t) :
    Indexed (fun v : V => v.left) (fun v n => v.left ≤ v.right ∧ v.right = n) 0 xs t := by
  induction hp with
  | nil => exact indexedNil _ _ _
  | snoc _ _ hab ih => exact indexedSnoc ih ⟨hab,rfl⟩

private theorem markIndex {xs s z} (hp : VisitMarks T h τ s xs z) :
    Indexed (fun v : V => T.visitMarker h τ v.state)
      (fun v n => v.left = v.right → T.visitMarker h τ v.state = ● ∧ n = ○) s xs z := by
  induction hp with
  | nil => exact indexedNil _ _ _
  | snoc v _ hl hz ih => exact indexedSnoc (hl ▸ ih) (hl ▸ hz)

/-- Realize the very same visits as a partition, with their original
indices, times, and type bits. The last right endpoint is open. -/
theorem visitPartition {xs : List V} {t : ℝ} (ht : VisitTimes T h τ xs t)
    (hm : VisitMarks T h τ ● xs ●) :
    ∃ (P : IntervalPartition (Set.Ico 0 t)) (hn : P.size = xs.length),
      ∀ i : Fin xs.length, (P.interval ⟨i.val,hn.symm ▸ i.isLt⟩) =
        ⟨xs[i.val].left,xs[i.val].right,T.visitMarker h τ xs[i.val].state,
          (readAt (fun v : V => T.visitMarker h τ v.state) xs ● (i.val+1)).complement⟩ := by
  let b (k : Fin (xs.length+1)) := readAt (fun v : V => v.left) xs t k.val
  let m (k : Fin (xs.length+1)) := readAt (fun v : V => T.visitMarker h τ v.state) xs ● k.val
  have ti := T.timeIndex h τ ht
  have mi := T.markIndex h τ hm
  have bl (i : Fin xs.length) : b i.castSucc = xs[i.val].left := by
    simp [b,readAt]
  have ml (i : Fin xs.length) : m i.castSucc = T.visitMarker h τ xs[i.val].state := by
    simp [m,readAt]
  have br (i : Fin xs.length) : b i.succ = xs[i.val].right := (ti.step i.val i.isLt).2.symm
  have mono : Monotone b := Fin.monotone_iff_le_succ.2 (fun i => by
    rw [bl,br]; exact (ti.step i.val i.isLt).1)
  have hz : IntervalPartition.SingletonCompatible b m := by
    intro i he
    change m i.castSucc = ● ∧ m i.succ = ○
    change b i.castSucc = b i.succ at he
    rw [bl,br] at he
    rw [ml]
    exact mi.step i.val i.isLt he
  have mlast : m (Fin.last xs.length) = ● := by simp [m,readAt]
  let Q := IntervalPartition.ofSingletonBoundaries b mono m hz mi.first mlast
  have hl : b 0 = 0 := ti.first
  have hr : b (Fin.last xs.length) = t := by simp [b,readAt]
  let P : IntervalPartition (Set.Ico 0 t) :=
    { Q with covers := Q.covers.trans (congrArg₂ Set.Ico hl hr) }
  refine ⟨P,rfl,?_⟩
  intro i
  change (⟨b i.castSucc,b i.succ,m i.castSucc,(m i.succ).complement⟩ : MarkedInterval) = _
  rw [bl,br,ml]
  rfl

theorem ordinary_cut_partition {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ)
    (i : Fin e.count) (t : ℝ) (ht : e.boundary i.castSucc < t) (he : t ≤ e.boundary i.succ)
    (hg : (e.start i).val.1 ∈ T.goalModes) (ho : (e.start i).val.1 ∉ T.terminalModes) :
    ∃ xs, BeforeFlow T h τ e i xs ∧
      let vs := xs ++ [⟨e.start i,e.boundary i.castSucc,t⟩]
      ∃ (P : IntervalPartition (Set.Ico 0 t)) (hn : P.size = vs.length),
        ∀ j : Fin vs.length, (P.interval ⟨j.val,hn.symm ▸ j.isLt⟩) =
          ⟨vs[j.val].left,vs[j.val].right,T.visitMarker h τ vs[j.val].state,
            (readAt (fun v : V => T.visitMarker h τ v.state) vs ● (j.val+1)).complement⟩ := by
  obtain ⟨xs,hp,hts,hms⟩ := T.ordinary_cut_times_marks h τ e i t ht he hg ho
  exact ⟨xs,hp,T.visitPartition h τ hts hms⟩

end STLTableau.Section4.Tableau
