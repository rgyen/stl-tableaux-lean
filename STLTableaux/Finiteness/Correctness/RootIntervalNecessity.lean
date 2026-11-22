import STLTableaux.Automata.Translation.NormalizedInputTranslation

/-! Recognition on a fixed partition requires the root on the entire first
piece, not just at time zero. No stability premise is needed. -/
namespace STLTableau.Section4.Finiteness
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

theorem finiteRootTableau_root_on_first_interval
    (X : Set Var) (root : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain)
    (hs : (finiteRootTableau (Clock := Clock) X root).recognizes
      JudgementTableau.labels_finite σ P) :
    ∀ t : σ.Time, t.val ∈ P.interval ⟨0, Generated.partition_size_pos σ P⟩ →
      σ.Satisfies root t := by
  have hrec := Subgraph.recognizes_lift _ _ JudgementTableau.labels_finite σ P hs
  obtain ⟨p, hr, ha, htrace⟩ := hrec
  let α : ClockValuation Clock := fun _ => 0
  have hi : (Section3.StateForm.ofLocal (.predicate (.plain root))).EvaluatedNumeric
      σ P α ⟨0, by omega⟩ := by
    intro l hl
    have he : l = .predicate (.plain root) := hl
    subst l
    intro hk
    trivial
  have hroot := (derives_fullTrace_and_root X _ _ p hr ha σ P α
    ⟨0, by omega⟩ hi (htrace α)).2.2
  have hplain := hroot.2 (.predicate (.plain root)) (by simp [Section3.StateForm.ofLocal])
  change (if h : 0 < P.size then _ else False) at hplain
  simp only [dif_pos (Generated.partition_size_pos σ P)] at hplain
  exact hplain

theorem finiteRootTableau_root_everywhere_of_one_piece
    (X : Set Var) (root : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (hsize : P.size = 1)
    (hs : (finiteRootTableau (Clock := Clock) X root).recognizes
      JudgementTableau.labels_finite σ P) : ∀ t : σ.Time, σ.Satisfies root t := by
  intro t
  have ht : t.val ∈ σ.domain := t.property
  rw [← P.covers] at ht
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ht
  have he : i = ⟨0, Generated.partition_size_pos σ P⟩ := by
    apply Fin.ext
    have := i.isLt
    omega
  subst i
  exact finiteRootTableau_root_on_first_interval X root σ P hs t hi

end STLTableau.Section4.Finiteness
