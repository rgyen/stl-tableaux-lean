import STLTableaux.Semantics.Partitions.SingletonBoundaryPartition
import STLTableaux.Semantics.Partitions.BoundaryMarkerAssignment

/-! Marker choice for the raw half-open/singleton assignment.
The marker after a singleton is open; every other left marker is closed.
This is a geometric construction, not a reachability invariant. -/
namespace STLTableau.IntervalPartition

/-- Label requirements augmented only at singleton boundaries: a singleton
starts closed, and the next piece starts open. Positive pieces otherwise keep
the freedom to assign their shared point to either neighbour. -/
def singletonRequirements {n : ℕ} (b : Fin (n + 1) → ℝ)
    (required : Fin n → Set Marker) (i : Fin n) : Set Marker :=
  {m | m ∈ required i ∨
    (m = ● ∧ b ⟨i.val, by omega⟩ = b ⟨i.val + 1, by omega⟩) ∨
    (m = ○ ∧ ∃ j : Fin n, j.val + 1 = i.val ∧
      b ⟨j.val, by omega⟩ = b ⟨j.val + 1, by omega⟩)}

/-- At the initial boundary there is no preceding singleton. Thus an open
requirement can only come from the first label itself. -/
@[simp] theorem open_mem_singletonRequirements_first_iff {n : ℕ} (hn : 0 < n)
    (b : Fin (n + 1) → ℝ) (required : Fin n → Set Marker) :
    ○ ∈ singletonRequirements b required ⟨0, hn⟩ ↔ ○ ∈ required ⟨0, hn⟩ := by
  constructor
  · rintro (hm | ⟨he, _⟩ | ⟨_, j, hj, _⟩)
    · exact hm
    · cases he
    · change j.val + 1 = 0 at hj
      omega
  · exact Or.inl

/-- Construct markers from local requirements, without requiring the canonical
half-open choice. The hypotheses are local compatibility checks, not a claim
that every automaton execution satisfies them. -/
theorem exists_markers_of_singleton_requirements {n : ℕ} (hn : 0 < n)
    (b : Fin (n + 1) → ℝ) (required : Fin n → Set Marker)
    (hfirst : ○ ∉ singletonRequirements b required ⟨0, hn⟩)
    (hconsistent : ∀ i, ¬ (○ ∈ singletonRequirements b required i ∧
      ● ∈ singletonRequirements b required i))
    (hlast : ∀ i : Fin n, i.val + 1 = n →
      b ⟨i.val, by omega⟩ ≠ b ⟨i.val + 1, by omega⟩) :
    ∃ m : Fin (n + 1) → Marker,
      m ⟨0, by omega⟩ = ● ∧ m ⟨n, by omega⟩ = ● ∧
      SingletonCompatible b m ∧
      ∀ i mark, mark ∈ required i → m ⟨i.val, by omega⟩ = mark := by
  obtain ⟨m, hm0, hmn, hm⟩ :=
    (exists_boundaryMarkers_iff hn (singletonRequirements b required)).mpr
      ⟨hfirst, hconsistent⟩
  refine ⟨m, hm0, hmn, ?_, fun i mark hmark => hm i mark (Or.inl hmark)⟩
  intro i he
  refine ⟨hm i ● (Or.inr (Or.inl ⟨rfl, he⟩)), ?_⟩
  have hi : i.val + 1 < n := by
    have := i.isLt
    by_contra hh
    exact hlast i (by omega) he
  exact hm ⟨i.val + 1, hi⟩ ○ (Or.inr (Or.inr ⟨rfl, i, rfl, he⟩))

noncomputable def singletonMarkers {n : ℕ} (b : Fin (n + 1) → ℝ)
    (j : Fin (n + 1)) : Marker :=
  if hj : 0 < j.val then
    if b ⟨j.val - 1, by omega⟩ = b j then ○ else ●
  else ●

@[simp] theorem singletonMarkers_first {n : ℕ} (b : Fin (n + 1) → ℝ) :
    singletonMarkers b ⟨0, by omega⟩ = ● := by simp [singletonMarkers]

theorem singletonMarkers_succ {n : ℕ} (b : Fin (n + 1) → ℝ) (i : Fin n) :
    singletonMarkers b ⟨i.val + 1, by omega⟩ =
      if b ⟨i.val, by omega⟩ = b ⟨i.val + 1, by omega⟩ then ○ else ● := by
  simp [singletonMarkers]

/-- Adjacent zero-width pieces cannot both own the same point. -/
def IsolatedSingletons {n : ℕ} (b : Fin (n + 1) → ℝ) : Prop :=
  ∀ (i : Fin n) (hi : i.val + 1 < n),
    b ⟨i.val, by omega⟩ = b ⟨i.val + 1, by omega⟩ →
    b ⟨i.val + 1, by omega⟩ ≠ b ⟨i.val + 2, by omega⟩

theorem singletonMarkers_compatible {n : ℕ} (b : Fin (n + 1) → ℝ)
    (hisolated : IsolatedSingletons b) : SingletonCompatible b (singletonMarkers b) := by
  intro i hi
  constructor
  · by_cases hipos : 0 < i.val
    · have hprev : b ⟨i.val - 1, by omega⟩ ≠ b ⟨i.val, by omega⟩ := by
        intro he
        let j : Fin n := ⟨i.val - 1, by omega⟩
        have hj : j.val + 1 = i.val := by dsimp [j]; omega
        have hbad := hisolated j (by omega)
        have hidx : (⟨j.val + 1, by omega⟩ : Fin (n + 1)) = ⟨i.val, by omega⟩ := Fin.ext hj
        have hidx' : (⟨j.val + 2, by omega⟩ : Fin (n + 1)) =
            ⟨i.val + 1, by omega⟩ := Fin.ext (by change j.val + 2 = i.val + 1; omega)
        rw [hidx, hidx'] at hbad
        exact hbad he hi
      simp [singletonMarkers, hipos, hprev]
    · have hz : i.val = 0 := by omega
      simp [singletonMarkers, hz]
  · rw [singletonMarkers_succ, if_pos hi]

theorem singletonMarkers_right {n : ℕ} (b : Fin (n + 1) → ℝ) (i : Fin n)
    (hi : b ⟨i.val, by omega⟩ ≠ b ⟨i.val + 1, by omega⟩) :
    singletonMarkers b ⟨i.val + 1, by omega⟩ = ● := by
  rw [singletonMarkers_succ, if_neg hi]

/-- The last boundary is excluded from the prefix domain. Its singleton, if
observed at an early stop, is appended separately by `appendPointSuffix`. -/
theorem singletonMarkers_last {n : ℕ} (b : Fin (n + 1) → ℝ)
    (hlast : ∀ i : Fin n, i.val + 1 = n →
      b ⟨i.val, by omega⟩ ≠ b ⟨i.val + 1, by omega⟩) :
    singletonMarkers b ⟨n, by omega⟩ = ● := by
  by_cases hn : n = 0
  · subst n
    exact singletonMarkers_first b
  · let i : Fin n := ⟨n - 1, by omega⟩
    have he : i.val + 1 = n := by dsimp [i]; omega
    have hidx : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := Fin.ext he
    rw [← hidx]
    exact singletonMarkers_right b i (hlast i he)

/-- Under the subset-of-raw convention the markers are uniquely determined
by the boundary times, rather than freely chosen proof witnesses. -/
theorem singletonMarkers_unique {n : ℕ} (b : Fin (n + 1) → ℝ)
    (m : Fin (n + 1) → Marker) (hfirst : m ⟨0, by omega⟩ = ●)
    (hz : SingletonCompatible b m)
    (hright : ∀ i : Fin n, b ⟨i.val, by omega⟩ ≠ b ⟨i.val + 1, by omega⟩ →
      m ⟨i.val + 1, by omega⟩ = ●) : m = singletonMarkers b := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact hfirst.trans (singletonMarkers_first b).symm
  · rw [show i.succ = (⟨i.val + 1, by omega⟩ : Fin (n + 1)) from rfl,
      singletonMarkers_succ]
    split_ifs with hi
    · exact (hz i hi).2
    · exact hright i hi

/-- Construct the partition without accepting a marker-array witness. Label
agreement is still checked separately against these determined markers. -/
noncomputable def ofIsolatedSingletons {n : ℕ} (b : Fin (n + 1) → ℝ)
    (hb : Monotone b) (hisolated : IsolatedSingletons b)
    (hlast : ∀ i : Fin n, i.val + 1 = n →
      b ⟨i.val, by omega⟩ ≠ b ⟨i.val + 1, by omega⟩) :
    IntervalPartition (Set.Ico (b ⟨0, by omega⟩) (b ⟨n, by omega⟩)) :=
  ofSingletonBoundaries b hb (singletonMarkers b) (singletonMarkers_compatible b hisolated)
    (singletonMarkers_first b) (singletonMarkers_last b hlast)

/-- Exact feasibility, including label-marker requirements. This identifies
the geometric and label obligations that path selection must discharge. -/
theorem exists_singletonMarkers_iff {n : ℕ} (b : Fin (n + 1) → ℝ)
    (required : Fin n → Set Marker) :
    (∃ m : Fin (n + 1) → Marker,
      m ⟨0, by omega⟩ = ● ∧ m ⟨n, by omega⟩ = ● ∧
      SingletonCompatible b m ∧
      (∀ i : Fin n, b ⟨i.val, by omega⟩ ≠ b ⟨i.val + 1, by omega⟩ →
        m ⟨i.val + 1, by omega⟩ = ●) ∧
      ∀ i mark, mark ∈ required i → m ⟨i.val, by omega⟩ = mark) ↔
    IsolatedSingletons b ∧
      (∀ i : Fin n, i.val + 1 = n →
        b ⟨i.val, by omega⟩ ≠ b ⟨i.val + 1, by omega⟩) ∧
      (∀ i mark, mark ∈ required i → singletonMarkers b ⟨i.val, by omega⟩ = mark) := by
  constructor
  · rintro ⟨m, hfirst, hlast, hz, hright, hreq⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i hi he he'
      have hopen := (hz i he).2
      have hclosed := (hz ⟨i.val + 1, hi⟩ he').1
      rw [hopen] at hclosed
      cases hclosed
    · intro i hi he
      have hopen := (hz i he).2
      have hidx : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := Fin.ext hi
      rw [hidx, hlast] at hopen
      cases hopen
    · rw [← singletonMarkers_unique b m hfirst hz hright]
      exact hreq
  · rintro ⟨hisolated, hlast, hreq⟩
    exact ⟨singletonMarkers b, singletonMarkers_first b, singletonMarkers_last b hlast,
      singletonMarkers_compatible b hisolated, singletonMarkers_right b, hreq⟩

end STLTableau.IntervalPartition
