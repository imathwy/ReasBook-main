module

public import Topology_Munkres_2000.Book.Exercise_24_1
public import Topology_Munkres_2000.Book.Theorem_62_1
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

/- Exercise 59.3 (1): For `n > 1`, Euclidean `1`-space is not homeomorphic to
Euclidean `n`-space. -/
#check euclideanSpaceNotHomeomorphicReal

/-- Helper for Exercise 59.3: extend a Euclidean vector by zero in all later coordinates. -/
noncomputable def euclideanZeroExtend {m n : ℕ} (_h : m ≤ n) :
    EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) :=
  fun x ↦ WithLp.toLp 2 (fun i ↦ if hi : i.val < m then x ⟨i.val, hi⟩ else 0)

/-- Helper for Exercise 59.3: zero extension is continuous. -/
lemma continuous_euclideanZeroExtend {m n : ℕ} (h : m ≤ n) :
    Continuous (euclideanZeroExtend h) := by
  -- Pass to the ordinary product topology and check continuity coordinatewise.
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).comp
  apply continuous_pi
  intro i
  by_cases hi : i.val < m
  · simpa [euclideanZeroExtend, hi] using
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin m ↦ ℝ) ⟨i.val, hi⟩ :
        Continuous fun x : EuclideanSpace ℝ (Fin m) ↦ x ⟨i.val, hi⟩)
  · simpa [euclideanZeroExtend, hi] using
      (continuous_const : Continuous fun _ : EuclideanSpace ℝ (Fin m) ↦ (0 : ℝ))

/-- Helper for Exercise 59.3: zero extension preserves all original coordinates. -/
lemma injective_euclideanZeroExtend {m n : ℕ} (h : m ≤ n) :
    Function.Injective (euclideanZeroExtend h) := by
  -- Equality after extension can be read back on each coordinate below `m`.
  intro x y hxy
  ext i
  have hi := congrArg
    (fun z : EuclideanSpace ℝ (Fin n) ↦ z ⟨i.val, lt_of_lt_of_le i.isLt h⟩) hxy
  simpa [euclideanZeroExtend, i.isLt] using hi

/-- Helper for Exercise 59.3: a proper zero-extended coordinate subspace is not open. -/
lemma not_isOpen_range_euclideanZeroExtend {m n : ℕ} (h : m < n) :
    ¬ IsOpen (Set.range (euclideanZeroExtend h.le)) := by
  -- An open neighborhood of zero would contain a small vector in the first omitted direction.
  intro hopen
  have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ Set.range (euclideanZeroExtend h.le) := by
    refine ⟨0, ?_⟩
    ext i
    simp [euclideanZeroExtend]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  let j : Fin n := ⟨m, h⟩
  let y : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j (ε / 2)
  have hyball : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε := by
    rw [Metric.mem_ball, dist_zero_right, PiLp.norm_single 2 (fun _ : Fin n ↦ ℝ), Real.norm_eq_abs]
    rw [abs_of_pos (half_pos hε)]
    linarith
  obtain ⟨x, hx⟩ := hball hyball
  have hcoord := congrArg (fun z : EuclideanSpace ℝ (Fin n) ↦ z j) hx
  -- Zero extension vanishes at `j`, while the perturbation has positive `j`-coordinate.
  simp [euclideanZeroExtend, j, y] at hcoord
  exact (ne_of_gt (half_pos hε)) hcoord.symm

/-- Helper for Exercise 59.3: a continuous injective Euclidean self-map has open range. -/
lemma isOpen_range_of_continuous_injective_euclidean {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf_continuous : Continuous f) (hf_injective : Function.Injective f) :
    IsOpen (Set.range f) := by
  -- Apply invariance of domain to the same map with domain presented as `Set.univ`.
  let fU : ↥(Set.univ : Set (EuclideanSpace ℝ (Fin n))) → EuclideanSpace ℝ (Fin n) :=
    fun x ↦ f x
  have hfU_continuous : Continuous fU := by
    simpa [fU, Function.comp_def] using hf_continuous.comp continuous_subtype_val
  have hfU_injective : Function.Injective fU := by
    intro x y hxy
    apply Subtype.ext
    exact hf_injective hxy
  have hopen := (invarianceOfDomain isOpen_univ fU hfU_continuous hfU_injective).isOpen_range
  have hrange : Set.range fU = Set.range f := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨⟨x, Set.mem_univ x⟩, ?_⟩
      rfl
  rwa [hrange] at hopen

/-- Helper for Exercise 59.3: lower-dimensional Euclidean space is not homeomorphic to a
higher-dimensional one. -/
lemma euclideanSpacesNotHomeomorphicOfLt {m n : ℕ} (h : m < n) :
    ¬ Nonempty (EuclideanSpace ℝ (Fin m) ≃ₜ EuclideanSpace ℝ (Fin n)) := by
  -- Transport zero extension across a hypothetical homeomorphism to get a self-map of `ℝⁿ`.
  rintro ⟨e⟩
  let f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    euclideanZeroExtend h.le ∘ e.symm
  have hf_continuous : Continuous f :=
    (continuous_euclideanZeroExtend h.le).comp e.symm.continuous
  have hf_injective : Function.Injective f :=
    (injective_euclideanZeroExtend h.le).comp e.symm.injective
  have hopen : IsOpen (Set.range f) :=
    isOpen_range_of_continuous_injective_euclidean f hf_continuous hf_injective
  have hrange : Set.range f = Set.range (euclideanZeroExtend h.le) := by
    ext y
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨e.symm x, hx⟩
    · rintro ⟨x, rfl⟩
      refine ⟨e x, ?_⟩
      simp [f]
  rw [hrange] at hopen
  exact not_isOpen_range_euclideanZeroExtend h hopen

/-- Exercise 59.3 (2): For `n > 2`, Euclidean `2`-space is not homeomorphic to
Euclidean `n`-space. -/
theorem planeNotHomeomorphicEuclideanSpace (n : ℕ) (h : 2 < n) :
    ¬ Nonempty (EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin n)) := by
  -- The strict-dimension obstruction applies directly with lower dimension two.
  exact euclideanSpacesNotHomeomorphicOfLt h

/-- The general fact noted after Exercise 59.3: Euclidean spaces of unequal finite
dimensions are not homeomorphic. -/
theorem euclideanSpacesNotHomeomorphicOfNe (m n : ℕ) (h : m ≠ n) :
    ¬ Nonempty (EuclideanSpace ℝ (Fin m) ≃ₜ EuclideanSpace ℝ (Fin n)) := by
  -- Order the two dimensions and reverse a hypothetical homeomorphism when necessary.
  rcases lt_or_gt_of_ne h with hmn | hnm
  · exact euclideanSpacesNotHomeomorphicOfLt hmn
  · rintro ⟨e⟩
    exact euclideanSpacesNotHomeomorphicOfLt hnm ⟨e.symm⟩
