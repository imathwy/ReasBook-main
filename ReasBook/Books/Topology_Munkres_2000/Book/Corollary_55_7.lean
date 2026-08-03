module

public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Instances.Matrix
public import Topology_Munkres_2000.Book.Proposition_55_1.Triangle
public import Topology_Munkres_2000.Book.Theorem_55_6

public section

open Module.End

/-- Helper for Corollary 55.7: the standard triangle is convex. -/
private lemma convex_standardTriangle : Convex ℝ standardTriangle := by
  -- Each defining coordinate inequality is preserved by convex combinations.
  rw [convex_iff_segment_subset]
  intro x hx y hy
  rw [segment_subset_iff]
  intro a b ha hb hab
  rw [mem_standardTriangle] at hx hy ⊢
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  constructor
  · exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
  constructor
  · exact add_nonneg (mul_nonneg ha hx.2.1) (mul_nonneg hb hy.2.1)
  · nlinarith [mul_nonneg ha (sub_nonneg.mpr hx.2.2),
      mul_nonneg hb (sub_nonneg.mpr hy.2.2)]

/-- Helper for Corollary 55.7: the standard triangle is bounded. -/
private lemma isBounded_standardTriangle : Bornology.IsBounded standardTriangle := by
  -- All coordinates lie in the unit interval, so the triangle lies in a bounded box.
  rw [isBounded_iff_forall_norm_le]
  refine ⟨2, ?_⟩
  intro x hx
  rw [mem_standardTriangle] at hx
  rw [EuclideanSpace.norm_eq]
  have hx0 : x 0 ≤ 1 := by
    linarith [hx.2.2, hx.2.1]
  have hx1 : x 1 ≤ 1 := by
    linarith [hx.2.2, hx.1]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs]
  rw [abs_of_nonneg hx.1, abs_of_nonneg hx.2.1]
  rw [Real.sqrt_le_iff]
  constructor
  · norm_num
  · nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

/-- Helper for Corollary 55.7: the standard triangle has nonempty interior. -/
private lemma interior_standardTriangle_nonempty : (interior standardTriangle).Nonempty := by
  -- A small ball around `(1/4, 1/4)` remains strictly inside all three half-spaces.
  let c : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun _ ↦ 1 / 4)
  have hradius : 0 < (1 / 8 : ℝ) := by
    norm_num
  refine ⟨c, mem_interior_iff_mem_nhds.2 ?_⟩
  refine Filter.mem_of_superset (Metric.ball_mem_nhds c hradius) ?_
  intro x hx
  rw [Metric.mem_ball] at hx
  rw [mem_standardTriangle]
  have hcoord (i : Fin 2) : |x i - c i| < 1 / 8 := by
    rw [← Real.dist_eq]
    exact (PiLp.dist_apply_le x c i).trans_lt hx
  have h0 := hcoord 0
  have h1 := hcoord 1
  change |x 0 - 1 / 4| < 1 / 8 at h0
  change |x 1 - 1 / 4| < 1 / 8 at h1
  rw [abs_lt] at h0 h1
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- Helper for Corollary 55.7: there exists a homeomorphism from the standard triangle to the
closed unit disk. -/
private lemma standardTriangle_exists_homeomorph_closedUnitDisk :
    Nonempty (standardTriangle ≃ₜ B²) := by
  -- Restrict the ambient gauge-rescale homeomorphism to the two closed sets.
  obtain ⟨e, _, hclosure, _⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      convex_standardTriangle interior_standardTriangle_nonempty isBounded_standardTriangle
  have hclosed : IsClosed standardTriangle := by
    have htriangle : standardTriangle =
        {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1} := by
      ext x
      exact mem_standardTriangle x
    rw [htriangle]
    have hc0 : Continuous (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0) := by
      fun_prop
    have hc1 : Continuous (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 1) := by
      fun_prop
    exact (isClosed_le continuous_const hc0).inter
      ((isClosed_le continuous_const hc1).inter
        (isClosed_le (hc0.add hc1) continuous_const))
  rw [hclosed.closure_eq] at hclosure
  exact ⟨(e.image standardTriangle).trans (Homeomorph.setCongr hclosure)⟩

/-- Helper for Corollary 55.7: a chosen homeomorphism from the standard triangle to the closed
unit disk. -/
private noncomputable def standardTriangleHomeomorphClosedUnitDisk :
    standardTriangle ≃ₜ B² :=
  Classical.choice standardTriangle_exists_homeomorph_closedUnitDisk

/-- Helper for Corollary 55.7: every continuous self-map of the standard triangle has a fixed
point. -/
private lemma standardTriangle_exists_fixedPoint
    (f : standardTriangle → standardTriangle) (hf : Continuous f) :
    ∃ x, Function.IsFixedPt f x := by
  -- Conjugate the self-map to the disk and transport its fixed point back.
  let e := standardTriangleHomeomorphClosedUnitDisk
  let g : B² → B² := fun y ↦ e (f (e.symm y))
  have hg : Continuous g := by
    exact e.continuous.comp (hf.comp e.symm.continuous)
  obtain ⟨y, hy⟩ := closedUnitDisk_exists_fixedPoint g hg
  refine ⟨e.symm y, ?_⟩
  apply e.injective
  rw [e.apply_symm_apply]
  change e (f (e.symm y)) = y at hy
  exact hy

/-- Helper for Corollary 55.7: encode a point of the standard triangle as a three-coordinate
probability vector. -/
private noncomputable def triangleProbabilityVector (x : standardTriangle) : Fin 3 → ℝ :=
  ![x.1 0, x.1 1, 1 - x.1 0 - x.1 1]

/-- Helper for Corollary 55.7: every coordinate of the encoded probability vector is
nonnegative. -/
private lemma triangleProbabilityVector_nonneg (x : standardTriangle) (i : Fin 3) :
    0 ≤ triangleProbabilityVector x i := by
  -- The third coordinate is the unused slack in the triangle inequality.
  have hx := (mem_standardTriangle x.1).mp x.2
  fin_cases i
  · exact hx.1
  · exact hx.2.1
  · have hthird : 0 ≤ 1 - x.1 0 - x.1 1 := by
      linarith [hx.2.2]
    simpa [triangleProbabilityVector] using hthird

/-- Helper for Corollary 55.7: the encoded probability-vector coordinates sum to one. -/
private lemma triangleProbabilityVector_sum (x : standardTriangle) :
    ∑ i, triangleProbabilityVector x i = 1 := by
  -- The slack coordinate was chosen precisely to complete the sum to one.
  simp [triangleProbabilityVector, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]

/-- Helper for Corollary 55.7: the encoded probability vector is nonzero. -/
private lemma triangleProbabilityVector_ne_zero (x : standardTriangle) :
    triangleProbabilityVector x ≠ 0 := by
  -- A zero vector cannot have coordinate sum one.
  intro hx
  have hsum := triangleProbabilityVector_sum x
  rw [hx] at hsum
  simp at hsum

/-- Helper for Corollary 55.7: the coordinate sum of the positive-matrix image of an encoded
probability vector. -/
private noncomputable def positiveMatrixScale
    (A : Matrix (Fin 3) (Fin 3) ℝ) (x : standardTriangle) : ℝ :=
  ∑ i, A.mulVec (triangleProbabilityVector x) i

/-- Helper for Corollary 55.7: a strictly positive matrix has positive normalization scale on
the standard triangle. -/
private lemma positiveMatrixScale_pos (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ∀ i j, 0 < A i j) (x : standardTriangle) :
    0 < positiveMatrixScale A x := by
  -- Every output coordinate is positive because the input is nonnegative and has sum one.
  have hrow (i : Fin 3) : 0 < A.mulVec (triangleProbabilityVector x) i := by
    have hweighted : 0 < ∑ j, A i j * triangleProbabilityVector x j := by
      have hmin : 0 < min (A i 0) (min (A i 1) (A i 2)) := by
        exact lt_min (hA i 0) (lt_min (hA i 1) (hA i 2))
      have hle : min (A i 0) (min (A i 1) (A i 2)) ≤
          ∑ j, A i j * triangleProbabilityVector x j := by
        rw [Fin.sum_univ_three]
        have h0 := triangleProbabilityVector_nonneg x 0
        have h1 := triangleProbabilityVector_nonneg x 1
        have h2 := triangleProbabilityVector_nonneg x 2
        have hs := triangleProbabilityVector_sum x
        rw [Fin.sum_univ_three] at hs
        have ha0 : min (A i 0) (min (A i 1) (A i 2)) ≤ A i 0 := min_le_left _ _
        have ha1 : min (A i 0) (min (A i 1) (A i 2)) ≤ A i 1 :=
          (min_le_right _ _).trans (min_le_left _ _)
        have ha2 : min (A i 0) (min (A i 1) (A i 2)) ≤ A i 2 :=
          (min_le_right _ _).trans (min_le_right _ _)
        nlinarith [mul_le_mul_of_nonneg_right ha0 h0,
          mul_le_mul_of_nonneg_right ha1 h1, mul_le_mul_of_nonneg_right ha2 h2]
      exact hmin.trans_le hle
    exact hweighted
  unfold positiveMatrixScale
  exact Finset.sum_pos (fun i _ ↦ hrow i) Finset.univ_nonempty

/-- Helper for Corollary 55.7: the normalized positive-matrix action on the first two
coordinates lies in the standard triangle. -/
private lemma normalizedPositiveMatrixAction_mem (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ∀ i j, 0 < A i j) (x : standardTriangle) :
    WithLp.toLp 2 (fun i : Fin 2 ↦
      A.mulVec (triangleProbabilityVector x) i.castSucc / positiveMatrixScale A x) ∈
      standardTriangle := by
  -- Positivity gives the coordinate inequalities, and the omitted third coordinate gives slack.
  rw [mem_standardTriangle]
  have hs := positiveMatrixScale_pos A hA x
  have hrow (i : Fin 3) : 0 ≤ A.mulVec (triangleProbabilityVector x) i := by
    unfold Matrix.mulVec dotProduct
    exact Finset.sum_nonneg fun j _ ↦
      mul_nonneg (le_of_lt (hA i j)) (triangleProbabilityVector_nonneg x j)
  constructor
  · exact div_nonneg (hrow 0) hs.le
  constructor
  · exact div_nonneg (hrow 1) hs.le
  · unfold positiveMatrixScale
    rw [Fin.sum_univ_three]
    norm_num only [Fin.castSucc_zero, Fin.castSucc_one]
    rw [← add_div]
    have hscale :
        0 < A.mulVec (triangleProbabilityVector x) 0 +
          A.mulVec (triangleProbabilityVector x) 1 +
          A.mulVec (triangleProbabilityVector x) 2 := by
      simpa [positiveMatrixScale, Fin.sum_univ_three] using hs
    have hsum :
        A.mulVec (triangleProbabilityVector x) 0 +
          A.mulVec (triangleProbabilityVector x) 1 ≤
        A.mulVec (triangleProbabilityVector x) 0 +
          A.mulVec (triangleProbabilityVector x) 1 +
          A.mulVec (triangleProbabilityVector x) 2 := by
      linarith [hrow 2]
    exact (div_le_one hscale).mpr hsum

/-- Helper for Corollary 55.7: the normalized positive-matrix action is a self-map of the
standard triangle. -/
private noncomputable def normalizedPositiveMatrixAction
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : ∀ i j, 0 < A i j) :
    standardTriangle → standardTriangle :=
  fun x ↦ ⟨WithLp.toLp 2 (fun i : Fin 2 ↦
    A.mulVec (triangleProbabilityVector x) i.castSucc / positiveMatrixScale A x),
    normalizedPositiveMatrixAction_mem A hA x⟩

/-- Helper for Corollary 55.7: the probability-vector encoding varies continuously on the
standard triangle. -/
private lemma continuous_triangleProbabilityVector : Continuous triangleProbabilityVector := by
  -- Each of the three coordinates is an affine expression in the triangle coordinates.
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun x : standardTriangle ↦ x.1 0)
    fun_prop
  · change Continuous (fun x : standardTriangle ↦ x.1 1)
    fun_prop
  · change Continuous (fun x : standardTriangle ↦ 1 - x.1 0 - x.1 1)
    fun_prop

/-- Helper for Corollary 55.7: the normalization scale varies continuously on the standard
triangle. -/
private lemma continuous_positiveMatrixScale (A : Matrix (Fin 3) (Fin 3) ℝ) :
    Continuous (positiveMatrixScale A) := by
  -- Matrix-vector multiplication and the finite coordinate sum preserve continuity.
  unfold positiveMatrixScale
  apply continuous_finsetSum Finset.univ
  intro i _
  exact (continuous_apply i).comp
    (continuous_const.matrix_mulVec continuous_triangleProbabilityVector)

/-- Helper for Corollary 55.7: the normalized positive-matrix action is continuous. -/
private lemma continuous_normalizedPositiveMatrixAction (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ∀ i j, 0 < A i j) : Continuous (normalizedPositiveMatrixAction A hA) := by
  -- The positive scale keeps the coordinatewise quotient away from division by zero.
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
  apply continuous_pi
  intro i
  have hmul : Continuous (fun x : standardTriangle ↦
      A.mulVec (triangleProbabilityVector x) i.castSucc) :=
    (continuous_apply i.castSucc).comp
      (continuous_const.matrix_mulVec continuous_triangleProbabilityVector)
  exact hmul.div (continuous_positiveMatrixScale A)
    (fun x ↦ (positiveMatrixScale_pos A hA x).ne')

/-- Corollary 55.7. A `3 × 3` real matrix with strictly positive entries has a
strictly positive real eigenvalue. -/
theorem Matrix.exists_pos_eigenvalue_of_pos
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : ∀ i j, 0 < A i j) :
    ∃ μ : ℝ, 0 < μ ∧ HasEigenvalue A.toLin' μ := by
  -- Apply Brouwer to the normalized action on probability vectors.
  obtain ⟨x, hx⟩ := standardTriangle_exists_fixedPoint
    (normalizedPositiveMatrixAction A hA) (continuous_normalizedPositiveMatrixAction A hA)
  let v := triangleProbabilityVector x
  let μ := positiveMatrixScale A x
  have hμ : 0 < μ := positiveMatrixScale_pos A hA x
  have hfixed : (normalizedPositiveMatrixAction A hA x).1 = x.1 :=
    congrArg Subtype.val hx
  have hcoord (i : Fin 2) : A.mulVec v i.castSucc = μ * v i.castSucc := by
    have hi := congrFun (congrArg WithLp.ofLp hfixed) i
    fin_cases i
    · change A.mulVec v 0 / μ = v 0 at hi
      simpa [mul_comm] using (div_eq_iff hμ.ne').mp hi
    · change A.mulVec v 1 / μ = v 1 at hi
      simpa [mul_comm] using (div_eq_iff hμ.ne').mp hi
  have hthird : A.mulVec v 2 = μ * v 2 := by
    -- The preserved coordinate sum recovers the omitted third equation.
    have hscale : A.mulVec v 0 + A.mulVec v 1 + A.mulVec v 2 = μ := by
      simp [μ, positiveMatrixScale, Fin.sum_univ_three, v]
    have hvsum : v 0 + v 1 + v 2 = 1 := by
      simpa [Fin.sum_univ_three, v] using triangleProbabilityVector_sum x
    have h0 := hcoord 0
    have h1 := hcoord 1
    norm_num only [Fin.castSucc_zero, Fin.castSucc_one] at h0 h1
    nlinarith
  refine ⟨μ, hμ, ?_⟩
  -- Assemble the three coordinate identities into a nonzero eigenvector.
  have heigen_eq : Matrix.toLin' A v = μ • v := by
    rw [Matrix.toLin'_apply]
    funext i
    fin_cases i
    · simpa [smul_eq_mul] using hcoord 0
    · simpa [smul_eq_mul] using hcoord 1
    · simpa [smul_eq_mul] using hthird
  have hmem : v ∈ Module.End.eigenspace (Matrix.toLin' A) μ :=
    mem_eigenspace_iff.mpr heigen_eq
  have hvector : HasEigenvector A.toLin' μ v :=
    hasEigenvector_iff.mpr ⟨hmem, triangleProbabilityVector_ne_zero x⟩
  exact hasEigenvalue_of_hasEigenvector hvector
