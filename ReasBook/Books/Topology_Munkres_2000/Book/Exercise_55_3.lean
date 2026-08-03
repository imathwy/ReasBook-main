module

public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.Convex.GaugeRescale
public import Topology_Munkres_2000.Book.Proposition_55_1.Triangle
public import Topology_Munkres_2000.Book.Theorem_55_6

public section

open Module.End

/-- Helper for Exercise 55.3: the standard triangle is convex. -/
lemma convex_standardTriangle : Convex ℝ standardTriangle := by
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

/-- Helper for Exercise 55.3: the standard triangle is bounded. -/
lemma isBounded_standardTriangle : Bornology.IsBounded standardTriangle := by
  -- All coordinates lie in the unit interval, so the triangle lies in a bounded box.
  rw [isBounded_iff_forall_norm_le]
  refine ⟨2, ?_⟩
  intro x hx
  rw [mem_standardTriangle] at hx
  rw [EuclideanSpace.norm_eq]
  have hx0 : x 0 ≤ 1 := by linarith [hx.2.2, hx.2.1]
  have hx1 : x 1 ≤ 1 := by linarith [hx.2.2, hx.1]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs]
  rw [abs_of_nonneg hx.1, abs_of_nonneg hx.2.1]
  rw [Real.sqrt_le_iff]
  constructor
  · norm_num
  · nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

/-- Helper for Exercise 55.3: the standard triangle has nonempty interior. -/
lemma interior_standardTriangle_nonempty : (interior standardTriangle).Nonempty := by
  -- A small ball around `(1/4, 1/4)` remains strictly inside all three half-spaces.
  let c : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun _ ↦ 1 / 4)
  refine ⟨c, mem_interior_iff_mem_nhds.2 ?_⟩
  refine Filter.mem_of_superset (Metric.ball_mem_nhds c (show 0 < (1 / 8 : ℝ) by norm_num)) ?_
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

/-- Helper for Exercise 55.3: there exists a homeomorphism from the standard triangle to the
closed unit disk. -/
lemma standardTriangle_exists_homeomorph_closedUnitDisk : Nonempty (standardTriangle ≃ₜ B²) := by
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
    have hc0 : Continuous (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0) := by fun_prop
    have hc1 : Continuous (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 1) := by fun_prop
    exact (isClosed_le continuous_const hc0).inter
      ((isClosed_le continuous_const hc1).inter
        (isClosed_le (hc0.add hc1) continuous_const))
  rw [hclosed.closure_eq] at hclosure
  exact ⟨(e.image standardTriangle).trans (Homeomorph.setCongr hclosure)⟩

/-- Helper for Exercise 55.3: a chosen homeomorphism from the standard triangle to the closed
unit disk. -/
noncomputable def standardTriangleHomeomorphClosedUnitDisk : standardTriangle ≃ₜ B² :=
  Classical.choice standardTriangle_exists_homeomorph_closedUnitDisk

/-- Helper for Exercise 55.3: every continuous self-map of the standard triangle has a fixed
point. -/
lemma standardTriangle_exists_fixedPoint
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

/-- Helper for Exercise 55.3: encode a point of the standard triangle as a three-coordinate
probability vector. -/
noncomputable def triangleProbabilityVector (x : standardTriangle) : Fin 3 → ℝ :=
  ![x.1 0, x.1 1, 1 - x.1 0 - x.1 1]

/-- Helper for Exercise 55.3: every coordinate of the encoded probability vector is
nonnegative. -/
lemma triangleProbabilityVector_nonneg (x : standardTriangle) (i : Fin 3) :
    0 ≤ triangleProbabilityVector x i := by
  -- The third coordinate is the unused slack in the triangle inequality.
  have hx := (mem_standardTriangle x.1).mp x.2
  fin_cases i
  · exact hx.1
  · exact hx.2.1
  · have hthird : 0 ≤ 1 - x.1 0 - x.1 1 := by linarith [hx.2.2]
    simpa [triangleProbabilityVector] using hthird

/-- Helper for Exercise 55.3: the encoded probability-vector coordinates sum to one. -/
lemma triangleProbabilityVector_sum (x : standardTriangle) :
    ∑ i, triangleProbabilityVector x i = 1 := by
  -- The slack coordinate was chosen precisely to complete the sum to one.
  simp [triangleProbabilityVector, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]

/-- Helper for Exercise 55.3: the encoded probability vector is nonzero. -/
lemma triangleProbabilityVector_ne_zero (x : standardTriangle) :
    triangleProbabilityVector x ≠ 0 := by
  -- A zero vector cannot have coordinate sum one.
  intro hx
  have hsum := triangleProbabilityVector_sum x
  rw [hx] at hsum
  simp at hsum

/-- Helper for Exercise 55.3: the coordinate sum of the positive-matrix image of an encoded
probability vector. -/
noncomputable def positiveMatrixScale
    (B : Matrix (Fin 3) (Fin 3) ℝ) (x : standardTriangle) : ℝ :=
  ∑ i, B.mulVec (triangleProbabilityVector x) i

/-- Helper for Exercise 55.3: a strictly positive matrix has positive normalization scale on the
standard triangle. -/
lemma positiveMatrixScale_pos (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hB : ∀ i j, 0 < B i j) (x : standardTriangle) :
    0 < positiveMatrixScale B x := by
  -- Every output coordinate is positive because the input is nonnegative and has sum one.
  have hrow (i : Fin 3) : 0 < B.mulVec (triangleProbabilityVector x) i := by
    have hsum : 0 < ∑ j, B i j * triangleProbabilityVector x j := by
      have hweighted : 0 < ∑ j, B i j * triangleProbabilityVector x j := by
        have hmin : 0 < min (B i 0) (min (B i 1) (B i 2)) := by
          exact lt_min (hB i 0) (lt_min (hB i 1) (hB i 2))
        have hle : min (B i 0) (min (B i 1) (B i 2)) ≤
            ∑ j, B i j * triangleProbabilityVector x j := by
          rw [Fin.sum_univ_three]
          have h0 := triangleProbabilityVector_nonneg x 0
          have h1 := triangleProbabilityVector_nonneg x 1
          have h2 := triangleProbabilityVector_nonneg x 2
          have hs := triangleProbabilityVector_sum x
          rw [Fin.sum_univ_three] at hs
          have hb0 : min (B i 0) (min (B i 1) (B i 2)) ≤ B i 0 := min_le_left _ _
          have hb1 : min (B i 0) (min (B i 1) (B i 2)) ≤ B i 1 :=
            (min_le_right _ _).trans (min_le_left _ _)
          have hb2 : min (B i 0) (min (B i 1) (B i 2)) ≤ B i 2 :=
            (min_le_right _ _).trans (min_le_right _ _)
          nlinarith [mul_le_mul_of_nonneg_right hb0 h0,
            mul_le_mul_of_nonneg_right hb1 h1, mul_le_mul_of_nonneg_right hb2 h2]
        exact hmin.trans_le hle
      exact hweighted
    exact hsum
  unfold positiveMatrixScale
  exact Finset.sum_pos (fun i _ ↦ hrow i) Finset.univ_nonempty

/-- Helper for Exercise 55.3: the normalized positive-matrix action on the first two coordinates
lies in the standard triangle. -/
lemma normalizedPositiveMatrixAction_mem (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hB : ∀ i j, 0 < B i j) (x : standardTriangle) :
    WithLp.toLp 2 (fun i : Fin 2 ↦
      B.mulVec (triangleProbabilityVector x) i.castSucc / positiveMatrixScale B x) ∈
      standardTriangle := by
  -- Positivity gives the coordinate inequalities, and the omitted third coordinate gives slack.
  rw [mem_standardTriangle]
  have hs := positiveMatrixScale_pos B hB x
  have hrow (i : Fin 3) : 0 ≤ B.mulVec (triangleProbabilityVector x) i := by
    unfold Matrix.mulVec dotProduct
    exact Finset.sum_nonneg fun j _ ↦
      mul_nonneg (le_of_lt (hB i j)) (triangleProbabilityVector_nonneg x j)
  constructor
  · exact div_nonneg (hrow 0) hs.le
  constructor
  · exact div_nonneg (hrow 1) hs.le
  · unfold positiveMatrixScale
    rw [Fin.sum_univ_three]
    norm_num only [Fin.castSucc_zero, Fin.castSucc_one]
    rw [← add_div]
    exact (div_le_one (by simpa [positiveMatrixScale, Fin.sum_univ_three] using hs)).mpr
      (by linarith [hrow 2])

/-- Helper for Exercise 55.3: the normalized positive-matrix action is a self-map of the standard
triangle. -/
noncomputable def normalizedPositiveMatrixAction (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hB : ∀ i j, 0 < B i j) : standardTriangle → standardTriangle :=
  fun x ↦ ⟨WithLp.toLp 2 (fun i : Fin 2 ↦
    B.mulVec (triangleProbabilityVector x) i.castSucc / positiveMatrixScale B x),
    normalizedPositiveMatrixAction_mem B hB x⟩

/-- Helper for Exercise 55.3: the probability-vector encoding varies continuously on the
standard triangle. -/
lemma continuous_triangleProbabilityVector : Continuous triangleProbabilityVector := by
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

/-- Helper for Exercise 55.3: the normalization scale varies continuously on the standard
triangle. -/
lemma continuous_positiveMatrixScale (B : Matrix (Fin 3) (Fin 3) ℝ) :
    Continuous (positiveMatrixScale B) := by
  -- Matrix-vector multiplication and the finite coordinate sum preserve continuity.
  unfold positiveMatrixScale
  apply continuous_finsetSum Finset.univ
  intro i _
  exact (continuous_apply i).comp
    (continuous_const.matrix_mulVec continuous_triangleProbabilityVector)

/-- Helper for Exercise 55.3: the normalized positive-matrix action is continuous. -/
lemma continuous_normalizedPositiveMatrixAction (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hB : ∀ i j, 0 < B i j) : Continuous (normalizedPositiveMatrixAction B hB) := by
  -- The positive scale keeps the coordinatewise quotient away from division by zero.
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
  apply continuous_pi
  intro i
  have hmul : Continuous (fun x : standardTriangle ↦
      B.mulVec (triangleProbabilityVector x) i.castSucc) :=
    (continuous_apply i.castSucc).comp
      (continuous_const.matrix_mulVec continuous_triangleProbabilityVector)
  exact hmul.div (continuous_positiveMatrixScale B)
    (fun x ↦ (positiveMatrixScale_pos B hB x).ne')

/-- Helper for Exercise 55.3: a strictly positive real `3 × 3` matrix has a strictly positive
real eigenvalue. -/
lemma Matrix.exists_pos_eigenvalue_of_pos_local
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : ∀ i j, 0 < B i j) :
    ∃ μ : ℝ, 0 < μ ∧ HasEigenvalue B.toLin' μ := by
  -- Apply Brouwer to the normalized action on probability vectors.
  obtain ⟨x, hx⟩ := standardTriangle_exists_fixedPoint
    (normalizedPositiveMatrixAction B hB) (continuous_normalizedPositiveMatrixAction B hB)
  let v := triangleProbabilityVector x
  let μ := positiveMatrixScale B x
  have hμ : 0 < μ := positiveMatrixScale_pos B hB x
  have hfixed : (normalizedPositiveMatrixAction B hB x).1 = x.1 :=
    congrArg Subtype.val hx
  have hcoord (i : Fin 2) : B.mulVec v i.castSucc = μ * v i.castSucc := by
    have hi := congrFun (congrArg WithLp.ofLp hfixed) i
    fin_cases i
    · change B.mulVec v 0 / μ = v 0 at hi
      simpa [mul_comm] using (div_eq_iff hμ.ne').mp hi
    · change B.mulVec v 1 / μ = v 1 at hi
      simpa [mul_comm] using (div_eq_iff hμ.ne').mp hi
  have hthird : B.mulVec v 2 = μ * v 2 := by
    have hscale : B.mulVec v 0 + B.mulVec v 1 + B.mulVec v 2 = μ := by
      simpa [μ, positiveMatrixScale, Fin.sum_univ_three, v]
    have hvsum : v 0 + v 1 + v 2 = 1 := by
      simpa [Fin.sum_univ_three, v] using triangleProbabilityVector_sum x
    have h0 := hcoord 0
    have h1 := hcoord 1
    norm_num only [Fin.castSucc_zero, Fin.castSucc_one] at h0 h1
    nlinarith
  refine ⟨μ, hμ, ?_⟩
  -- The fixed-point coordinate equations assemble into a nonzero eigenvector.
  apply hasEigenvalue_of_hasEigenvector
  rw [hasEigenvector_iff]
  constructor
  · rw [mem_eigenspace_iff, Matrix.toLin'_apply]
    funext i
    fin_cases i
    · simpa [smul_eq_mul] using hcoord 0
    · simpa [smul_eq_mul] using hcoord 1
    · simpa [smul_eq_mul] using hthird
  · exact triangleProbabilityVector_ne_zero x

/-- Helper for Exercise 55.3: a nonnegative eigenvalue of a nonnegative `3 × 3` matrix is at most
the sum of all matrix entries. -/
lemma Matrix.nonneg_eigenvalue_le_sum_entries
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : ∀ i j, 0 ≤ B i j)
    (μ : ℝ) (hμ : 0 ≤ μ) (heig : HasEigenvalue B.toLin' μ) :
    μ ≤ ∑ i, ∑ j, B i j := by
  -- Compare the eigenvector equation at a coordinate of maximal absolute value.
  classical
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  rw [hasEigenvector_iff] at hv
  have heq : B.mulVec v = μ • v := by
    simpa [Matrix.toLin'_apply] using (mem_eigenspace_iff.mp hv.1)
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ (fun i ↦ |v i|)
    Finset.univ_nonempty
  have hvk : 0 < |v k| := by
    have hv_nonzero : ∃ i, v i ≠ 0 := by
      by_contra h
      apply hv.2
      funext i
      by_contra hi
      exact h ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hv_nonzero
    exact (abs_pos.mpr hi).trans_le (hk i (Finset.mem_univ i))
  have hrow : μ * |v k| ≤ (∑ j, B k j) * |v k| := by
    have hcoordinate := congrFun heq k
    have habs : μ * |v k| = |B.mulVec v k| := by
      rw [hcoordinate, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hμ]
    rw [habs]
    calc
      |B.mulVec v k| ≤ ∑ j, |B k j * v j| := by
        unfold Matrix.mulVec dotProduct
        simpa using Finset.abs_sum_le_sum_abs (fun j ↦ B k j * v j) Finset.univ
      _ = ∑ j, B k j * |v j| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul, abs_of_nonneg (hB k j)]
      _ ≤ ∑ j, B k j * |v k| := by
        exact Finset.sum_le_sum fun j _ ↦
          mul_le_mul_of_nonneg_left (hk j (Finset.mem_univ j)) (hB k j)
      _ = (∑ j, B k j) * |v k| := by rw [Finset.sum_mul]
  have hrow_bound : ∑ j, B k j ≤ ∑ i, ∑ j, B i j := by
    exact Finset.single_le_sum
      (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hB i j) (Finset.mem_univ k)
  have hscaled : μ * |v k| ≤ (∑ i, ∑ j, B i j) * |v k| :=
    hrow.trans (mul_le_mul_of_nonneg_right hrow_bound hvk.le)
  exact le_of_mul_le_mul_right hscaled hvk

/-- Helper for Exercise 55.3: an eigenvalue of a real matrix is characterized by
the vanishing of its characteristic determinant at that scalar. -/
lemma Matrix.hasEigenvalue_toLin'_iff_det_sub_smul_one_eq_zero
    (B : Matrix (Fin 3) (Fin 3) ℝ) (μ : ℝ) :
    HasEigenvalue B.toLin' μ ↔
      (B - μ • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = 0 := by
  -- Translate the eigenspace condition into singularity of the shifted endomorphism.
  rw [hasEigenvalue_iff, eigenspace_def, ← LinearMap.det_eq_zero_iff_ker_ne_bot]
  -- Identify that shifted endomorphism with the linear map of the shifted matrix.
  have hdet : LinearMap.det (B.toLin' - μ • 1) =
      (B - μ • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det := by
    rw [← LinearMap.det_toLin']
    congr 1
    ext x i
    simp
  rw [hdet]

/-- Helper for Exercise 55.3: determinant-zero equations for shifted matrices
are preserved under simultaneous convergence of the matrices and scalars. -/
lemma Matrix.det_sub_smul_one_eq_zero_of_tendsto
    (B : ℕ → Matrix (Fin 3) (Fin 3) ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (μs : ℕ → ℝ) (μ : ℝ) (hB : Filter.Tendsto B Filter.atTop (nhds A))
    (hμ : Filter.Tendsto μs Filter.atTop (nhds μ))
    (hz : ∀ n, (B n - μs n • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = 0) :
    (A - μ • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = 0 := by
  -- First pass convergence through subtraction and scalar multiplication.
  have hmat : Filter.Tendsto
      (fun n ↦ B n - μs n • (1 : Matrix (Fin 3) (Fin 3) ℝ)) Filter.atTop
      (nhds (A - μ • (1 : Matrix (Fin 3) (Fin 3) ℝ))) := by
    exact hB.sub (hμ.smul tendsto_const_nhds)
  -- Continuity of the determinant gives the desired limiting determinant.
  have hdet : Filter.Tendsto
      (fun n ↦ (B n - μs n • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det) Filter.atTop
      (nhds ((A - μ • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det)) := by
    exact (continuous_id.matrix_det.tendsto _).comp hmat
  have hzero : Filter.Tendsto (fun _ : ℕ ↦ (0 : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds
  have hdetzero : Filter.Tendsto
      (fun n ↦ (B n - μs n • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det) Filter.atTop
      (nhds 0) := by
    simpa only [hz] using hzero
  exact tendsto_nhds_unique hdet hdetzero

/-- Helper for Exercise 55.3: nonsingularity excludes zero from the shifted
determinant equation. -/
lemma Matrix.det_sub_smul_one_ne_zero_at_zero
    (A : Matrix (Fin 3) (Fin 3) ℝ) (h_nonsingular : A.det ≠ 0) :
    (A - 0 • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det ≠ 0 := by
  -- At scalar zero the shifted matrix simplifies back to the original matrix.
  simpa using h_nonsingular

/-- Exercise 55.3. Every nonsingular `3 × 3` real matrix with nonnegative entries
has a strictly positive real eigenvalue. -/
theorem Matrix.exists_pos_eigenvalue_of_nonneg_of_det_ne_zero
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (h_nonsingular : A.det ≠ 0) :
    ∃ μ : ℝ, 0 < μ ∧ HasEigenvalue A.toLin' μ := by
  -- Route correction: reconstruct the unavailable positive-entry corollary locally via
  -- Brouwer, then pass positive eigenvalues of small positive perturbations to a limit.
  classical
  let B : ℕ → Matrix (Fin 3) (Fin 3) ℝ :=
    fun n i j ↦ A i j + 1 / ((n : ℝ) + 1)
  have hB_pos (n : ℕ) : ∀ i j, 0 < B n i j := by
    intro i j
    dsimp [B]
    have hden : 0 < (n : ℝ) + 1 := by exact_mod_cast Nat.succ_pos n
    exact add_pos_of_nonneg_of_pos (hA i j) (one_div_pos.mpr hden)
  choose μ hμ_pos hμ_eig using fun n ↦ Matrix.exists_pos_eigenvalue_of_pos_local (B n) (hB_pos n)
  have hB_nonneg (n : ℕ) : ∀ i j, 0 ≤ B n i j :=
    fun i j ↦ (hB_pos n i j).le
  have hμ_upper (n : ℕ) : μ n ≤ ∑ i, ∑ j, A i j + 9 := by
    have hbound := Matrix.nonneg_eigenvalue_le_sum_entries (B n) (hB_nonneg n)
      (μ n) (hμ_pos n).le (hμ_eig n)
    have hperturb : ∑ i, ∑ j, B n i j ≤ ∑ i, ∑ j, A i j + 9 := by
      simp only [B, Fin.sum_univ_three]
      have hden : 0 < (n : ℝ) + 1 := by exact_mod_cast Nat.succ_pos n
      have hfrac : 1 / ((n : ℝ) + 1) ≤ 1 := by
        exact (div_le_one hden).mpr (by norm_num)
      linarith
    exact hbound.trans hperturb
  have hμ_mem (n : ℕ) : μ n ∈ Set.Icc 0 (∑ i, ∑ j, A i j + 9) :=
    ⟨(hμ_pos n).le, hμ_upper n⟩
  obtain ⟨μlim, hμlim_mem, φ, hφ, hμlim⟩ := isCompact_Icc.tendsto_subseq hμ_mem
  have hB_tendsto : Filter.Tendsto (B ∘ φ) Filter.atTop (nhds A) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have hfrac : Filter.Tendsto
        (fun n : ℕ ↦ 1 / (((φ n : ℕ) : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    simpa [B, Function.comp_def] using tendsto_const_nhds.add hfrac
  have hdetzero (n : ℕ) :
      (B (φ n) - μ (φ n) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = 0 := by
    exact (Matrix.hasEigenvalue_toLin'_iff_det_sub_smul_one_eq_zero _ _).mp (hμ_eig (φ n))
  have hlimit_det :
      (A - μlim • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = 0 := by
    exact Matrix.det_sub_smul_one_eq_zero_of_tendsto (B ∘ φ) A (μ ∘ φ) μlim
      hB_tendsto hμlim hdetzero
  have hμlim_ne : μlim ≠ 0 := by
    intro hzero
    apply Matrix.det_sub_smul_one_ne_zero_at_zero A h_nonsingular
    simpa [hzero] using hlimit_det
  refine ⟨μlim, lt_of_le_of_ne hμlim_mem.1 (Ne.symm hμlim_ne), ?_⟩
  exact (Matrix.hasEigenvalue_toLin'_iff_det_sub_smul_one_eq_zero A μlim).mpr hlimit_det
