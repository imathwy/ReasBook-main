import BauschkeLean.Chap22.Definition_22_13
import BauschkeLean.Chap22.Example_22_15
import Mathlib.Analysis.Fourier.ZMod

open Complex
open scoped BigOperators EuclideanSpace InnerProductSpace

noncomputable section

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The standard counterclockwise orientation on `ℝ²`, obtained by transporting the standard
orientation on `ℂ` across the canonical orthonormal-basis isometry `ℂ ≃ₗᵢ[ℝ] ℝ²`. -/
abbrev counterclockwiseOrientation : Orientation ℝ ℝ² (Fin 2) :=
  Orientation.map (Fin 2)
    (Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)).toLinearEquiv
    Complex.orientation

private abbrev euclideanToComplex : ℝ² ≃ₗᵢ[ℝ] ℂ :=
  (Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)).symm

private theorem counterclockwiseOrientation_map_euclideanToComplex :
    Orientation.map (Fin 2) euclideanToComplex.toLinearEquiv counterclockwiseOrientation =
      Complex.orientation := by
  simpa [counterclockwiseOrientation, euclideanToComplex, Orientation.map_symm] using
    (Equiv.symm_apply_apply
      (Orientation.map (Fin 2)
        (Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)).toLinearEquiv)
      Complex.orientation)

private theorem counterclockwiseRotation_complex (θ : Real.Angle) (x : ℝ²) :
    euclideanToComplex (counterclockwiseOrientation.rotation θ x) =
      θ.toCircle * euclideanToComplex x := by
  simpa [counterclockwiseOrientation, euclideanToComplex, Orientation.map_symm] using
    (counterclockwiseOrientation.rotation_map_complex θ euclideanToComplex
      counterclockwiseOrientation_map_euclideanToComplex x)

/-- Evaluating the counterclockwise rotation on `ℝ²` recovers the usual trigonometric coordinate
formula. -/
@[simp] theorem counterclockwiseRotation_apply (θ : ℝ) (x : ℝ²) :
    counterclockwiseOrientation.rotation θ x =
      !₂[Real.cos θ * x 0 - Real.sin θ * x 1, Real.sin θ * x 0 + Real.cos θ * x 1] := by
  apply euclideanToComplex.injective
  change euclideanToComplex (counterclockwiseOrientation.rotation θ x) =
    euclideanToComplex !₂[Real.cos θ * x 0 - Real.sin θ * x 1,
      Real.sin θ * x 0 + Real.cos θ * x 1]
  rw [counterclockwiseRotation_complex]
  apply Complex.ext <;>
    simp [euclideanToComplex, Complex.isometryOfOrthonormal, Complex.exp_mul_I,
      sub_eq_add_neg, add_mul]
  ring_nf

/-- Remark 22.16 (1): the operator of Example 22.15 is the counterclockwise rotator on `ℝ²`
through the angle `π / 2`. -/
theorem quarterTurnOperator_eq_counterclockwiseRotationOperator_pi_div_two :
    quarterTurnOperator =
      (counterclockwiseOrientation.rotation (Real.pi / 2 : ℝ)).toContinuousLinearMap := by
  ext x i
  fin_cases i
  · have h0 := congrArg (fun y : ℝ² ↦ y 0) (counterclockwiseRotation_apply (Real.pi / 2 : ℝ) x)
    simp [quarterTurnOperator_apply] at h0 ⊢
  · have h1 := congrArg (fun y : ℝ² ↦ y 1) (counterclockwiseRotation_apply (Real.pi / 2 : ℝ) x)
    simp [quarterTurnOperator_apply] at h1 ⊢

/-- Helper for Remark 22.16: a planar counterclockwise rotation splits into its identity part and
the quarter-turn part. -/
private theorem rotation_apply_eq_cos_smul_add_sin_smul_quarter_turn (θ : ℝ) (x : ℝ²) :
    counterclockwiseOrientation.rotation θ x =
      Real.cos θ • x + Real.sin θ • quarterTurnOperator x := by
  -- Compare both coordinates with the explicit trigonometric formulas for the two operators.
  ext i
  fin_cases i
  · have h0 := congrArg (fun y : ℝ² ↦ y 0) (counterclockwiseRotation_apply θ x)
    simp [quarterTurnOperator_apply] at h0 ⊢
    ring
  · have h1 := congrArg (fun y : ℝ² ↦ y 1) (counterclockwiseRotation_apply θ x)
    simp [quarterTurnOperator_apply] at h1 ⊢
    ring

/-- Helper for Remark 22.16: on a closed cycle, the self-pairing term is exactly minus one half of
the total edge energy. -/
private theorem closed_cycle_self_pairing_eq_neg_half_edge_energy
    {n : ℕ} (x : ℕ → ℝ²) (hx : x n = x 0) :
    Finset.sum (Finset.range n) (fun i ↦ ⟪x (i + 1) - x i, x i⟫_ℝ) =
      -((1 : ℝ) / 2) * (Finset.sum (Finset.range n) (fun i ↦ ‖x (i + 1) - x i‖ ^ 2)) := by
  let edge : ℕ → ℝ := fun i ↦ ‖x (i + 1) - x i‖ ^ 2
  let selfPair : ℕ → ℝ := fun i ↦ ⟪x (i + 1) - x i, x i⟫_ℝ
  have hstep :
      ∀ i, edge i + 2 * selfPair i = ‖x (i + 1)‖ ^ 2 - ‖x i‖ ^ 2 := by
    intro i
    -- Expand one edge and collect the telescoping norm terms.
    calc
      edge i + 2 * selfPair i
          = ‖x (i + 1) - x i‖ ^ 2 + 2 * ⟪x (i + 1) - x i, x i⟫_ℝ := by
              simp [edge, selfPair]
      _ = (‖x (i + 1)‖ ^ 2 - 2 * ⟪x (i + 1), x i⟫_ℝ + ‖x i‖ ^ 2) +
            2 * (⟪x (i + 1), x i⟫_ℝ - ‖x i‖ ^ 2) := by
              simp [norm_sub_sq_real, inner_sub_left]
      _ = ‖x (i + 1)‖ ^ 2 - ‖x i‖ ^ 2 := by
            ring
  have htelescoping :
      Finset.sum (Finset.range n) (fun i ↦ edge i + 2 * selfPair i) = 0 := by
    -- Sum the one-step identity and collapse the right-hand side to the endpoint difference.
    calc
      Finset.sum (Finset.range n) (fun i ↦ edge i + 2 * selfPair i)
          = Finset.sum (Finset.range n) (fun i ↦ ‖x (i + 1)‖ ^ 2 - ‖x i‖ ^ 2) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hstep i
      _ = ‖x n‖ ^ 2 - ‖x 0‖ ^ 2 := by
            simpa using Finset.sum_range_sub (fun i ↦ ‖x i‖ ^ 2) n
      _ = 0 := by
            simp [hx]
  have hsum :
      Finset.sum (Finset.range n) edge + 2 * Finset.sum (Finset.range n) selfPair = 0 := by
    simpa [Finset.sum_add_distrib, Finset.mul_sum, edge, selfPair,
      add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      htelescoping
  have hfinal :
      Finset.sum (Finset.range n) selfPair =
        -((1 : ℝ) / 2) * Finset.sum (Finset.range n) edge := by
    linarith
  simpa [edge, selfPair] using hfinal

/-- Helper for Remark 22.16: the cyclic defect of a rotation splits into an edge-energy term and
an oriented-area term measured by the quarter-turn operator. -/
private theorem rotation_cycle_sum_split
    {n : ℕ} (θ : ℝ) (x : ℕ → ℝ²) (hx : x n = x 0) :
    Finset.sum (Finset.range n)
        (fun i ↦ ⟪x (i + 1) - x i, counterclockwiseOrientation.rotation θ (x i)⟫_ℝ) =
      -(Real.cos θ / 2) * (Finset.sum (Finset.range n) (fun i ↦ ‖x (i + 1) - x i‖ ^ 2)) +
        Real.sin θ *
          (Finset.sum (Finset.range n)
            (fun i ↦ ⟪x (i + 1) - x i, quarterTurnOperator (x i)⟫_ℝ)) := by
  -- First rewrite each summand using the linear decomposition of the rotation.
  calc
    Finset.sum (Finset.range n)
        (fun i ↦ ⟪x (i + 1) - x i, counterclockwiseOrientation.rotation θ (x i)⟫_ℝ)
        = Real.cos θ * Finset.sum (Finset.range n) (fun i ↦ ⟪x (i + 1) - x i, x i⟫_ℝ) +
            Real.sin θ *
              Finset.sum (Finset.range n)
                (fun i ↦ ⟪x (i + 1) - x i, quarterTurnOperator (x i)⟫_ℝ) := by
            calc
              Finset.sum (Finset.range n)
                  (fun i ↦ ⟪x (i + 1) - x i, counterclockwiseOrientation.rotation θ (x i)⟫_ℝ)
                  = Finset.sum (Finset.range n)
                      (fun i ↦
                        Real.cos θ * ⟪x (i + 1) - x i, x i⟫_ℝ +
                          Real.sin θ *
                            ⟪x (i + 1) - x i, quarterTurnOperator (x i)⟫_ℝ) := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      rw [rotation_apply_eq_cos_smul_add_sin_smul_quarter_turn]
                      simp [inner_add_right, inner_smul_right]
              _ = Real.cos θ * Finset.sum (Finset.range n) (fun i ↦ ⟪x (i + 1) - x i, x i⟫_ℝ) +
                    Real.sin θ *
                      Finset.sum (Finset.range n)
                        (fun i ↦ ⟪x (i + 1) - x i, quarterTurnOperator (x i)⟫_ℝ) := by
                    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = Real.cos θ *
          (-((1 : ℝ) / 2) * Finset.sum (Finset.range n) (fun i ↦ ‖x (i + 1) - x i‖ ^ 2)) +
        Real.sin θ *
          Finset.sum (Finset.range n)
            (fun i ↦ ⟪x (i + 1) - x i, quarterTurnOperator (x i)⟫_ℝ) := by
          rw [closed_cycle_self_pairing_eq_neg_half_edge_energy x hx]
    _ = -(Real.cos θ / 2) * Finset.sum (Finset.range n) (fun i ↦ ‖x (i + 1) - x i‖ ^ 2) +
        Real.sin θ *
          Finset.sum (Finset.range n)
            (fun i ↦ ⟪x (i + 1) - x i, quarterTurnOperator (x i)⟫_ℝ) := by
          ring

/-- Helper for Remark 22.16: the complex model turns the quarter-turn pairing into the
imaginary part of the Hermitian product. -/
private theorem inner_quarterTurn_eq_complex_im_mul_conj (v w : ℝ²) :
    ⟪v, quarterTurnOperator w⟫_ℝ =
      Complex.im (euclideanToComplex v * (starRingEnd ℂ) (euclideanToComplex w)) := by
  -- Rewrite the quarter-turn as the oriented right-angle rotation, then transport the area form
  -- to `ℂ` where it is the imaginary part of the Hermitian product.
  have hquarter : quarterTurnOperator w = counterclockwiseOrientation.rightAngleRotation w := by
    simpa [counterclockwiseOrientation.rotation_pi_div_two] using
      congrArg (fun f : ℝ² →L[ℝ] ℝ² ↦ f w)
        quarterTurnOperator_eq_counterclockwiseRotationOperator_pi_div_two
  rw [hquarter, counterclockwiseOrientation.inner_rightAngleRotation_right]
  rw [counterclockwiseOrientation.areaForm_map_complex euclideanToComplex
    counterclockwiseOrientation_map_euclideanToComplex]
  have him :
      ((starRingEnd ℂ) (euclideanToComplex v) * euclideanToComplex w).im =
        -Complex.im (euclideanToComplex v * (starRingEnd ℂ) (euclideanToComplex w)) := by
    simpa [map_mul] using
      (Complex.conj_im
        (euclideanToComplex v * (starRingEnd ℂ) (euclideanToComplex w)))
  have him' := congrArg Neg.neg him
  simpa using him'

/-- Helper for Remark 22.16: the Euclidean-to-complex isometry preserves squared norms. -/
private theorem complex_normSq_eq_real_norm_sq (v : ℝ²) :
    Complex.normSq (euclideanToComplex v) = ‖v‖ ^ 2 := by
  -- The bridge to `ℂ` is an isometry, so the complex norm square is the original squared norm.
  rw [← Complex.sq_norm]
  simpa using congrArg (fun t : ℝ ↦ t ^ 2) (euclideanToComplex.norm_map v)

/-- Helper for Remark 22.16: the real inner product on `ℝ` is ordinary multiplication. -/
private theorem real_inner_eq_mul (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  -- View `a` as a scalar multiple of `1` and use linearity of the real inner product.
  have hone : ⟪(1 : ℝ), b⟫_ℝ = b := by
    calc
      ⟪(1 : ℝ), b⟫_ℝ = ⟪(1 : ℝ), b • (1 : ℝ)⟫_ℝ := by simp
      _ = b * ⟪(1 : ℝ), (1 : ℝ)⟫_ℝ := by rw [real_inner_smul_right]
      _ = b := by simp
  calc
    ⟪a, b⟫_ℝ = ⟪a • (1 : ℝ), b⟫_ℝ := by simp
    _ = a * ⟪(1 : ℝ), b⟫_ℝ := by rw [real_inner_smul_left]
    _ = a * b := by rw [hone]

/-- Helper for Remark 22.16: transporting a polygonal cycle to `ℂ` preserves the quarter-turn
defect term pointwise. -/
private theorem complex_cycle_quarter_turn_sum_eq
    {n : ℕ} (x : ℕ → ℝ²) :
    Finset.sum (Finset.range n) (fun i ↦ ⟪x (i + 1) - x i, quarterTurnOperator (x i)⟫_ℝ) =
      Finset.sum (Finset.range n)
        (fun i ↦
          Complex.im
            ((euclideanToComplex (x (i + 1)) - euclideanToComplex (x i)) *
              (starRingEnd ℂ) (euclideanToComplex (x i)))) := by
  -- Rewrite each planar quarter-turn summand in the complex coordinates provided by the isometry.
  apply Finset.sum_congr rfl
  intro i hi
  simpa using inner_quarterTurn_eq_complex_im_mul_conj (x (i + 1) - x i) (x i)

/-- Helper for Remark 22.16: transporting a polygonal cycle to `ℂ` preserves the edge-energy term
pointwise. -/
private theorem complex_cycle_edge_energy_sum_eq
    {n : ℕ} (x : ℕ → ℝ²) :
    Finset.sum (Finset.range n) (fun i ↦ ‖x (i + 1) - x i‖ ^ 2) =
      Finset.sum (Finset.range n)
        (fun i ↦ Complex.normSq (euclideanToComplex (x (i + 1)) - euclideanToComplex (x i))) := by
  -- The Euclidean-to-complex linear isometry preserves the norm of every edge difference.
  apply Finset.sum_congr rfl
  intro i hi
  simpa using (complex_normSq_eq_real_norm_sq (x (i + 1) - x i)).symm

/-- Helper for Remark 22.16: a closed real cycle stays closed after transport to `ℂ`. -/
private theorem complex_cycle_closed_of_real_cycle_closed
    {n : ℕ} (x : ℕ → ℝ²) (hx : x n = x 0) :
    euclideanToComplex (x n) = euclideanToComplex (x 0) := by
  -- Apply the linear isometry to the endpoint identity.
  simpa using congrArg euclideanToComplex hx

/-- Helper for Remark 22.16: the standard additive character has the expected orthogonality sum on
`ZMod n`. -/
private theorem zmod_sum_stdAddChar_mul
    {n : ℕ} [NeZero n] (t : ZMod n) :
    ∑ i : ZMod n, ZMod.stdAddChar (t * i) = if t = 0 then (n : ℂ) else 0 := by
  -- Separate the zero mode from the primitive nonzero modes.
  by_cases ht : t = 0
  · simp [ht]
  · have hsum : ∑ i : ZMod n, ZMod.stdAddChar (t * i) = 0 := by
        simpa [AddChar.mulShift_apply] using
          (AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar n ht) :
            ∑ a, (ZMod.stdAddChar.mulShift t) a = 0)
    simpa [ht] using hsum

/-- Helper for Remark 22.16: shifting a function on `ZMod n` by one step multiplies its discrete
Fourier transform by the corresponding additive character. -/
private theorem zmod_dft_shift_apply
    {n : ℕ} [NeZero n] (f : ZMod n → ℂ) (k : ZMod n) :
    ZMod.dft (fun j ↦ f (j + 1)) k = ZMod.stdAddChar k * ZMod.dft f k := by
  -- Reindex the defining Fourier sum by the cyclic permutation `j ↦ j - 1`.
  rw [ZMod.dft_apply, ZMod.dft_apply]
  have hshift :
      ∑ j : ZMod n, ZMod.stdAddChar (-(j * k)) * f (j + 1) =
        ∑ j : ZMod n, ZMod.stdAddChar (-((j - 1) * k)) * f j := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      ((Equiv.sum_comp (Equiv.addRight (-1 : ZMod n))
        (fun j : ZMod n ↦ ZMod.stdAddChar (-(j * k)) * f (j + 1))).symm)
  calc
    ∑ j : ZMod n, ZMod.stdAddChar (-(j * k)) * f (j + 1)
        = ∑ j : ZMod n, ZMod.stdAddChar (-((j - 1) * k)) * f j := hshift
    _ = ∑ j : ZMod n, (ZMod.stdAddChar k * ZMod.stdAddChar (-(j * k))) * f j := by
          apply Fintype.sum_congr
          intro j
          have harg : -((j - 1) * k) = k + -(j * k) := by
            ring
          have hchar :
              ZMod.stdAddChar (k + -(j * k)) =
                ZMod.stdAddChar k * ZMod.stdAddChar (-(j * k)) := by
            simpa using ZMod.stdAddChar.map_add_eq_mul k (-(j * k))
          rw [harg, hchar]
    _ = ZMod.stdAddChar k * ∑ j : ZMod n, ZMod.stdAddChar (-(j * k)) * f j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring

/-- Helper for Remark 22.16: the cyclic difference operator is diagonalized by the discrete
Fourier transform on `ZMod n`. -/
private theorem zmod_dft_difference_apply
    {n : ℕ} [NeZero n] (f : ZMod n → ℂ) (k : ZMod n) :
    ZMod.dft (fun j ↦ f (j + 1) - f j) k = (ZMod.stdAddChar k - 1) * ZMod.dft f k := by
  -- Expand the transform across the difference, then insert the one-step shift formula.
  calc
    ZMod.dft (fun j ↦ f (j + 1) - f j) k = ZMod.dft (fun j ↦ f (j + 1)) k - ZMod.dft f k := by
      simp [ZMod.dft_apply, smul_eq_mul, sub_eq_add_neg, mul_add, Finset.sum_add_distrib]
    _ = ZMod.stdAddChar k * ZMod.dft f k - ZMod.dft f k := by
          rw [zmod_dft_shift_apply]
    _ = (ZMod.stdAddChar k - 1) * ZMod.dft f k := by
          ring

/-- Helper for Remark 22.16: conjugating the Fourier kernel replaces the negative frequency in
`ZMod.dft` by the positive-frequency additive character. -/
private theorem zmod_conj_dft_apply
    {n : ℕ} [NeZero n] (h : ZMod n → ℂ) (k : ZMod n) :
    ∑ j : ZMod n, ZMod.stdAddChar (j * k) * (starRingEnd ℂ) (h j) =
      (starRingEnd ℂ) (ZMod.dft h k) := by
  -- Identify the conjugated kernel with the positive-frequency character on the unit circle.
  have hkernel (t : ZMod n) :
      (starRingEnd ℂ) (ZMod.stdAddChar (-t)) = ZMod.stdAddChar t := by
    rw [ZMod.stdAddChar_apply]
    rw [show ZMod.toCircle (-t) = (ZMod.toCircle t)⁻¹ by
      simpa using (AddChar.map_neg_eq_inv (ZMod.toCircle) t)]
    rw [Circle.coe_inv_eq_conj]
    simpa [ZMod.stdAddChar_apply] using (Complex.conj_conj ((ZMod.toCircle t : Circle) : ℂ))
  rw [ZMod.dft_apply]
  symm
  calc
    (starRingEnd ℂ) (∑ j : ZMod n, ZMod.stdAddChar (-(j * k)) • h j)
        = ∑ j : ZMod n, (starRingEnd ℂ) (ZMod.stdAddChar (-(j * k)) • h j) := by
            rw [map_sum]
    _ = ∑ j : ZMod n, ZMod.stdAddChar (j * k) * (starRingEnd ℂ) (h j) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [smul_eq_mul, hkernel, mul_comm]

/-- Helper for Remark 22.16: Parseval's identity for the `ZMod` Fourier transform in mixed
pairing form. -/
private theorem zmod_parseval_pairing
    {n : ℕ} [NeZero n] (g h : ZMod n → ℂ) :
    ∑ j : ZMod n, g j * (starRingEnd ℂ) (h j) =
      ((n : ℂ)⁻¹) * ∑ k : ZMod n, ZMod.dft g k * (starRingEnd ℂ) (ZMod.dft h k) := by
  -- Expand `g` by Fourier inversion and collapse the inner character sum to the conjugated
  -- Fourier coefficient of `h`.
  have hg (j : ZMod n) :
      g j = ((n : ℂ)⁻¹) * ∑ k : ZMod n, ZMod.stdAddChar (k * j) * ZMod.dft g k := by
    calc
      g j = ZMod.dft.symm (ZMod.dft g) j := by
        simpa using (congrFun (ZMod.dft.left_inv g) j).symm
      _ = ((n : ℂ)⁻¹) * ∑ k : ZMod n, ZMod.stdAddChar (k * j) * ZMod.dft g k := by
        simpa [smul_eq_mul, mul_comm] using (ZMod.invDFT_apply (Ψ := ZMod.dft g) j)
  calc
    ∑ j : ZMod n, g j * (starRingEnd ℂ) (h j)
        = ∑ j : ZMod n,
            ((((n : ℂ)⁻¹) * ∑ k : ZMod n, ZMod.stdAddChar (k * j) * ZMod.dft g k) *
              (starRingEnd ℂ) (h j)) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hg j]
    _ = ∑ j : ZMod n,
          (n : ℂ)⁻¹ *
            ((∑ k : ZMod n, ZMod.stdAddChar (k * j) * ZMod.dft g k) *
              (starRingEnd ℂ) (h j)) := by
                apply Finset.sum_congr rfl
                intro j hj
                ring
    _ = (n : ℂ)⁻¹ * ∑ j : ZMod n,
          (∑ k : ZMod n, ZMod.stdAddChar (k * j) * ZMod.dft g k) *
            (starRingEnd ℂ) (h j) := by
              rw [Finset.mul_sum]
    _ = ((n : ℂ)⁻¹) * ∑ k : ZMod n, ZMod.dft g k * (∑ j : ZMod n,
          ZMod.stdAddChar (k * j) * (starRingEnd ℂ) (h j)) := by
            congr 1
            calc
              ∑ j : ZMod n,
                  (∑ k : ZMod n, ZMod.stdAddChar (k * j) * ZMod.dft g k) *
                    (starRingEnd ℂ) (h j)
                  = ∑ j : ZMod n, ∑ k : ZMod n,
                      (ZMod.stdAddChar (k * j) * ZMod.dft g k) * (starRingEnd ℂ) (h j) := by
                        apply Finset.sum_congr rfl
                        intro j hj
                        rw [Finset.sum_mul]
              _ = ∑ k : ZMod n, ∑ j : ZMod n,
                    (ZMod.stdAddChar (k * j) * ZMod.dft g k) * (starRingEnd ℂ) (h j) := by
                      rw [Finset.sum_comm]
              _ = ∑ k : ZMod n, ZMod.dft g k * ∑ j : ZMod n,
                    ZMod.stdAddChar (k * j) * (starRingEnd ℂ) (h j) := by
                      apply Finset.sum_congr rfl
                      intro k hk
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro j hj
                      ring
    _ = ((n : ℂ)⁻¹) * ∑ k : ZMod n, ZMod.dft g k * (starRingEnd ℂ) (ZMod.dft h k) := by
            congr 1
            apply Finset.sum_congr rfl
            intro k hk
            rw [show ∑ j : ZMod n, ZMod.stdAddChar (k * j) * (starRingEnd ℂ) (h j) =
                (starRingEnd ℂ) (ZMod.dft h k) by
              simpa [mul_comm] using zmod_conj_dft_apply h k]

/-- Helper for Remark 22.16: the cyclic defect pairing is the Fourier-mode sum with coefficient
`ZMod.stdAddChar k - 1`. -/
private theorem zmod_difference_pairing_eq_frequency_sum
    {n : ℕ} [NeZero n] (f : ZMod n → ℂ) :
    let Δ : ZMod n → ℂ := fun j ↦ f (j + 1) - f j
    ∑ j : ZMod n, Δ j * (starRingEnd ℂ) (f j) =
      ((n : ℂ)⁻¹) * ∑ k : ZMod n, (ZMod.stdAddChar k - 1) * (Complex.normSq (ZMod.dft f k) : ℂ) := by
  let Δ : ZMod n → ℂ := fun j ↦ f (j + 1) - f j
  -- Specialize Parseval to `(Δ, f)` and then diagonalize `Δ` by the one-step difference formula.
  calc
    ∑ j : ZMod n, Δ j * (starRingEnd ℂ) (f j)
        = ((n : ℂ)⁻¹) * ∑ k : ZMod n, ZMod.dft Δ k * (starRingEnd ℂ) (ZMod.dft f k) := by
            simpa using zmod_parseval_pairing Δ f
    _ = ((n : ℂ)⁻¹) * ∑ k : ZMod n,
          ((ZMod.stdAddChar k - 1) * ZMod.dft f k) * (starRingEnd ℂ) (ZMod.dft f k) := by
            congr 1
            apply Finset.sum_congr rfl
            intro k hk
            rw [show ZMod.dft Δ k = (ZMod.stdAddChar k - 1) * ZMod.dft f k by
              simpa [Δ] using zmod_dft_difference_apply f k]
    _ = ((n : ℂ)⁻¹) * ∑ k : ZMod n,
          (ZMod.stdAddChar k - 1) * (Complex.normSq (ZMod.dft f k) : ℂ) := by
            congr 1
            apply Finset.sum_congr rfl
            intro k hk
            simpa [mul_assoc] using congrArg (fun t : ℂ => (ZMod.stdAddChar k - 1) * t)
              (Complex.mul_conj (ZMod.dft f k))

/-- Helper for Remark 22.16: the total edge energy is the Fourier-mode sum of the squared
difference multiplier. -/
private theorem zmod_difference_energy_eq_frequency_sum
    {n : ℕ} [NeZero n] (f : ZMod n → ℂ) :
    let Δ : ZMod n → ℂ := fun j ↦ f (j + 1) - f j
    ∑ j : ZMod n, Complex.normSq (Δ j) =
      ((n : ℝ)⁻¹) * ∑ k : ZMod n,
        Complex.normSq (ZMod.stdAddChar k - 1) * Complex.normSq (ZMod.dft f k) := by
  let Δ : ZMod n → ℂ := fun j ↦ f (j + 1) - f j
  -- First record the complex Parseval identity for `Δ`, then strip `Complex.ofReal` at the end.
  have hcomplex :
      (((∑ j : ZMod n, Complex.normSq (Δ j) : ℝ)) : ℂ) =
        ((((n : ℝ)⁻¹) * ∑ k : ZMod n,
            Complex.normSq (ZMod.stdAddChar k - 1) * Complex.normSq (ZMod.dft f k)) : ℝ) := by
    calc
      (((∑ j : ZMod n, Complex.normSq (Δ j) : ℝ)) : ℂ)
          = ∑ j : ZMod n, (Complex.normSq (Δ j) : ℂ) := by
              simp
      _ = ∑ j : ZMod n, Δ j * (starRingEnd ℂ) (Δ j) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Complex.mul_conj]
      _ = ((n : ℂ)⁻¹) * ∑ k : ZMod n, ZMod.dft Δ k * (starRingEnd ℂ) (ZMod.dft Δ k) := by
            simpa using zmod_parseval_pairing Δ Δ
      _ = ((n : ℂ)⁻¹) * ∑ k : ZMod n,
            (((Complex.normSq (ZMod.stdAddChar k - 1) *
                Complex.normSq (ZMod.dft f k)) : ℝ) : ℂ) := by
              congr 1
              apply Finset.sum_congr rfl
              intro k hk
              rw [show ZMod.dft Δ k = (ZMod.stdAddChar k - 1) * ZMod.dft f k by
                simpa [Δ] using zmod_dft_difference_apply f k]
              rw [Complex.mul_conj, Complex.normSq_mul]
      _ = ((((n : ℝ)⁻¹) * ∑ k : ZMod n,
            Complex.normSq (ZMod.stdAddChar k - 1) * Complex.normSq (ZMod.dft f k)) : ℝ) := by
              simp [Complex.ofReal_mul]
  exact Complex.ofReal_injective hcomplex

/-- Helper for Remark 22.16: after transporting a closed complex cycle to `ZMod n`, the
quarter-turn defect sum is exactly the `ZMod` pairing for the cyclic difference operator. -/
private theorem complex_cycle_pairing_reindex_to_zmod
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (z : ℕ → ℂ) (hz : z n = z 0) :
    let f : ZMod n → ℂ := fun j ↦ z j.val
    let Δ : ZMod n → ℂ := fun j ↦ f (j + 1) - f j
    Finset.sum (Finset.range n)
        (fun i ↦ Complex.im ((z (i + 1) - z i) * (starRingEnd ℂ) (z i))) =
      ∑ j : ZMod n, Complex.im (Δ j * (starRingEnd ℂ) (f j)) := by
  let f : ZMod n → ℂ := fun j ↦ z j.val
  let Δ : ZMod n → ℂ := fun j ↦ f (j + 1) - f j
  change Finset.sum (Finset.range n)
        (fun i ↦ Complex.im ((z (i + 1) - z i) * (starRingEnd ℂ) (z i))) =
      ∑ j : ZMod n, Complex.im (Δ j * (starRingEnd ℂ) (f j))
  rcases n with _ | _ | n
  · cases NeZero.ne 0 rfl
  · omega
  · change Finset.sum (Finset.range (n + 2))
          (fun i ↦ Complex.im ((z (i + 1) - z i) * (starRingEnd ℂ) (z i))) =
        ∑ i : Fin (n + 2), Complex.im (Δ i * (starRingEnd ℂ) (f i))
    rw [Finset.sum_fin_eq_sum_range]
    -- Compare each natural-indexed edge with the corresponding successor edge on the cyclic group.
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs with hi0
    · by_cases hi' : i + 1 < n + 2
      · have hf : f ⟨i, hi0⟩ = z i := by
          rfl
        have hnext : ((⟨i, hi0⟩ : Fin (n + 2)) + 1).val = i + 1 := by
          simpa using (Fin.val_add_one_of_lt' (i := ⟨i, hi0⟩) hi')
        have hΔ : Δ ⟨i, hi0⟩ = z (i + 1) - z i := by
          change z (((⟨i, hi0⟩ : Fin (n + 2)) + 1).val) - z i = z (i + 1) - z i
          rw [hnext]
        rw [hf, hΔ]
      · have hlast : i = n + 1 := by
          omega
        subst hlast
        have hf : f ⟨n + 1, hi0⟩ = z (n + 1) := by
          rfl
        have hwrap : ((⟨n + 1, hi0⟩ : Fin (n + 2)) + 1).val = 0 := by
          rw [Fin.val_add]
          simp
        have hΔ : Δ ⟨n + 1, hi0⟩ = z 0 - z (n + 1) := by
          change z (((⟨n + 1, hi0⟩ : Fin (n + 2)) + 1).val) - z (n + 1) = z 0 - z (n + 1)
          rw [hwrap]
        -- The last successor edge wraps to `0`, and the closure hypothesis identifies it with
        -- the final natural edge of the polygon.
        calc
          Complex.im ((z (n + 2) - z (n + 1)) * (starRingEnd ℂ) (z (n + 1)))
              = Complex.im ((z 0 - z (n + 1)) * (starRingEnd ℂ) (z (n + 1))) := by
                  simp [hz]
          _ = Complex.im (Δ ⟨n + 1, hi0⟩ * (starRingEnd ℂ) (f ⟨n + 1, hi0⟩)) := by
                rw [hf, hΔ]
    · have : i < n + 2 := Finset.mem_range.mp hi
      omega

/-- Helper for Remark 22.16: after transporting a closed complex cycle to `ZMod n`, the total
edge energy is exactly the `ZMod` norm-square sum of the cyclic difference operator. -/
private theorem complex_cycle_edge_energy_reindex_to_zmod
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (z : ℕ → ℂ) (hz : z n = z 0) :
    let f : ZMod n → ℂ := fun j ↦ z j.val
    let Δ : ZMod n → ℂ := fun j ↦ f (j + 1) - f j
    Finset.sum (Finset.range n) (fun i ↦ Complex.normSq (z (i + 1) - z i)) =
      ∑ j : ZMod n, Complex.normSq (Δ j) := by
  let f : ZMod n → ℂ := fun j ↦ z j.val
  let Δ : ZMod n → ℂ := fun j ↦ f (j + 1) - f j
  change Finset.sum (Finset.range n) (fun i ↦ Complex.normSq (z (i + 1) - z i)) =
      ∑ j : ZMod n, Complex.normSq (Δ j)
  rcases n with _ | _ | n
  · cases NeZero.ne 0 rfl
  · omega
  · change Finset.sum (Finset.range (n + 2)) (fun i ↦ Complex.normSq (z (i + 1) - z i)) =
        ∑ i : Fin (n + 2), Complex.normSq (Δ i)
    rw [Finset.sum_fin_eq_sum_range]
    -- The same endpoint bookkeeping identifies the natural edge energies with the cyclic ones.
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs with hi0
    · by_cases hi' : i + 1 < n + 2
      · have hnext : ((⟨i, hi0⟩ : Fin (n + 2)) + 1).val = i + 1 := by
          simpa using (Fin.val_add_one_of_lt' (i := ⟨i, hi0⟩) hi')
        have hΔ : Δ ⟨i, hi0⟩ = z (i + 1) - z i := by
          change z (((⟨i, hi0⟩ : Fin (n + 2)) + 1).val) - z i = z (i + 1) - z i
          rw [hnext]
        rw [hΔ]
      · have hlast : i = n + 1 := by
          omega
        subst hlast
        have hwrap : ((⟨n + 1, hi0⟩ : Fin (n + 2)) + 1).val = 0 := by
          rw [Fin.val_add]
          simp
        have hΔ : Δ ⟨n + 1, hi0⟩ = z 0 - z (n + 1) := by
          change z (((⟨n + 1, hi0⟩ : Fin (n + 2)) + 1).val) - z (n + 1) = z 0 - z (n + 1)
          rw [hwrap]
        -- The terminal natural edge is the wrapped successor edge on `ZMod n`.
        calc
          Complex.normSq (z (n + 2) - z (n + 1)) = Complex.normSq (z 0 - z (n + 1)) := by
            simp [hz]
          _ = Complex.normSq (Δ ⟨n + 1, hi0⟩) := by
            rw [hΔ]
    · have : i < n + 2 := Finset.mem_range.mp hi
      omega

/-- Helper for Remark 22.16: the imaginary part of a single Fourier mode is the expected sine
coefficient. -/
private theorem stdAddChar_sub_one_im_eq_sin_double
    {n : ℕ} [NeZero n] (k : ZMod n) :
    Complex.im (ZMod.stdAddChar k - 1) =
      Real.sin (2 * (Real.pi * (k.val : ℝ) / (n : ℝ))) := by
  -- Expand the additive character into a complex exponential and read off its imaginary part.
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  have hscalar :
      ((((2 * (Real.pi * (k.val : ℝ) / (n : ℝ))) : ℝ) : ℂ)) =
        2 * (Real.pi : ℂ) * (k.val : ℂ) / (n : ℂ) := by
    have hscalar_real :
        2 * (Real.pi * (k.val : ℝ) / (n : ℝ)) =
          2 * Real.pi * (k.val : ℝ) / (n : ℝ) := by
      ring
    exact_mod_cast hscalar_real
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (n : ℂ) =
        (((2 * (Real.pi * (k.val : ℝ) / (n : ℝ))) : ℝ) : ℂ) * Complex.I := by
    calc
      2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (n : ℂ)
          = (2 * (Real.pi : ℂ) * (k.val : ℂ) / (n : ℂ)) * Complex.I := by
              ring
      _ = (((2 * (Real.pi * (k.val : ℝ) / (n : ℝ))) : ℝ) : ℂ) * Complex.I := by
            rw [hscalar]
  rw [harg]
  calc
    Complex.im
        (Complex.exp ((((2 * (Real.pi * (k.val : ℝ) / (n : ℝ))) : ℝ) : ℂ) * Complex.I) - 1)
        = Complex.im
            (Complex.exp ((((2 * (Real.pi * (k.val : ℝ) / (n : ℝ))) : ℝ) : ℂ) * Complex.I)) := by
              simp
    _ = Real.sin (2 * (Real.pi * (k.val : ℝ) / (n : ℝ))) := by
          simpa using Complex.exp_ofReal_mul_I_im (2 * (Real.pi * (k.val : ℝ) / (n : ℝ)))

/-- Helper for Remark 22.16: the norm-square of a single Fourier difference multiplier is the
expected quadratic sine coefficient. -/
private theorem stdAddChar_sub_one_normSq_eq_four_mul_sin_sq
    {n : ℕ} [NeZero n] (k : ZMod n) :
    Complex.normSq (ZMod.stdAddChar k - 1) =
      4 * Real.sin (Real.pi * (k.val : ℝ) / (n : ℝ)) ^ 2 := by
  -- Expand the unit complex number into cosine and sine coordinates, then simplify the norm.
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  have hscalar :
      ((((2 * (Real.pi * (k.val : ℝ) / (n : ℝ))) : ℝ) : ℂ)) =
        2 * (Real.pi : ℂ) * (k.val : ℂ) / (n : ℂ) := by
    have hscalar_real :
        2 * (Real.pi * (k.val : ℝ) / (n : ℝ)) =
          2 * Real.pi * (k.val : ℝ) / (n : ℝ) := by
      ring
    exact_mod_cast hscalar_real
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (n : ℂ) =
        (((2 * (Real.pi * (k.val : ℝ) / (n : ℝ))) : ℝ) : ℂ) * Complex.I := by
    calc
      2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (n : ℂ)
          = (2 * (Real.pi : ℂ) * (k.val : ℂ) / (n : ℂ)) * Complex.I := by
              ring
      _ = (((2 * (Real.pi * (k.val : ℝ) / (n : ℝ))) : ℝ) : ℂ) * Complex.I := by
            rw [hscalar]
  rw [harg, Complex.normSq_eq_norm_sq]
  have hnorm :
      ‖Complex.exp ((((2 * (Real.pi * (k.val : ℝ) / (n : ℝ))) : ℝ) : ℂ) * Complex.I) - 1‖ =
        ‖2 * Real.sin ((2 * (Real.pi * (k.val : ℝ) / (n : ℝ))) / 2)‖ := by
    simpa [mul_comm] using
      Complex.norm_exp_I_mul_ofReal_sub_one (2 * (Real.pi * (k.val : ℝ) / (n : ℝ)))
  rw [hnorm, Real.norm_eq_abs, sq_abs]
  have hhalf : (2 * (Real.pi * (k.val : ℝ) / (n : ℝ))) / 2 =
      Real.pi * (k.val : ℝ) / (n : ℝ) := by
    ring
  rw [hhalf]
  ring

/-- Helper for Remark 22.16: each Fourier coefficient satisfies the sharp cotangent bound from the
source spectral argument. -/
private theorem stdAddChar_sub_one_im_le_cot_normSq
    {n : ℕ} (hn : 2 ≤ n) [NeZero n] (k : ZMod n) :
    Complex.im (ZMod.stdAddChar k - 1) ≤
      (Real.cot (Real.pi / (n : ℝ)) / 2) * Complex.normSq (ZMod.stdAddChar k - 1) := by
  let α : ℝ := Real.pi / (n : ℝ)
  let t : ℝ := Real.pi * (k.val : ℝ) / (n : ℝ)
  have hn_real : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    linarith
  have hα_pos : 0 < α := by
    dsimp [α]
    positivity
  have hα_lt_pi : α < Real.pi := by
    -- The base angle `π / n` lies strictly inside `(0, π)` once `n ≥ 2`.
    dsimp [α]
    field_simp [hn_pos.ne']
    nlinarith [Real.pi_pos, hn_real]
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have ht_le_pi_sub_alpha : t ≤ Real.pi - α := by
    -- The mode parameter `k.val / n` always stays in the half-open interval `[0, 1)`.
    have hk_succ_le : (k.val : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt k.val_lt
    dsimp [t, α]
    field_simp [hn_pos.ne']
    nlinarith [Real.pi_pos, hk_succ_le]
  rw [stdAddChar_sub_one_im_eq_sin_double, stdAddChar_sub_one_normSq_eq_four_mul_sin_sq]
  change Real.sin (2 * t) ≤ (Real.cot α / 2) * (4 * Real.sin t ^ 2)
  by_cases hk : k = 0
  · -- The zero Fourier mode is trivial because both coefficients vanish.
    simpa [t, hk]
  · have hkval_pos_nat : 0 < k.val := by
      refine Nat.pos_of_ne_zero ?_
      intro hkval_zero
      apply hk
      simpa [hkval_zero] using (ZMod.natCast_zmod_val k).symm
    have hkval_pos : 0 < (k.val : ℝ) := by
      exact_mod_cast hkval_pos_nat
    have hα_le_t : α ≤ t := by
      -- Nonzero modes start at the first step `π / n`.
      have hkval_one_le : (1 : ℝ) ≤ (k.val : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hkval_pos_nat
      dsimp [t, α]
      field_simp [hn_pos.ne']
      nlinarith [Real.pi_pos, hkval_one_le]
    have hsinα_pos : 0 < Real.sin α := by
      exact Real.sin_pos_of_mem_Ioo ⟨hα_pos, hα_lt_pi⟩
    have hsin_t_nonneg : 0 ≤ Real.sin t := by
      have ht_le_pi : t ≤ Real.pi := by
        linarith [ht_le_pi_sub_alpha, hα_pos]
      exact Real.sin_nonneg_of_nonneg_of_le_pi ht_nonneg ht_le_pi
    have hsin_t_sub_nonneg : 0 ≤ Real.sin (t - α) := by
      have ht_sub_nonneg : 0 ≤ t - α := sub_nonneg.mpr hα_le_t
      have ht_sub_le_pi : t - α ≤ Real.pi := by
        linarith [ht_le_pi_sub_alpha, hα_pos]
      exact Real.sin_nonneg_of_nonneg_of_le_pi ht_sub_nonneg ht_sub_le_pi
    have hproduct_nonneg : 0 ≤ 2 * Real.sin t * Real.sin (t - α) := by
      nlinarith
    have hdifference_mul_nonneg :
        0 ≤ ((Real.cot α / 2) * (4 * Real.sin t ^ 2) - Real.sin (2 * t)) * Real.sin α := by
      -- Rewrite the coefficient gap into `2 sin t sin (t - α)`.
      calc
        0 ≤ 2 * Real.sin t * Real.sin (t - α) := hproduct_nonneg
        _ = ((Real.cot α / 2) * (4 * Real.sin t ^ 2) - Real.sin (2 * t)) * Real.sin α := by
              rw [Real.sin_two_mul, Real.cot_eq_cos_div_sin, Real.sin_sub]
              field_simp [hsinα_pos.ne']
              ring
    have hdifference_nonneg :
        0 ≤ (Real.cot α / 2) * (4 * Real.sin t ^ 2) - Real.sin (2 * t) := by
      have hdifference_mul_nonneg' :
          0 ≤ Real.sin α * ((Real.cot α / 2) * (4 * Real.sin t ^ 2) - Real.sin (2 * t)) := by
        simpa [mul_comm] using hdifference_mul_nonneg
      exact nonneg_of_mul_nonneg_right hdifference_mul_nonneg' hsinα_pos
    linarith

/-- Helper for Remark 22.16: the only remaining structural input is the sharp cotangent bound for
closed complex cycles. -/
private theorem complex_cycle_im_le_cot_edge_energy
    {n : ℕ} (hn : 2 ≤ n) (z : ℕ → ℂ) (hz : z n = z 0) :
    Finset.sum (Finset.range n)
        (fun i ↦ Complex.im ((z (i + 1) - z i) * (starRingEnd ℂ) (z i))) ≤
      (Real.cot (Real.pi / (n : ℝ)) / 2) *
        (Finset.sum (Finset.range n) (fun i ↦ Complex.normSq (z (i + 1) - z i))) := by
  have hpos : 0 < n := by
    linarith
  let f : ZMod n → ℂ := fun j ↦ z j.val
  let Δ : ZMod n → ℂ := fun j ↦ f (j + 1) - f j
  haveI : NeZero n := ⟨Nat.ne_of_gt hpos⟩
  have hpair :
      Finset.sum (Finset.range n)
          (fun i ↦ Complex.im ((z (i + 1) - z i) * (starRingEnd ℂ) (z i))) =
        ∑ j : ZMod n, Complex.im (Δ j * (starRingEnd ℂ) (f j)) := by
    -- First move the defect sum from `Nat` indices to the cyclic successor operator on `ZMod n`.
    simpa [f, Δ] using complex_cycle_pairing_reindex_to_zmod (n := n) hn z hz
  have henergy :
      Finset.sum (Finset.range n) (fun i ↦ Complex.normSq (z (i + 1) - z i)) =
        ∑ j : ZMod n, Complex.normSq (Δ j) := by
    -- The same reindexing turns the edge-energy sum into the norm-square of the cyclic
    -- difference operator.
    simpa [f, Δ] using complex_cycle_edge_energy_reindex_to_zmod (n := n) hn z hz
  have hpairFreq :
      ∑ j : ZMod n, Δ j * (starRingEnd ℂ) (f j) =
        ((n : ℂ)⁻¹) * ∑ k : ZMod n, (ZMod.stdAddChar k - 1) * (Complex.normSq (ZMod.dft f k) : ℂ) := by
    -- The mixed Parseval identity turns the defect pairing into a weighted mode sum.
    simpa [f, Δ] using zmod_difference_pairing_eq_frequency_sum (n := n) f
  have henergyFreq :
      ∑ j : ZMod n, Complex.normSq (Δ j) =
        ((n : ℝ)⁻¹) * ∑ k : ZMod n,
          Complex.normSq (ZMod.stdAddChar k - 1) * Complex.normSq (ZMod.dft f k) := by
    -- The same Parseval package identifies the total edge energy with the modewise multiplier norm.
    simpa [f, Δ] using zmod_difference_energy_eq_frequency_sum (n := n) f
  let imAddHom : ℂ →+ ℝ := AddMonoidHom.mk' Complex.im Complex.add_im
  rw [hpair, henergy]
  rw [show ∑ j : ZMod n, Complex.im (Δ j * (starRingEnd ℂ) (f j)) =
      imAddHom (∑ j : ZMod n, Δ j * (starRingEnd ℂ) (f j)) by
        simp [imAddHom, map_sum]]
  rw [hpairFreq, henergyFreq]
  change Complex.im
      (((n : ℂ)⁻¹) *
        ∑ k : ZMod n, (ZMod.stdAddChar k - 1) * (Complex.normSq (ZMod.dft f k) : ℂ)) ≤
    (Real.cot (Real.pi / (n : ℝ)) / 2) *
      (((n : ℝ)⁻¹) *
        ∑ k : ZMod n,
          Complex.normSq (ZMod.stdAddChar k - 1) * Complex.normSq (ZMod.dft f k))
  have him_sum :
      Complex.im
          (((n : ℂ)⁻¹) *
            ∑ k : ZMod n, (ZMod.stdAddChar k - 1) * (Complex.normSq (ZMod.dft f k) : ℂ)) =
        (n : ℝ)⁻¹ *
          ∑ k : ZMod n, Complex.im (ZMod.stdAddChar k - 1) * Complex.normSq (ZMod.dft f k) := by
    -- The Parseval factor `(n : ℂ)⁻¹` and the Fourier weights are real scalars.
    calc
      Complex.im
          (((n : ℂ)⁻¹) *
            ∑ k : ZMod n, (ZMod.stdAddChar k - 1) * (Complex.normSq (ZMod.dft f k) : ℂ))
          = Complex.re ((n : ℂ)⁻¹) *
              Complex.im
                (∑ k : ZMod n, (ZMod.stdAddChar k - 1) * (Complex.normSq (ZMod.dft f k) : ℂ)) +
              Complex.im ((n : ℂ)⁻¹) *
                Complex.re
                  (∑ k : ZMod n, (ZMod.stdAddChar k - 1) * (Complex.normSq (ZMod.dft f k) : ℂ)) := by
              rw [Complex.mul_im]
      _ = (n : ℝ)⁻¹ *
            Complex.im
              (∑ k : ZMod n, (ZMod.stdAddChar k - 1) * (Complex.normSq (ZMod.dft f k) : ℂ)) := by
            simp
      _ = (n : ℝ)⁻¹ *
            ∑ k : ZMod n,
              Complex.im ((ZMod.stdAddChar k - 1) * (Complex.normSq (ZMod.dft f k) : ℂ)) := by
            rw [show Complex.im
                (∑ k : ZMod n, (ZMod.stdAddChar k - 1) * (Complex.normSq (ZMod.dft f k) : ℂ)) =
                  imAddHom
                    (∑ k : ZMod n, (ZMod.stdAddChar k - 1) * (Complex.normSq (ZMod.dft f k) : ℂ))
                by rfl]
            simp [imAddHom, map_sum]
      _ = (n : ℝ)⁻¹ *
            ∑ k : ZMod n, Complex.im (ZMod.stdAddChar k - 1) * Complex.normSq (ZMod.dft f k) := by
            congr 1
            apply Finset.sum_congr rfl
            intro k hk
            rw [Complex.mul_im]
            simp [mul_assoc, mul_left_comm, mul_comm]
  have hmode_le :
      ∑ k : ZMod n, Complex.im (ZMod.stdAddChar k - 1) * Complex.normSq (ZMod.dft f k) ≤
        (Real.cot (Real.pi / (n : ℝ)) / 2) *
          ∑ k : ZMod n, Complex.normSq (ZMod.stdAddChar k - 1) * Complex.normSq (ZMod.dft f k) := by
    -- Compare the spectral coefficients modewise and then sum against the nonnegative weights.
    calc
      ∑ k : ZMod n, Complex.im (ZMod.stdAddChar k - 1) * Complex.normSq (ZMod.dft f k)
          ≤ ∑ k : ZMod n,
              ((Real.cot (Real.pi / (n : ℝ)) / 2) * Complex.normSq (ZMod.stdAddChar k - 1)) *
                Complex.normSq (ZMod.dft f k) := by
                refine Finset.sum_le_sum ?_
                intro k hk
                exact mul_le_mul_of_nonneg_right
                  (stdAddChar_sub_one_im_le_cot_normSq (n := n) hn k)
                  (Complex.normSq_nonneg _)
      _ = ∑ k : ZMod n,
            (Real.cot (Real.pi / (n : ℝ)) / 2) *
              (Complex.normSq (ZMod.stdAddChar k - 1) * Complex.normSq (ZMod.dft f k)) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = (Real.cot (Real.pi / (n : ℝ)) / 2) *
            ∑ k : ZMod n, Complex.normSq (ZMod.stdAddChar k - 1) * Complex.normSq (ZMod.dft f k) := by
            rw [Finset.mul_sum]
  have hinv_nonneg : 0 ≤ (n : ℝ)⁻¹ := by
    positivity
  -- Route correction: the Fourier reduction is fixed, so the proof now closes by summing the
  -- sharp scalar mode bound against the nonnegative Parseval weights.
  calc
    Complex.im
        (((n : ℂ)⁻¹) *
          ∑ k : ZMod n, (ZMod.stdAddChar k - 1) * (Complex.normSq (ZMod.dft f k) : ℂ))
        = (n : ℝ)⁻¹ *
            ∑ k : ZMod n, Complex.im (ZMod.stdAddChar k - 1) * Complex.normSq (ZMod.dft f k) := by
            exact him_sum
    _ ≤ (n : ℝ)⁻¹ *
          ((Real.cot (Real.pi / (n : ℝ)) / 2) *
            ∑ k : ZMod n, Complex.normSq (ZMod.stdAddChar k - 1) * Complex.normSq (ZMod.dft f k)) := by
          exact mul_le_mul_of_nonneg_left hmode_le hinv_nonneg
    _ = (Real.cot (Real.pi / (n : ℝ)) / 2) *
          (((n : ℝ)⁻¹) *
            ∑ k : ZMod n, Complex.normSq (ZMod.stdAddChar k - 1) * Complex.normSq (ZMod.dft f k)) := by
          ring

private theorem quarter_turn_cycle_sum_le_cot_edge_energy
    {n : ℕ} (hn : 2 ≤ n) (x : ℕ → ℝ²) (hx : x n = x 0) :
    Finset.sum (Finset.range n) (fun i ↦ ⟪x (i + 1) - x i, quarterTurnOperator (x i)⟫_ℝ) ≤
      (Real.cot (Real.pi / (n : ℝ)) / 2) *
        (Finset.sum (Finset.range n) (fun i ↦ ‖x (i + 1) - x i‖ ^ 2)) := by
  -- Move the closed polygon to `ℂ`; after this transport, only the sharp complex cycle inequality
  -- remains, and all real-coordinate bookkeeping has been eliminated.
  let z : ℕ → ℂ := fun i ↦ euclideanToComplex (x i)
  have hz : z n = z 0 := by
    simpa [z] using complex_cycle_closed_of_real_cycle_closed x hx
  rw [complex_cycle_quarter_turn_sum_eq, complex_cycle_edge_energy_sum_eq]
  simpa [z] using complex_cycle_im_le_cot_edge_energy hn z hz

/-- Helper for Remark 22.16: the sign of the coefficient produced by the structural bound is
exactly the angle condition `θ ≤ π / n`. -/
private theorem rotation_angle_coefficient_nonpos_iff
    {θ : ℝ} {n : ℕ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) (hn : 2 ≤ n) :
    Real.sin θ * Real.cot (Real.pi / (n : ℝ)) - Real.cos θ ≤ 0 ↔
      θ ≤ Real.pi / (n : ℝ) := by
  let α : ℝ := Real.pi / (n : ℝ)
  have hn_real : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    linarith
  have hα_pos : 0 < α := by
    positivity
  have hα_le_pi_div_two : α ≤ Real.pi / 2 := by
    dsimp [α]
    field_simp [hn_pos.ne']
    nlinarith [Real.pi_pos, hn_real]
  have hα_lt_pi : α < Real.pi := by
    dsimp [α]
    field_simp [hn_pos.ne']
    nlinarith [Real.pi_pos, hn_real]
  have hsinα_pos : 0 < Real.sin α := by
    exact Real.sin_pos_of_mem_Ioo ⟨hα_pos, hα_lt_pi⟩
  have hcoeff_mul :
      (Real.sin θ * Real.cot α - Real.cos θ) * Real.sin α = Real.sin (θ - α) := by
    -- Convert the cotangent coefficient into the sine subtraction formula.
    calc
      (Real.sin θ * Real.cot α - Real.cos θ) * Real.sin α
          = Real.sin θ * Real.cos α - Real.cos θ * Real.sin α := by
              rw [Real.cot_eq_cos_div_sin]
              field_simp [hsinα_pos.ne']
      _ = Real.sin (θ - α) := by
            rw [Real.sin_sub]
  constructor
  · intro hcoeff
    have hsin_nonpos : Real.sin (θ - α) ≤ 0 := by
      have hmul_nonpos :
          (Real.sin θ * Real.cot α - Real.cos θ) * Real.sin α ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg hcoeff (le_of_lt hsinα_pos)
      simpa [hcoeff_mul] using hmul_nonpos
    have hsub_mem : θ - α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · linarith [hθ.1, hα_le_pi_div_two]
      · linarith [hθ.2, hα_pos]
    have hzero_mem : (0 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith [Real.pi_pos]
    have hsub_le_zero : θ - α ≤ 0 := by
      have hsin_le_zero : Real.sin (θ - α) ≤ Real.sin 0 := by
        simpa using hsin_nonpos
      exact (Real.strictMonoOn_sin.le_iff_le hsub_mem hzero_mem).1 hsin_le_zero
    simpa [α] using hsub_le_zero
  · intro hθα
    have hsub_nonpos : θ - α ≤ 0 := by
      linarith
    have hsub_neg_pi_le : -Real.pi ≤ θ - α := by
      linarith [hθ.1, hα_le_pi_div_two]
    have hsin_nonpos : Real.sin (θ - α) ≤ 0 := by
      exact Real.sin_nonpos_of_nonpos_of_neg_pi_le hsub_nonpos hsub_neg_pi_le
    have hmul_nonpos :
        (Real.sin θ * Real.cot α - Real.cos θ) * Real.sin α ≤ 0 := by
      simpa [hcoeff_mul] using hsin_nonpos
    have hmul_nonpos' :
        Real.sin α * (Real.sin θ * Real.cot α - Real.cos θ) ≤ 0 := by
      simpa [mul_comm] using hmul_nonpos
    exact nonpos_of_mul_nonpos_right hmul_nonpos' hsinα_pos

/-- Helper for Remark 22.16: the regular `n`-gon is the sharp witness for the reverse
implication, producing the exact sine defect. -/
private theorem regular_ngon_rotation_cycle_sum_eq
    {θ : ℝ} {n : ℕ} (hn : 2 ≤ n) :
    ∃ x : ℕ → ℝ²,
      x n = x 0 ∧
        Finset.sum (Finset.range n)
            (fun i ↦ ⟪x (i + 1) - x i, counterclockwiseOrientation.rotation θ (x i)⟫_ℝ) =
          2 * (n : ℝ) * Real.sin (Real.pi / (n : ℝ)) *
            Real.sin (θ - Real.pi / (n : ℝ)) := by
  let α : ℝ := 2 * Real.pi / (n : ℝ)
  let x : ℕ → ℝ² := fun i ↦ !₂[Real.cos ((i : ℝ) * α), Real.sin ((i : ℝ) * α)]
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hn
  have hα_half : α / 2 = Real.pi / (n : ℝ) := by
    dsimp [α]
    field_simp [hn_real_pos.ne']
  have hα_succ (i : ℕ) : ((i + 1 : ℕ) : ℝ) * α = (i : ℝ) * α + α := by
    norm_num
    ring
  refine ⟨x, ?_, ?_⟩
  · -- The regular `n`-gon closes because the total turning angle is `2π`.
    have hαn : (n : ℝ) * α = 2 * Real.pi := by
      dsimp [α]
      field_simp [hn_real_pos.ne']
    dsimp [x]
    rw [hαn]
    simp [Real.cos_two_pi, Real.sin_two_pi]
  · let term : ℕ → ℝ := fun i ↦
      ⟪x (i + 1) - x i, counterclockwiseOrientation.rotation θ (x i)⟫_ℝ
    have hterm_const :
        ∀ i,
          term i = Real.cos (θ - α) - Real.cos θ := by
      intro i
      -- Expand the regular `n`-gon coordinates and cancel the dependence on the vertex index.
      dsimp [term, x]
      rw [hα_succ i]
      simp [counterclockwiseRotation_apply, PiLp.inner_apply, Fin.sum_univ_two,
        Real.cos_add, Real.sin_add, Real.cos_sub]
      rw [real_inner_eq_mul, real_inner_eq_mul]
      ring_nf
      symm
      have hsq :
          Real.cos ((i : ℝ) * α) ^ 2 + Real.sin ((i : ℝ) * α) ^ 2 = 1 := by
        simpa [add_comm] using Real.sin_sq_add_cos_sq ((i : ℝ) * α)
      calc
        Real.cos α * Real.cos θ + Real.sin α * Real.sin θ - Real.cos θ
            = Real.cos (θ - α) - Real.cos θ := by
                have hcos :
                    Real.cos (θ - α) - Real.cos θ =
                      Real.cos θ * Real.cos α + Real.sin θ * Real.sin α - Real.cos θ := by
                  rw [Real.cos_sub]
                simpa [mul_comm, mul_left_comm, mul_assoc] using hcos.symm
        _ = (Real.cos ((i : ℝ) * α) ^ 2 + Real.sin ((i : ℝ) * α) ^ 2) *
              (Real.cos α * Real.cos θ + Real.sin α * Real.sin θ - Real.cos θ) := by
                rw [hsq]
                have hcos :
                    Real.cos (θ - α) - Real.cos θ =
                      Real.cos θ * Real.cos α + Real.sin θ * Real.sin α - Real.cos θ := by
                  rw [Real.cos_sub]
                rw [hcos]
                ring
        _ = Real.cos (↑i * α) ^ 2 * Real.cos α * Real.cos θ +
              Real.cos (↑i * α) ^ 2 * Real.sin α * Real.sin θ -
            Real.cos (↑i * α) ^ 2 * Real.cos θ +
          Real.cos α * Real.sin (↑i * α) ^ 2 * Real.cos θ +
            Real.sin (↑i * α) ^ 2 * Real.sin α * Real.sin θ -
              Real.sin (↑i * α) ^ 2 * Real.cos θ := by
                ring
    have hconst :
        Real.cos (θ - α) - Real.cos θ =
          2 * Real.sin (Real.pi / (n : ℝ)) * Real.sin (θ - Real.pi / (n : ℝ)) := by
      rw [Real.cos_sub_cos]
      have hsum : ((θ - α) + θ) / 2 = θ - α / 2 := by
        ring
      have hdiff : ((θ - α) - θ) / 2 = -(α / 2) := by
        ring
      rw [hsum, hdiff, hα_half, Real.sin_neg]
      ring
    -- Each edge contributes the same amount, so the full cycle sum is `n` times the base defect.
    calc
      Finset.sum (Finset.range n)
          (fun i ↦ ⟪x (i + 1) - x i, counterclockwiseOrientation.rotation θ (x i)⟫_ℝ)
          = Finset.sum (Finset.range n) term := by
              rfl
      _ = Finset.sum (Finset.range n) (fun _ ↦ Real.cos (θ - α) - Real.cos θ) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hterm_const i
      _ = (n : ℝ) * (Real.cos (θ - α) - Real.cos θ) := by
            simp
            ring
      _ = (n : ℝ) * (2 * Real.sin (Real.pi / (n : ℝ)) *
            Real.sin (θ - Real.pi / (n : ℝ))) := by
            rw [hconst]
      _ = 2 * (n : ℝ) * Real.sin (Real.pi / (n : ℝ)) *
            Real.sin (θ - Real.pi / (n : ℝ)) := by
            ring

/-- Remark 22.16 (2): if `θ ∈ [0, π / 2]` and `n ≥ 2`, then the counterclockwise rotator on
`ℝ²` through the angle `θ`, viewed as its associated singleton-valued set-valued operator, is
`n`-cyclically monotone if and only if `θ ∈ [0, π / n]`. -/
theorem counterclockwiseRotation_isNCyclicallyMonotone_iff
    {θ : ℝ} {n : ℕ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) (hn : 2 ≤ n) :
    SetValuedOperator.IsNCyclicallyMonotone
        ((counterclockwiseOrientation.rotation θ).toContinuousLinearMap.toSetValuedOperator) n ↔
      θ ∈ Set.Icc (0 : ℝ) (Real.pi / (n : ℝ)) := by
  let α : ℝ := Real.pi / (n : ℝ)
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hn
  have hα_pos : 0 < α := by
    positivity
  have hα_le_pi_div_two : α ≤ Real.pi / 2 := by
    have hn_real : (2 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    dsimp [α]
    field_simp [hn_real_pos.ne']
    nlinarith [Real.pi_pos, hn_real]
  have hsinθ_nonneg : 0 ≤ Real.sin θ := by
    exact Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  constructor
  · intro hrot
    rcases regular_ngon_rotation_cycle_sum_eq (θ := θ) hn with ⟨x, hx, hsum⟩
    -- Test the cyclic inequality on the regular polygon witness to recover the sharp angle bound.
    have hineq :=
      hrot.ineq
        x
        (fun i ↦ counterclockwiseOrientation.rotation θ (x i))
        (by
          intro i hi
          simp [Function.toSetValuedOperator_apply])
        hx
    rw [hsum] at hineq
    have hsinα_pos : 0 < Real.sin α := by
      have hα_lt_pi : α < Real.pi := by
        linarith [hα_le_pi_div_two, Real.pi_pos]
      exact Real.sin_pos_of_mem_Ioo ⟨hα_pos, hα_lt_pi⟩
    have hfactor_pos : 0 < 2 * (n : ℝ) * Real.sin α := by
      positivity
    have hsin_nonpos : Real.sin (θ - α) ≤ 0 := by
      have hineq' : (2 * (n : ℝ) * Real.sin α) * Real.sin (θ - α) ≤ 0 := by
        simpa [α, mul_assoc, mul_left_comm, mul_comm] using hineq
      exact nonpos_of_mul_nonpos_right hineq' hfactor_pos
    have hsub_mem : θ - α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · linarith [hθ.1, hα_le_pi_div_two]
      · linarith [hθ.2, hα_pos]
    have hzero_mem : (0 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith [Real.pi_pos]
    have hsub_le_zero : θ - α ≤ 0 := by
      have hsin_le_zero : Real.sin (θ - α) ≤ Real.sin 0 := by
        simpa using hsin_nonpos
      exact (Real.strictMonoOn_sin.le_iff_le hsub_mem hzero_mem).1 hsin_le_zero
    exact ⟨hθ.1, by simpa [α] using hsub_le_zero⟩
  · intro hangle
    refine ⟨hn, ?_⟩
    intro x u hu hx
    have hu_eq :
        ∀ i, i < n → u i = counterclockwiseOrientation.rotation θ (x i) := by
      intro i hi
      simpa [Function.toSetValuedOperator_apply] using hu i hi
    have hrewrite :
        Finset.sum (Finset.range n) (fun i ↦ ⟪x (i + 1) - x i, u i⟫_ℝ) =
          Finset.sum (Finset.range n)
            (fun i ↦ ⟪x (i + 1) - x i, counterclockwiseOrientation.rotation θ (x i)⟫_ℝ) := by
      -- On a singleton-valued graph, every admissible `u i` is forced to equal the rotation value.
      apply Finset.sum_congr rfl
      intro i hi
      rw [hu_eq i (Finset.mem_range.mp hi)]
    rw [hrewrite, rotation_cycle_sum_split θ x hx]
    let edgeEnergy : ℝ :=
      Finset.sum (Finset.range n) (fun i ↦ ‖x (i + 1) - x i‖ ^ 2)
    let quarterDefect : ℝ :=
      Finset.sum (Finset.range n) (fun i ↦ ⟪x (i + 1) - x i, quarterTurnOperator (x i)⟫_ℝ)
    have hquarter :
        quarterDefect ≤ (Real.cot α / 2) * edgeEnergy := by
      simpa [α, edgeEnergy, quarterDefect] using
        quarter_turn_cycle_sum_le_cot_edge_energy hn x hx
    have hcoeff_nonpos : Real.sin θ * Real.cot α - Real.cos θ ≤ 0 := by
      rw [rotation_angle_coefficient_nonpos_iff hθ hn]
      simpa [α] using hangle.2
    have hedge_nonneg : 0 ≤ edgeEnergy := by
      exact Finset.sum_nonneg fun i hi ↦ sq_nonneg ‖x (i + 1) - x i‖
    -- Use the sharp quarter-turn bound and then the sign of the resulting coefficient.
    have hupper :
        -(Real.cos θ / 2) * edgeEnergy + Real.sin θ * quarterDefect ≤
          -(Real.cos θ / 2) * edgeEnergy +
            Real.sin θ * ((Real.cot α / 2) * edgeEnergy) := by
      nlinarith [mul_le_mul_of_nonneg_left hquarter hsinθ_nonneg]
    have hcoeff_term :
        -(Real.cos θ / 2) * edgeEnergy +
            Real.sin θ * ((Real.cot α / 2) * edgeEnergy) ≤ 0 := by
      have hhalf_nonpos : (Real.sin θ * Real.cot α - Real.cos θ) / 2 ≤ 0 := by
        linarith
      have hmul_nonpos :
          ((Real.sin θ * Real.cot α - Real.cos θ) / 2) * edgeEnergy ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg hhalf_nonpos hedge_nonneg
      calc
        -(Real.cos θ / 2) * edgeEnergy + Real.sin θ * ((Real.cot α / 2) * edgeEnergy)
            = ((Real.sin θ * Real.cot α - Real.cos θ) / 2) * edgeEnergy := by
                ring
        _ ≤ 0 := hmul_nonpos
    linarith
