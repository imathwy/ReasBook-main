import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

/-- The cubic shear diffeomorphism `(x, y) ↦ (x, y + x^3)` of `ℝ²`. -/
def cubicShear : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) where
  toEquiv :=
    { toFun := fun p ↦ (p.1, p.2 + p.1 ^ 3)
      invFun := fun p ↦ (p.1, p.2 - p.1 ^ 3)
      left_inv := by
        intro p
        ext <;> simp
      right_inv := by
        intro p
        ext <;> simp }
  contMDiff_toFun := by
    -- The forward coordinate change is smooth because each component is a smooth polynomial map.
    exact
      ((contDiff_fst : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦ p.1).prodMk
        (contDiff_snd.add (contDiff_fst.pow 3))).contMDiff
  contMDiff_invFun := by
    -- The inverse coordinate change is smooth for the same reason.
    exact
      ((contDiff_fst : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦ p.1).prodMk
        (contDiff_snd.sub (contDiff_fst.pow 3))).contMDiff

/-- The forward map of `cubicShear` is the coordinate change `(x, y) ↦ (x, y + x^3)`. -/
@[simp] theorem cubicShear_apply (p : ℝ × ℝ) : cubicShear p = (p.1, p.2 + p.1 ^ 3) := rfl

/-- The inverse map of `cubicShear` is `(x̃, ỹ) ↦ (x̃, ỹ - x̃^3)`. -/
@[simp] theorem cubicShear_symm_apply (p : ℝ × ℝ) :
    cubicShear.symm p = (p.1, p.2 - p.1 ^ 3) := rfl

/-- Exercise 3.17: the coordinates `x̃ = x` and `ỹ = y + x^3` define a global smooth coordinate
system on `ℝ²`, equivalently the cubic shear and its inverse are smooth maps. -/
theorem cubicShear_globalSmoothCoordinates :
    ContDiff ℝ ∞ cubicShear ∧ ContDiff ℝ ∞ cubicShear.symm :=
  ⟨cubicShear.contDiff, cubicShear.symm.contDiff⟩

/-- Helper for Exercise 3.17: the base point `(1, 0)` is sent by the cubic shear to `(1, 1)`. -/
lemma cubicShear_basepoint_image : cubicShear ((1 : ℝ), (0 : ℝ)) = ((1 : ℝ), (1 : ℝ)) := by
  -- This is the concrete coordinate rewrite used at the end of the proof.
  norm_num [cubicShear_apply]

/-- Helper for Exercise 3.17: the inverse cubic shear has the expected Jacobian at every point. -/
lemma cubicShear_symm_hasFDerivAt (p : ℝ × ℝ) :
    HasFDerivAt cubicShear.symm
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ -
          (3 * p.1 ^ 2) • ContinuousLinearMap.fst ℝ ℝ ℝ))
      p := by
  -- Differentiate the two coordinate functions of `(x̃, ỹ) ↦ (x̃, ỹ - x̃^3)` separately.
  have hpow :
      HasFDerivAt (fun q : ℝ × ℝ ↦ q.1 ^ 3)
        ((3 * p.1 ^ 2) • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
      ((hasFDerivAt_fst : HasFDerivAt (fun q : ℝ × ℝ ↦ q.1)
          (ContinuousLinearMap.fst ℝ ℝ ℝ) p).pow 3)
  simpa [cubicShear_symm_apply] using
    ((hasFDerivAt_fst : HasFDerivAt (fun q : ℝ × ℝ ↦ q.1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) p).prodMk
      ((hasFDerivAt_snd : HasFDerivAt (fun q : ℝ × ℝ ↦ q.2)
          (ContinuousLinearMap.snd ℝ ℝ ℝ) p).sub hpow))

/-- Helper for Exercise 3.17: the inverse-shear Jacobian sends the horizontal basis vector to
`(1, -(3 x^2))`. -/
lemma cubicShear_symm_fderiv_apply_e1 (p : ℝ × ℝ) :
    (fderiv ℝ cubicShear.symm p) ((1 : ℝ), (0 : ℝ)) = ((1 : ℝ), -(3 * p.1 ^ 2)) := by
  -- Replace `fderiv` by the Jacobian computed above and apply the linear map to `(1, 0)`.
  rw [(cubicShear_symm_hasFDerivAt p).fderiv]
  simp

/-- At `p = (1, 0)`, the `x̃`-coordinate vector determined by the cubic-shear coordinates is not
the standard `x`-coordinate vector. -/
-- Proof sketch: compute the derivative of `cubicShear.symm (x̃, ỹ) = (x̃, ỹ - x̃^3)` at the
-- coordinate point `cubicShear (1, 0) = (1, 1)` and apply it to the standard basis vector
-- `(1, 0)`; the second component is `-3`, so the result is not `(1, 0)`.
theorem cubicShear_dx_tilde_ne_dx_at_p :
    (fderiv ℝ cubicShear.symm (cubicShear ((1 : ℝ), (0 : ℝ)))) ((1 : ℝ), (0 : ℝ)) ≠
      ((1 : ℝ), (0 : ℝ)) := by
  -- Rewrite the evaluation point to `(1, 1)` and then compute the image of the horizontal vector.
  rw [cubicShear_basepoint_image, cubicShear_symm_fderiv_apply_e1]
  intro h
  -- The second coordinate would force `-3 = 0`, which is impossible.
  have hsecond : (-(3 * (1 : ℝ) ^ 2) : ℝ) = 0 := congrArg Prod.snd h
  norm_num at hsecond
