import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap03.Sec03_14.Proposition_3_9
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_28.Proposition_5_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_57.Proposition_8_19

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open NormedSpace

noncomputable section

local notation "R2" => EuclideanSpace ℝ (Fin 2)

-- Domain sampling pass:
-- * primary domain: smooth vector fields on open submanifolds and their pushforwards by
--   diffeomorphisms;
-- * source-facing layer here: the positive-quadrant open submanifold together with the fields `X`,
--   `Y`, and their pushforwards from Problem 8-10;
-- * core/canonical owners sampled upstream before refinement:
--   `VectorField.mpullback` for pushforward along a diffeomorphism,
--   `mfderiv_open_subset_inclusion_isInvertible` for transporting ambient tangent vectors to an
--   open subtype, and `NormedSpace.fromTangentSpace` for Euclidean coordinate formulas;
-- * bridge/view layer here: ambient `ℝ²` coordinate expressions obtained by pushing intrinsic
--   tangent vectors forward along the open-subset inclusion.

/-- The open submanifold `M = {(x,y) : 0 < x and 0 < y}` from Problem 8-10. -/
def problem_8_10_M : TopologicalSpace.Opens R2 where
  carrier := {p : R2 | 0 < p 0 ∧ 0 < p 1}
  is_open' := by
    refine IsOpen.inter ?_ ?_
    · change IsOpen {p : R2 | 0 < p 0}
      exact isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0)
    · change IsOpen {p : R2 | 0 < p 1}
      exact isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1)

/-- Membership in `problem_8_10_M` is given by the inequalities `x > 0` and `y > 0`. -/
theorem mem_problem_8_10_M (p : R2) :
    p ∈ (problem_8_10_M : Set R2) ↔ 0 < p 0 ∧ 0 < p 1 := Iff.rfl

/-- The coordinate formula `F(x,y) = (xy, y/x)` preserves the positive quadrant. -/
theorem problem_8_10_F_mem_M (p : problem_8_10_M) :
    !₂[((p : R2) 0 * (p : R2) 1), ((p : R2) 1 / (p : R2) 0)] ∈
      (problem_8_10_M : Set R2) := by
  -- Both output coordinates are positive because `x` and `y` are positive on the source point.
  rcases p.2 with ⟨hx, hy⟩
  change 0 < (p : R2) 0 * (p : R2) 1 ∧ 0 < (p : R2) 1 / (p : R2) 0
  exact ⟨mul_pos hx hy, div_pos hy hx⟩

/-- The map `F : M → M` from Problem 8-10, written on the positive-quadrant subtype. -/
def problem_8_10_F (p : problem_8_10_M) : problem_8_10_M :=
  ⟨!₂[((p : R2) 0 * (p : R2) 1), ((p : R2) 1 / (p : R2) 0)], problem_8_10_F_mem_M p⟩

/-- The underlying `ℝ²`-valued coordinate formula for `problem_8_10_F`. -/
@[simp]
theorem problem_8_10_F_apply (p : problem_8_10_M) :
    ((problem_8_10_F p : problem_8_10_M) : R2) =
      !₂[((p : R2) 0 * (p : R2) 1), ((p : R2) 1 / (p : R2) 0)] := rfl

/-- The explicit inverse-coordinate formula `(u,v) ↦ (sqrt (u / v), sqrt (uv))` preserves the
positive quadrant. -/
theorem problem_8_10_F_inv_mem_M (q : problem_8_10_M) :
    !₂[Real.sqrt (((q : R2) 0) / ((q : R2) 1)), Real.sqrt (((q : R2) 0) * ((q : R2) 1))] ∈
      (problem_8_10_M : Set R2) := by
  -- The radicands are positive on the positive quadrant, so both square roots stay positive.
  rcases q.2 with ⟨hu, hv⟩
  have hdiv : 0 < ((q : R2) 0) / ((q : R2) 1) := div_pos hu hv
  have hmul : 0 < ((q : R2) 0) * ((q : R2) 1) := mul_pos hu hv
  change 0 < Real.sqrt (((q : R2) 0) / ((q : R2) 1)) ∧
      0 < Real.sqrt (((q : R2) 0) * ((q : R2) 1))
  exact ⟨Real.sqrt_pos.2 hdiv, Real.sqrt_pos.2 hmul⟩

/-- The inverse map `F⁻¹ : M → M` from Problem 8-10, written on the positive-quadrant subtype. -/
def problem_8_10_F_inv (q : problem_8_10_M) : problem_8_10_M :=
  ⟨!₂[Real.sqrt (((q : R2) 0) / ((q : R2) 1)), Real.sqrt (((q : R2) 0) * ((q : R2) 1))],
    problem_8_10_F_inv_mem_M q⟩

/-- The underlying `ℝ²`-valued coordinate formula for `problem_8_10_F_inv`. -/
@[simp]
theorem problem_8_10_F_inv_apply (q : problem_8_10_M) :
    ((problem_8_10_F_inv q : problem_8_10_M) : R2) =
      !₂[Real.sqrt (((q : R2) 0) / ((q : R2) 1)), Real.sqrt (((q : R2) 0) * ((q : R2) 1))] := rfl

/-- The explicit inverse formula is a left inverse for `problem_8_10_F`. -/
theorem problem_8_10_F_left_inv (p : problem_8_10_M) :
    problem_8_10_F_inv (problem_8_10_F p) = p := by
  rcases p.2 with ⟨hx, hy⟩
  have hx0 : (p : R2) 0 ≠ 0 := ne_of_gt hx
  have hy0 : (p : R2) 1 ≠ 0 := ne_of_gt hy
  apply Subtype.ext
  ext i
  fin_cases i
  · -- The first inverse coordinate collapses to `√(x^2)`, hence to `x` on the positive quadrant.
    have hsq :
        ((p : R2) 0 * (p : R2) 1) / (((p : R2) 1) / ((p : R2) 0)) = ((p : R2) 0) ^ (2 : ℕ) := by
      field_simp [hx0, hy0]
    simp [problem_8_10_F_apply, problem_8_10_F_inv_apply, hsq, Real.sqrt_sq_eq_abs, abs_of_pos hx]
  · -- The second inverse coordinate collapses to `√(y^2)`, hence to `y` on the positive quadrant.
    have hsq :
        ((p : R2) 0 * (p : R2) 1) * (((p : R2) 1) / ((p : R2) 0)) = ((p : R2) 1) ^ (2 : ℕ) := by
      field_simp [hx0]
    simp [problem_8_10_F_apply, problem_8_10_F_inv_apply, hsq, Real.sqrt_sq_eq_abs, abs_of_pos hy]

/-- The explicit inverse formula is a right inverse for `problem_8_10_F`. -/
theorem problem_8_10_F_right_inv (q : problem_8_10_M) :
    problem_8_10_F (problem_8_10_F_inv q) = q := by
  rcases q.2 with ⟨hu, hv⟩
  have hu0 : (q : R2) 0 ≠ 0 := ne_of_gt hu
  have hv0 : (q : R2) 1 ≠ 0 := ne_of_gt hv
  apply Subtype.ext
  ext i
  fin_cases i
  · -- Combine the two square roots into `√(u^2)` and use positivity of `u`.
    have hsq :
        (((q : R2) 0) / ((q : R2) 1)) * (((q : R2) 0) * ((q : R2) 1)) =
          ((q : R2) 0) ^ (2 : ℕ) := by
      field_simp [hv0]
    calc
      Real.sqrt (((q : R2) 0) / ((q : R2) 1)) * Real.sqrt (((q : R2) 0) * ((q : R2) 1))
          = Real.sqrt ((((q : R2) 0) / ((q : R2) 1)) * (((q : R2) 0) * ((q : R2) 1))) := by
              rw [← Real.sqrt_mul (show 0 ≤ ((q : R2) 0) / ((q : R2) 1) by positivity)]
      _ = Real.sqrt (((q : R2) 0) ^ (2 : ℕ)) := by rw [hsq]
      _ = (q : R2) 0 := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hu]
  · -- Rewrite the quotient of square roots as `√(v^2)` and use positivity of `v`.
    have hsq :
        (((q : R2) 0) * ((q : R2) 1)) / (((q : R2) 0) / ((q : R2) 1)) =
          ((q : R2) 1) ^ (2 : ℕ) := by
      field_simp [hu0, hv0]
    calc
      Real.sqrt (((q : R2) 0) * ((q : R2) 1)) / Real.sqrt (((q : R2) 0) / ((q : R2) 1))
          = Real.sqrt ((((q : R2) 0) * ((q : R2) 1)) / (((q : R2) 0) / ((q : R2) 1))) := by
              rw [← Real.sqrt_div (show 0 ≤ ((q : R2) 0) * ((q : R2) 1) by positivity)]
      _ = Real.sqrt (((q : R2) 1) ^ (2 : ℕ)) := by rw [hsq]
      _ = (q : R2) 1 := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hv]

/-- The ambient coordinate formula `F(x,y) = (xy, y / x)` from Problem 8-10. -/
private def problem_8_10_FAmbient (p : R2) : R2 :=
  !₂[p 0 * p 1, p 1 / p 0]

/-- The ambient coordinate formula for the inverse map `F⁻¹(u,v) = (√(u / v), √(uv))`. -/
private def problem_8_10_FInvAmbient (q : R2) : R2 :=
  !₂[Real.sqrt (q 0 / q 1), Real.sqrt (q 0 * q 1)]

/-- The forward coordinate map of Problem 8-10 is smooth on the positive quadrant. -/
theorem problem_8_10_F_contMDiff :
    ContMDiff (𝓡 2) (𝓡 2) ∞ problem_8_10_F := by
  let toR2 : (Fin 2 → ℝ) ≃L[ℝ] R2 :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm
  have h0 : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (fun p : problem_8_10_M ↦ (p : R2) 0) := by
    simpa [Function.comp] using
      ((PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0).contDiff.contMDiff.comp
        (contMDiff_subtype_val : ContMDiff (𝓡 2) (𝓡 2) ∞
          (Subtype.val : problem_8_10_M → R2)))
  have h1 : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (fun p : problem_8_10_M ↦ (p : R2) 1) := by
    simpa [Function.comp] using
      ((PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1).contDiff.contMDiff.comp
        (contMDiff_subtype_val : ContMDiff (𝓡 2) (𝓡 2) ∞
          (Subtype.val : problem_8_10_M → R2)))
  have hPi :
      ContMDiff (𝓡 2) 𝓘(ℝ, Fin 2 → ℝ) ∞
        (fun p : problem_8_10_M ↦
          fun i : Fin 2 ↦ (((problem_8_10_F p : problem_8_10_M) : R2) i)) := by
    refine contMDiff_pi_space.2 ?_
    intro i
    fin_cases i
    · -- The first coordinate is the product `x * y`.
      simpa [problem_8_10_F_apply] using h0.mul h1
    · -- The second coordinate is the quotient `y / x`, smooth because `x > 0` on the source.
      have hdiv :
          ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (fun p : problem_8_10_M ↦ (p : R2) 1 / (p : R2) 0) := by
        exact h1.div₀ h0 (fun p ↦ ne_of_gt p.property.1)
      simpa [problem_8_10_F_apply] using hdiv
  have hSub :
      ContMDiff (𝓡 2) (𝓡 2) ∞ ((Subtype.val : problem_8_10_M → R2) ∘ problem_8_10_F) := by
    refine (toR2.contDiff.contMDiff.comp hPi).congr ?_
    intro p
    simp [toR2, Function.comp, problem_8_10_F_apply]
  exact (ContMDiff.subtypeVal_comp_iff problem_8_10_M problem_8_10_F).1 hSub

/-- The inverse coordinate map of Problem 8-10 is smooth on the positive quadrant. -/
theorem problem_8_10_F_inv_contMDiff :
    ContMDiff (𝓡 2) (𝓡 2) ∞ problem_8_10_F_inv := by
  have h0 : ContDiffOn ℝ ∞ (fun q : R2 ↦ q 0) (problem_8_10_M : Set R2) := by
    simpa using (contDiffOn_piLp_apply (p := 2) (i := 0) (t := (problem_8_10_M : Set R2)))
  have h1 : ContDiffOn ℝ ∞ (fun q : R2 ↦ q 1) (problem_8_10_M : Set R2) := by
    simpa using (contDiffOn_piLp_apply (p := 2) (i := 1) (t := (problem_8_10_M : Set R2)))
  have hAmbientOn : ContDiffOn ℝ ∞ problem_8_10_FInvAmbient (problem_8_10_M : Set R2) := by
    rw [contDiffOn_piLp (p := 2)]
    intro i
    fin_cases i
    · -- The first inverse coordinate is `sqrt (u / v)`, smooth because `u / v > 0` on `M`.
      have hdiv : ContDiffOn ℝ ∞ (fun q : R2 ↦ q 0 / q 1) (problem_8_10_M : Set R2) := by
        exact h0.div h1 (fun q hq ↦ ne_of_gt ((mem_problem_8_10_M q).1 hq).2)
      exact hdiv.sqrt (fun q hq ↦ ne_of_gt (div_pos ((mem_problem_8_10_M q).1 hq).1
        ((mem_problem_8_10_M q).1 hq).2))
    · -- The second inverse coordinate is `sqrt (uv)`, smooth because `uv > 0` on `M`.
      have hmul : ContDiffOn ℝ ∞ (fun q : R2 ↦ q 0 * q 1) (problem_8_10_M : Set R2) := by
        exact h0.mul h1
      exact hmul.sqrt (fun q hq ↦ ne_of_gt (mul_pos ((mem_problem_8_10_M q).1 hq).1
        ((mem_problem_8_10_M q).1 hq).2))
  have hAmbientMDiffOn :
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ problem_8_10_FInvAmbient (problem_8_10_M : Set R2) :=
    hAmbientOn.contMDiffOn
  have hSub :
      ContMDiff (𝓡 2) (𝓡 2) ∞ (problem_8_10_FInvAmbient ∘ (Subtype.val : problem_8_10_M → R2)) := by
    -- Restrict the ambient inverse-coordinate map to the open subtype once the ambient smoothness
    -- on `M` is established.
    exact hAmbientMDiffOn.comp_contMDiff
      (contMDiff_subtype_val : ContMDiff (𝓡 2) (𝓡 2) ∞ (Subtype.val : problem_8_10_M → R2))
      (fun q ↦ q.property)
  have hComp :
      problem_8_10_FInvAmbient ∘ (Subtype.val : problem_8_10_M → R2) =
        (Subtype.val : problem_8_10_M → R2) ∘ problem_8_10_F_inv := by
    funext q
    simp [problem_8_10_FInvAmbient, problem_8_10_F_inv_apply]
  -- Reduce smoothness into the codomain subtype to the ambient inverse-coordinate formula.
  refine (ContMDiff.subtypeVal_comp_iff problem_8_10_M problem_8_10_F_inv).mp ?_
  rw [← hComp]
  exact hSub

/-- For Problem 8-10: the map `F(x,y) = (xy, y/x)` on the positive quadrant is a diffeomorphism. -/
def problem_8_10_diffeomorph : problem_8_10_M ≃ₘ⟮𝓡 2, 𝓡 2⟯ problem_8_10_M where
  toEquiv :=
    { toFun := problem_8_10_F
      invFun := problem_8_10_F_inv
      left_inv := problem_8_10_F_left_inv
      right_inv := problem_8_10_F_right_inv }
  contMDiff_toFun := problem_8_10_F_contMDiff
  contMDiff_invFun := problem_8_10_F_inv_contMDiff

/-- Applying `problem_8_10_diffeomorph` is the same as applying the forward map `problem_8_10_F`. -/
@[simp]
theorem problem_8_10_diffeomorph_apply (p : problem_8_10_M) :
    problem_8_10_diffeomorph p = problem_8_10_F p := rfl

/-- The ambient tangent vector for `X = x ∂/∂x + y ∂/∂y` at a positive-quadrant point. -/
private def problem_8_10_XAmbient (p : problem_8_10_M) : TangentSpace (𝓡 2) (p : R2) :=
  (fromTangentSpace (p : R2)).symm !₂[((p : R2) 0), ((p : R2) 1)]

/-- The vector field `X = x ∂/∂x + y ∂/∂y` on the positive quadrant, obtained by transporting its
ambient tangent vector through the open-subset inclusion. -/
def problem_8_10_X (p : problem_8_10_M) : TangentSpace (𝓡 2) p :=
  (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : problem_8_10_M → R2) p).inverse (problem_8_10_XAmbient p)

/-- Helper for Problem 8-10: applying the derivative of the open-subset inclusion to the inverse
image of an ambient tangent vector recovers the original ambient vector. -/
theorem problem_8_10_subtypeVal_mfderiv_inverse_apply
    (p : problem_8_10_M) (w : TangentSpace (𝓡 2) (p : R2)) :
    mfderiv (𝓡 2) (𝓡 2) (Subtype.val : problem_8_10_M → R2) p
      ((mfderiv (𝓡 2) (𝓡 2) (Subtype.val : problem_8_10_M → R2) p).inverse w) = w := by
  -- The inclusion of an open subtype has invertible derivative, so applying it cancels `.inverse`.
  simpa using
    (mfderiv_open_subset_inclusion_isInvertible (I := 𝓡 2) problem_8_10_M p).self_apply_inverse w

/-- In ambient coordinates, `problem_8_10_X` has the textbook components `(x, y)`. -/
theorem problem_8_10_X_formula (p : problem_8_10_M) :
    fromTangentSpace (p : R2)
      (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : problem_8_10_M → R2) p
        (problem_8_10_X p)) =
        !₂[((p : R2) 0), ((p : R2) 1)] := by
  -- Push `problem_8_10_X` through the open-subtype inclusion.
  -- Then read off its ambient coordinates.
  simpa [problem_8_10_X, problem_8_10_XAmbient] using
    congrArg (fromTangentSpace (p : R2))
      (problem_8_10_subtypeVal_mfderiv_inverse_apply p (problem_8_10_XAmbient p))

/-- The ambient tangent vector for `Y = y ∂/∂x` at a positive-quadrant point. -/
private def problem_8_10_YAmbient (p : problem_8_10_M) : TangentSpace (𝓡 2) (p : R2) :=
  (fromTangentSpace (p : R2)).symm !₂[((p : R2) 1), (0 : ℝ)]

/-- The vector field `Y = y ∂/∂x` on the positive quadrant, obtained by transporting its ambient
tangent vector through the open-subset inclusion. -/
def problem_8_10_Y (p : problem_8_10_M) : TangentSpace (𝓡 2) p :=
  (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : problem_8_10_M → R2) p).inverse (problem_8_10_YAmbient p)

/-- In ambient coordinates, `problem_8_10_Y` has the textbook components `(y, 0)`. -/
theorem problem_8_10_Y_formula (p : problem_8_10_M) :
    fromTangentSpace (p : R2)
      (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : problem_8_10_M → R2) p
        (problem_8_10_Y p)) =
        !₂[((p : R2) 1), (0 : ℝ)] := by
  -- Push `problem_8_10_Y` through the open-subtype inclusion.
  -- Then read off its ambient coordinates.
  simpa [problem_8_10_Y, problem_8_10_YAmbient] using
    congrArg (fromTangentSpace (p : R2))
      (problem_8_10_subtypeVal_mfderiv_inverse_apply p (problem_8_10_YAmbient p))

/-- Helper for Problem 8-10: pushing `problem_8_10_X` through the open-subtype inclusion recovers
its ambient tangent vector. -/
private theorem problem_8_10_mfderiv_subtype_val_X (p : problem_8_10_M) :
    mfderiv (𝓡 2) (𝓡 2) (Subtype.val : problem_8_10_M → R2) p (problem_8_10_X p) =
      problem_8_10_XAmbient p := by
  -- The vector field was defined by transporting its ambient tangent vector through the inclusion.
  simpa [problem_8_10_X] using
    problem_8_10_subtypeVal_mfderiv_inverse_apply p (problem_8_10_XAmbient p)

/-- Helper for Problem 8-10: pushing `problem_8_10_Y` through the open-subtype inclusion recovers
its ambient tangent vector. -/
private theorem problem_8_10_mfderiv_subtype_val_Y (p : problem_8_10_M) :
    mfderiv (𝓡 2) (𝓡 2) (Subtype.val : problem_8_10_M → R2) p (problem_8_10_Y p) =
      problem_8_10_YAmbient p := by
  -- The vector field was defined by transporting its ambient tangent vector through the inclusion.
  simpa [problem_8_10_Y] using
    problem_8_10_subtypeVal_mfderiv_inverse_apply p (problem_8_10_YAmbient p)

/-- Helper for Problem 8-10: differentiating the ambient coordinate formula of `F` along
`problem_8_10_X` yields the target-coordinate vector `(2u, 0)` at `F(p)`. -/
private theorem problem_8_10_forward_ambient_deriv_on_X (p : problem_8_10_M) :
    fromTangentSpace (problem_8_10_F p : R2)
      (mfderiv (𝓡 2) (𝓡 2) (Subtype.val ∘ problem_8_10_F) p (problem_8_10_X p)) =
        !₂[(2 * (((problem_8_10_F p : problem_8_10_M) : R2) 0)), (0 : ℝ)] := by
  let proj0 : R2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0
  let proj1 : R2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1
  have hx0 : (p : R2) 0 ≠ 0 := ne_of_gt p.property.1
  have h0 : HasFDerivAt (fun q : R2 ↦ q 0) proj0 (p : R2) := by
    simpa [proj0] using
      (PiLp.hasFDerivAt_apply
        (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (f := (p : R2)) 0)
  have h1 : HasFDerivAt (fun q : R2 ↦ q 1) proj1 (p : R2) := by
    simpa [proj1] using
      (PiLp.hasFDerivAt_apply
        (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (f := (p : R2)) 1)
  have hInv :
      HasFDerivAt (fun q : R2 ↦ (q 0)⁻¹)
        ((ContinuousLinearMap.toSpanSingleton ℝ (-((p : R2) 0 ^ 2)⁻¹)).comp proj0) (p : R2) := by
    -- Differentiate the reciprocal of the first coordinate at the source point.
    simpa [proj0] using
      (hasFDerivAt_inv (𝕜 := ℝ) (x := (p : R2) 0) hx0).comp (p : R2) h0
  have hFirst :
      HasFDerivAt (fun q : R2 ↦ problem_8_10_FAmbient q 0)
        (((p : R2) 1) • proj0 + ((p : R2) 0) • proj1) (p : R2) := by
    -- The first coordinate is the product `(x, y) ↦ xy`.
    simpa [problem_8_10_FAmbient, proj0, proj1, add_comm, add_left_comm, add_assoc] using
      h0.mul h1
  have hSecond :
      HasFDerivAt (fun q : R2 ↦ problem_8_10_FAmbient q 1)
        (((p : R2) 1) • ((ContinuousLinearMap.toSpanSingleton ℝ (-((p : R2) 0 ^ 2)⁻¹)).comp proj0) +
          ((p : R2) 0)⁻¹ • proj1) (p : R2) := by
    -- Rewrite `y / x` as `y * x⁻¹` and differentiate product-wise.
    simpa [problem_8_10_FAmbient, div_eq_mul_inv, proj0, proj1] using h1.mul hInv
  let f' : Fin 2 → R2 →L[ℝ] ℝ := fun i =>
    match i with
    | 0 => ((p : R2) 1) • proj0 + ((p : R2) 0) • proj1
    | 1 =>
        ((p : R2) 1) • ((ContinuousLinearMap.toSpanSingleton ℝ (-((p : R2) 0 ^ 2)⁻¹)).comp
          proj0) +
          ((p : R2) 0)⁻¹ • proj1
  let toR2 : (Fin 2 → ℝ) ≃L[ℝ] R2 :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm
  have hAmbientPi :
      HasFDerivAt (fun q : R2 ↦ fun i : Fin 2 ↦ problem_8_10_FAmbient q i)
        (ContinuousLinearMap.pi f') (p : R2) := by
    -- Assemble the ambient derivative in plain product coordinates first.
    refine hasFDerivAt_pi.2 ?_
    intro i
    fin_cases i
    · simpa [f'] using hFirst
    · simpa [f'] using hSecond
  have hAmbient :
      HasFDerivAt problem_8_10_FAmbient
        (toR2.toContinuousLinearMap.comp (ContinuousLinearMap.pi f')) (p : R2) := by
    -- Transport the derivative from product coordinates back to the `PiLp` model space `R2`.
    simpa [toR2, Function.comp] using (toR2.comp_hasFDerivAt_iff.2 hAmbientPi)
  have hFAmbientMDiff : MDifferentiableAt (𝓡 2) (𝓡 2) problem_8_10_FAmbient (p : R2) := by
    exact hAmbient.hasMFDerivAt.mdifferentiableAt
  have hNeZero : (∞ : ℕ∞ω) ≠ 0 := by
    simp
  have hSubMDiff :
      MDifferentiableAt (𝓡 2) (𝓡 2) (Subtype.val : problem_8_10_M → R2) p :=
    (contMDiff_subtype_val :
      ContMDiff (𝓡 2) (𝓡 2) ∞ (Subtype.val : problem_8_10_M → R2)).mdifferentiableAt hNeZero
  have hComp :
      (Subtype.val ∘ problem_8_10_F) =
        problem_8_10_FAmbient ∘ (Subtype.val : problem_8_10_M → R2) := rfl
  -- Route correction: compute through the ambient formula `problem_8_10_FAmbient`, then use the
  -- open-subtype inclusion to identify `problem_8_10_X` with its ambient coordinates.
  rw [hComp]
  rw [mfderiv_comp_apply (x := p) (g := problem_8_10_FAmbient)
    (f := (Subtype.val : problem_8_10_M → R2)) hFAmbientMDiff hSubMDiff (problem_8_10_X p)]
  rw [problem_8_10_mfderiv_subtype_val_X p]
  have hEval :
      fderiv ℝ problem_8_10_FAmbient (p : R2) !₂[((p : R2) 0), ((p : R2) 1)] =
        !₂[(2 * (((problem_8_10_F p : problem_8_10_M) : R2) 0)), (0 : ℝ)] := by
    rw [hAmbient.fderiv]
    ext i
    fin_cases i
    · -- The first derivative component is `yx + xy = 2xy = 2u`.
      change ((ContinuousLinearMap.pi f') !₂[((p : R2) 0), ((p : R2) 1)] 0) =
        (2 * (((problem_8_10_F p : problem_8_10_M) : R2) 0))
      simp [f', proj0, proj1]
      ring
    · -- The derivative of `y / x` vanishes on the vector `(x, y)`.
      change ((ContinuousLinearMap.pi f') !₂[((p : R2) 0), ((p : R2) 1)] 1) = (0 : ℝ)
      simp [f', proj0, proj1]
      field_simp [hx0]
      ring
  simpa [problem_8_10_XAmbient, mfderiv_eq_fderiv] using hEval

/-- Helper for Problem 8-10: differentiating the ambient coordinate formula of `F` along
`problem_8_10_Y` yields the target-coordinate vector `(uv, -v^2)` at `F(p)`. -/
private theorem problem_8_10_forward_ambient_deriv_on_Y (p : problem_8_10_M) :
    fromTangentSpace (problem_8_10_F p : R2)
      (mfderiv (𝓡 2) (𝓡 2) (Subtype.val ∘ problem_8_10_F) p (problem_8_10_Y p)) =
        !₂[((((problem_8_10_F p : problem_8_10_M) : R2) 0) *
              (((problem_8_10_F p : problem_8_10_M) : R2) 1)),
            -((((problem_8_10_F p : problem_8_10_M) : R2) 1) ^ (2 : ℕ))] := by
  let proj0 : R2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0
  let proj1 : R2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1
  have hx0 : (p : R2) 0 ≠ 0 := ne_of_gt p.property.1
  have h0 : HasFDerivAt (fun q : R2 ↦ q 0) proj0 (p : R2) := by
    simpa [proj0] using
      (PiLp.hasFDerivAt_apply
        (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (f := (p : R2)) 0)
  have h1 : HasFDerivAt (fun q : R2 ↦ q 1) proj1 (p : R2) := by
    simpa [proj1] using
      (PiLp.hasFDerivAt_apply
        (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (f := (p : R2)) 1)
  have hInv :
      HasFDerivAt (fun q : R2 ↦ (q 0)⁻¹)
        ((ContinuousLinearMap.toSpanSingleton ℝ (-((p : R2) 0 ^ 2)⁻¹)).comp proj0) (p : R2) := by
    -- Differentiate the reciprocal of the first coordinate at the source point.
    simpa [proj0] using
      (hasFDerivAt_inv (𝕜 := ℝ) (x := (p : R2) 0) hx0).comp (p : R2) h0
  have hFirst :
      HasFDerivAt (fun q : R2 ↦ problem_8_10_FAmbient q 0)
        (((p : R2) 1) • proj0 + ((p : R2) 0) • proj1) (p : R2) := by
    -- The first coordinate is the product `(x, y) ↦ xy`.
    simpa [problem_8_10_FAmbient, proj0, proj1, add_comm, add_left_comm, add_assoc] using
      h0.mul h1
  have hSecond :
      HasFDerivAt (fun q : R2 ↦ problem_8_10_FAmbient q 1)
        (((p : R2) 1) • ((ContinuousLinearMap.toSpanSingleton ℝ (-((p : R2) 0 ^ 2)⁻¹)).comp proj0) +
          ((p : R2) 0)⁻¹ • proj1) (p : R2) := by
    -- Rewrite `y / x` as `y * x⁻¹` and differentiate product-wise.
    simpa [problem_8_10_FAmbient, div_eq_mul_inv, proj0, proj1] using h1.mul hInv
  let f' : Fin 2 → R2 →L[ℝ] ℝ := fun i =>
    match i with
    | 0 => ((p : R2) 1) • proj0 + ((p : R2) 0) • proj1
    | 1 =>
        ((p : R2) 1) • ((ContinuousLinearMap.toSpanSingleton ℝ (-((p : R2) 0 ^ 2)⁻¹)).comp
          proj0) +
          ((p : R2) 0)⁻¹ • proj1
  let toR2 : (Fin 2 → ℝ) ≃L[ℝ] R2 :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm
  have hAmbientPi :
      HasFDerivAt (fun q : R2 ↦ fun i : Fin 2 ↦ problem_8_10_FAmbient q i)
        (ContinuousLinearMap.pi f') (p : R2) := by
    -- Assemble the ambient derivative in plain product coordinates first.
    refine hasFDerivAt_pi.2 ?_
    intro i
    fin_cases i
    · simpa [f'] using hFirst
    · simpa [f'] using hSecond
  have hAmbient :
      HasFDerivAt problem_8_10_FAmbient
        (toR2.toContinuousLinearMap.comp (ContinuousLinearMap.pi f')) (p : R2) := by
    -- Transport the derivative from product coordinates back to the `PiLp` model space `R2`.
    simpa [toR2, Function.comp] using (toR2.comp_hasFDerivAt_iff.2 hAmbientPi)
  have hFAmbientMDiff : MDifferentiableAt (𝓡 2) (𝓡 2) problem_8_10_FAmbient (p : R2) := by
    exact hAmbient.hasMFDerivAt.mdifferentiableAt
  have hNeZero : (∞ : ℕ∞ω) ≠ 0 := by
    simp
  have hSubMDiff :
      MDifferentiableAt (𝓡 2) (𝓡 2) (Subtype.val : problem_8_10_M → R2) p :=
    (contMDiff_subtype_val :
      ContMDiff (𝓡 2) (𝓡 2) ∞ (Subtype.val : problem_8_10_M → R2)).mdifferentiableAt hNeZero
  have hComp :
      (Subtype.val ∘ problem_8_10_F) =
        problem_8_10_FAmbient ∘ (Subtype.val : problem_8_10_M → R2) := rfl
  -- Route correction: compute through the ambient formula `problem_8_10_FAmbient`, then use the
  -- open-subtype inclusion to identify `problem_8_10_Y` with its ambient coordinates.
  rw [hComp]
  rw [mfderiv_comp_apply (x := p) (g := problem_8_10_FAmbient)
    (f := (Subtype.val : problem_8_10_M → R2)) hFAmbientMDiff hSubMDiff (problem_8_10_Y p)]
  rw [problem_8_10_mfderiv_subtype_val_Y p]
  have hEval :
      fderiv ℝ problem_8_10_FAmbient (p : R2) !₂[((p : R2) 1), (0 : ℝ)] =
        !₂[((((problem_8_10_F p : problem_8_10_M) : R2) 0) *
              (((problem_8_10_F p : problem_8_10_M) : R2) 1)),
            -((((problem_8_10_F p : problem_8_10_M) : R2) 1) ^ (2 : ℕ))] := by
    rw [hAmbient.fderiv]
    ext i
    fin_cases i
    · -- The first derivative component is `y * y = uv`.
      change ((ContinuousLinearMap.pi f') !₂[((p : R2) 1), (0 : ℝ)] 0) =
        ((((problem_8_10_F p : problem_8_10_M) : R2) 0) *
          (((problem_8_10_F p : problem_8_10_M) : R2) 1))
      simp [f', proj0, proj1, problem_8_10_F_apply]
      field_simp [hx0]
    · -- The second derivative component is `-(y / x)^2 = -v^2`.
      change ((ContinuousLinearMap.pi f') !₂[((p : R2) 1), (0 : ℝ)] 1) =
        -((((problem_8_10_F p : problem_8_10_M) : R2) 1) ^ (2 : ℕ))
      simp [f', proj0, proj1, problem_8_10_F_apply]
      field_simp [hx0]
  simpa [problem_8_10_YAmbient, mfderiv_eq_fderiv] using hEval

/-- Helper for Problem 8-10: the canonical pushforward of a vector field by
`problem_8_10_diffeomorph` is `problem_8_10_F`-related to the original field. -/
private theorem problem_8_10_pushforward_related
    (Z : ∀ p : problem_8_10_M, TangentSpace (𝓡 2) p) :
    VectorField.f_related (problem_8_10_F : problem_8_10_M → problem_8_10_M) Z
      (((problem_8_10_diffeomorph _* Z) : ∀ q : problem_8_10_M, TangentSpace (𝓡 2) q)) := by
  -- Reuse the chapter pushforward theorem for diffeomorphisms without redoing the inverse
  -- calculation locally.
  exact f_related_pushforward_of_diffeomorph problem_8_10_diffeomorph Z

/-- Helper for Problem 8-10: pushing the canonical relatedness identity through the ambient
inclusion identifies the pushed-forward vector with the ambient derivative of
`Subtype.val ∘ problem_8_10_F`. -/
private theorem problem_8_10_pushforward_ambient_eq_forward_deriv
    (Z : ∀ p : problem_8_10_M, TangentSpace (𝓡 2) p) (p : problem_8_10_M) :
    mfderiv (𝓡 2) (𝓡 2) (Subtype.val : problem_8_10_M → R2) (problem_8_10_F p)
      ((((problem_8_10_diffeomorph _* Z) :
          ∀ q : problem_8_10_M, TangentSpace (𝓡 2) q) (problem_8_10_F p))) =
    mfderiv (𝓡 2) (𝓡 2) (Subtype.val ∘ problem_8_10_F) p (Z p) := by
  have hRelated := VectorField.f_related_apply (problem_8_10_pushforward_related Z) p
  have hNeZero : (∞ : ℕ∞ω) ≠ 0 := by
    simp
  have hSubMDiff :
      MDifferentiableAt (𝓡 2) (𝓡 2) (Subtype.val : problem_8_10_M → R2) (problem_8_10_F p) :=
    (contMDiff_subtype_val :
      ContMDiff (𝓡 2) (𝓡 2) ∞ (Subtype.val : problem_8_10_M → R2)).mdifferentiableAt hNeZero
  have hFMDiff : MDifferentiableAt (𝓡 2) (𝓡 2) problem_8_10_F p :=
    problem_8_10_F_contMDiff.mdifferentiableAt hNeZero
  -- Push the pointwise relatedness identity through the inclusion `M ↪ ℝ²`, then collapse the
  -- transport with a single chain-rule application.
  calc
    mfderiv (𝓡 2) (𝓡 2) (Subtype.val : problem_8_10_M → R2) (problem_8_10_F p)
        ((((problem_8_10_diffeomorph _* Z) :
            ∀ q : problem_8_10_M, TangentSpace (𝓡 2) q) (problem_8_10_F p)))
      =
        mfderiv (𝓡 2) (𝓡 2) (Subtype.val : problem_8_10_M → R2) (problem_8_10_F p)
          ((mfderiv (𝓡 2) (𝓡 2) problem_8_10_F p) (Z p)) := by
            simpa using congrArg
              (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : problem_8_10_M → R2) (problem_8_10_F p))
              hRelated.symm
    _ = mfderiv (𝓡 2) (𝓡 2) (Subtype.val ∘ problem_8_10_F) p (Z p) := by
          symm
          simpa using
            (mfderiv_comp_apply (x := p) (g := (Subtype.val : problem_8_10_M → R2))
              (f := problem_8_10_F) hSubMDiff hFMDiff (Z p))

/-- For Problem 8-10: in ambient Euclidean coordinates on the positive quadrant, the pushforward
of `X = x ∂/∂x + y ∂/∂y` by `F`, realized canonically as
`VectorField.mpullback (𝓡 2) (𝓡 2) problem_8_10_diffeomorph.symm problem_8_10_X`, has
components `(2u, 0)`. -/
theorem problem_8_10_pushforward_X_formula (q : problem_8_10_M) :
    fromTangentSpace (q : R2)
      (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : problem_8_10_M → R2) q
        (VectorField.mpullback (𝓡 2) (𝓡 2) problem_8_10_diffeomorph.symm problem_8_10_X q)) =
        !₂[(2 * ((q : R2) 0)), (0 : ℝ)] := by
  -- Route correction: switch to the canonical pushforward notation so the shared transport helper
  -- matches the theorem statement directly.
  change fromTangentSpace (q : R2)
      (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : problem_8_10_M → R2) q
        ((((problem_8_10_diffeomorph _* problem_8_10_X) :
            ∀ r : problem_8_10_M, TangentSpace (𝓡 2) r) q))) =
      !₂[(2 * ((q : R2) 0)), (0 : ℝ)]
  let p : problem_8_10_M := problem_8_10_F_inv q
  have hPush :
      mfderiv (𝓡 2) (𝓡 2) (Subtype.val : problem_8_10_M → R2) (problem_8_10_F p)
        ((((problem_8_10_diffeomorph _* problem_8_10_X) :
            ∀ r : problem_8_10_M, TangentSpace (𝓡 2) r) (problem_8_10_F p))) =
      mfderiv (𝓡 2) (𝓡 2) (Subtype.val ∘ problem_8_10_F) p (problem_8_10_X p) := by
    -- Reuse the generic ambient transport identity instead of redoing the chain-rule algebra here.
    exact problem_8_10_pushforward_ambient_eq_forward_deriv problem_8_10_X p
  have hAtPreimage :
      fromTangentSpace (problem_8_10_F p : R2)
        (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : problem_8_10_M → R2) (problem_8_10_F p)
          ((((problem_8_10_diffeomorph _* problem_8_10_X) :
              ∀ r : problem_8_10_M, TangentSpace (𝓡 2) r) (problem_8_10_F p)))) =
        !₂[(2 * (((problem_8_10_F p : problem_8_10_M) : R2) 0)), (0 : ℝ)] := by
    -- Rewrite the pushforward through the inclusion and reuse the ambient derivative computation.
    rw [hPush]
    exact problem_8_10_forward_ambient_deriv_on_X p
  have hFq : problem_8_10_F p = q := by
    simpa [p] using problem_8_10_F_right_inv q
  have hAtQ' := hAtPreimage
  -- Move the preimage-point computation from `problem_8_10_F p` back to the target point `q`.
  rw [hFq] at hAtQ'
  simpa using hAtQ'

/-- Problem 8-10 (3): in ambient Euclidean coordinates on the positive quadrant, the pushforward
of `Y = y ∂/∂x` by `F`, realized canonically as
`VectorField.mpullback (𝓡 2) (𝓡 2) problem_8_10_diffeomorph.symm problem_8_10_Y`, has
components `(uv, -v^2)`. -/
theorem problem_8_10_pushforward_Y_formula (q : problem_8_10_M) :
    fromTangentSpace (q : R2)
      (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : problem_8_10_M → R2) q
        (VectorField.mpullback (𝓡 2) (𝓡 2) problem_8_10_diffeomorph.symm problem_8_10_Y q)) =
        !₂[(((q : R2) 0) * ((q : R2) 1)), -(((q : R2) 1) ^ (2 : ℕ))] := by
  -- Route correction: switch to the canonical pushforward notation so the shared transport helper
  -- matches the theorem statement directly.
  change fromTangentSpace (q : R2)
      (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : problem_8_10_M → R2) q
        ((((problem_8_10_diffeomorph _* problem_8_10_Y) :
            ∀ r : problem_8_10_M, TangentSpace (𝓡 2) r) q))) =
      !₂[(((q : R2) 0) * ((q : R2) 1)), -(((q : R2) 1) ^ (2 : ℕ))]
  let p : problem_8_10_M := problem_8_10_F_inv q
  have hPush :
      mfderiv (𝓡 2) (𝓡 2) (Subtype.val : problem_8_10_M → R2) (problem_8_10_F p)
        ((((problem_8_10_diffeomorph _* problem_8_10_Y) :
            ∀ r : problem_8_10_M, TangentSpace (𝓡 2) r) (problem_8_10_F p))) =
      mfderiv (𝓡 2) (𝓡 2) (Subtype.val ∘ problem_8_10_F) p (problem_8_10_Y p) := by
    -- Reuse the generic ambient transport identity instead of redoing the chain-rule algebra here.
    exact problem_8_10_pushforward_ambient_eq_forward_deriv problem_8_10_Y p
  have hAtPreimage :
      fromTangentSpace (problem_8_10_F p : R2)
        (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : problem_8_10_M → R2) (problem_8_10_F p)
          ((((problem_8_10_diffeomorph _* problem_8_10_Y) :
              ∀ r : problem_8_10_M, TangentSpace (𝓡 2) r) (problem_8_10_F p)))) =
        !₂[((((problem_8_10_F p : problem_8_10_M) : R2) 0) *
              (((problem_8_10_F p : problem_8_10_M) : R2) 1)),
            -((((problem_8_10_F p : problem_8_10_M) : R2) 1) ^ (2 : ℕ))] := by
    -- Rewrite the pushforward through the inclusion and reuse the ambient derivative computation.
    rw [hPush]
    exact problem_8_10_forward_ambient_deriv_on_Y p
  have hFq : problem_8_10_F p = q := by
    simpa [p] using problem_8_10_F_right_inv q
  have hAtQ' := hAtPreimage
  -- Move the preimage-point computation from `problem_8_10_F p` back to the target point `q`.
  rw [hFq] at hAtQ'
  simpa using hAtQ'
