import Mathlib
import SmoothManifolds_Lee_2012.Chap02.Sec02_08.Proposition_2_12
import SmoothManifolds_Lee_2012.Chap03.Sec03_14.Proposition_3_9
import SmoothManifolds_Lee_2012.Chap05.Sec05_28.Proposition_5_1
import SmoothManifolds_Lee_2012.Chap08.Sec08_57.Definition_8_57_extra_1
import SmoothManifolds_Lee_2012.Chap08.Sec08_57.Definition_8_57_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open NormedSpace

noncomputable section

local notation "R2" => EuclideanSpace ℝ (Fin 2)

-- Domain sampling pass:
-- * primary domain: diffeomorphisms between open submanifolds and pushforwards of vector fields;
-- * relevant owner declarations checked before refinement:
--   `NormedSpace.fromTangentSpace` (canonical tangent-space coordinates),
--   `mfderiv_open_subset_inclusion_isInvertible` (chapter bridge for open-subset inclusions),
--   `VectorField.mpullback` (canonical pushforward owner for diffeomorphisms),
--   and `Proposition_8_19` / `Definition_8_57_extra_2` (chapter-local pushforward interface).
-- Primitive data here is the pair of open subsets, the explicit coordinate diffeomorphism, and
-- the source vector field. The pushforward coordinate formula is derived API from the diffeomorph
-- owner together with the ambient-coordinate bridge through the open-subset inclusions.

/-- The open submanifold `M = {(x,y) : y > 0 and x + y > 0}` from Example 8.20. -/
def example_8_20_M : TopologicalSpace.Opens R2 where
  carrier := {p : R2 | 0 < p 1 ∧ 0 < p 0 + p 1}
  is_open' := by
    refine IsOpen.inter ?_ ?_
    · change IsOpen {p : R2 | 0 < p 1}
      exact isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1)
    · change IsOpen {p : R2 | 0 < p 0 + p 1}
      have h0 : Continuous fun p : R2 ↦ p 0 :=
        PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0
      have h1 : Continuous fun p : R2 ↦ p 1 :=
        PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1
      exact isOpen_lt continuous_const (h0.add h1)

/-- Membership in the source open submanifold `example_8_20_M` is given by the textbook
inequalities `y > 0` and `x + y > 0`. -/
theorem mem_example_8_20_M (p : R2) :
    p ∈ (example_8_20_M : Set R2) ↔ 0 < p 1 ∧ 0 < p 0 + p 1 := Iff.rfl

/-- The open submanifold `N = {(u,v) : u > 0 and v > 0}` from Example 8.20. -/
def example_8_20_N : TopologicalSpace.Opens R2 where
  carrier := {p : R2 | 0 < p 0 ∧ 0 < p 1}
  is_open' := by
    refine IsOpen.inter ?_ ?_
    · change IsOpen {p : R2 | 0 < p 0}
      exact isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0)
    · change IsOpen {p : R2 | 0 < p 1}
      exact isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1)

/-- Membership in the target open submanifold `example_8_20_N` is given by the textbook
inequalities `u > 0` and `v > 0`. -/
theorem mem_example_8_20_N (p : R2) :
    p ∈ (example_8_20_N : Set R2) ↔ 0 < p 0 ∧ 0 < p 1 := Iff.rfl

/-- The explicit coordinate formula for the map `F(x,y) = (x + y, x/y + 1)` lands in
`example_8_20_N`. -/
theorem example_8_20_F_mem_N (p : example_8_20_M) :
    !₂[((p : R2) 0) + (p : R2) 1, ((p : R2) 0) / ((p : R2) 1) + 1] ∈
      (example_8_20_N : Set R2) := by
  rcases p.property with ⟨hy, hxy⟩
  have hy0 : (p : R2) 1 ≠ 0 := ne_of_gt hy
  constructor
  · -- The first target coordinate is exactly `x + y`, which is positive on `M`.
    simpa using hxy
  · -- Rewrite `x / y + 1` as `(x + y) / y` and use positivity of numerator and denominator.
    have hrewrite :
        (p : R2) 0 / (p : R2) 1 + 1 = ((p : R2) 0 + (p : R2) 1) / (p : R2) 1 := by
      field_simp [hy0]
    rw [hrewrite]
    exact div_pos hxy hy

/-- The map `F : M → N` from Example 8.20, written on the open-submanifold subtypes. -/
def example_8_20_F (p : example_8_20_M) : example_8_20_N :=
  ⟨!₂[((p : R2) 0) + (p : R2) 1, ((p : R2) 0) / ((p : R2) 1) + 1], example_8_20_F_mem_N p⟩

/-- The underlying `ℝ²`-valued coordinate formula for `example_8_20_F`. -/
@[simp] theorem example_8_20_F_apply (p : example_8_20_M) :
    ((example_8_20_F p : example_8_20_N) : R2) =
      !₂[((p : R2) 0) + (p : R2) 1, ((p : R2) 0) / ((p : R2) 1) + 1] := rfl

/-- The explicit inverse-coordinate formula `(u,v) ↦ (u - u/v, u/v)` lands back in
`example_8_20_M`. -/
theorem example_8_20_F_inv_mem_M (q : example_8_20_N) :
    !₂[((q : R2) 0) - ((q : R2) 0) / ((q : R2) 1), ((q : R2) 0) / ((q : R2) 1)] ∈
      (example_8_20_M : Set R2) := by
  rcases q.property with ⟨hu, hv⟩
  constructor
  · -- The second source coordinate is `u / v`, positive because both target coordinates are.
    exact div_pos hu hv
  · -- The sum of the inverse coordinates collapses back to `u`.
    have hsum :
        ((q : R2) 0 - (q : R2) 0 / (q : R2) 1) + (q : R2) 0 / (q : R2) 1 = (q : R2) 0 := by
      ring
    simpa [hsum]

/-- The inverse map `F⁻¹ : N → M` from Example 8.20, written on the open-submanifold subtypes. -/
def example_8_20_F_inv (q : example_8_20_N) : example_8_20_M :=
  ⟨!₂[((q : R2) 0) - ((q : R2) 0) / ((q : R2) 1), ((q : R2) 0) / ((q : R2) 1)],
    example_8_20_F_inv_mem_M q⟩

/-- The underlying `ℝ²`-valued coordinate formula for `example_8_20_F_inv`. -/
@[simp] theorem example_8_20_F_inv_apply (q : example_8_20_N) :
    ((example_8_20_F_inv q : example_8_20_M) : R2) =
      !₂[((q : R2) 0) - ((q : R2) 0) / ((q : R2) 1), ((q : R2) 0) / ((q : R2) 1)] := rfl

/-- The explicit inverse formula of Example 8.20 is a left inverse for `example_8_20_F`. -/
theorem example_8_20_F_left_inv (p : example_8_20_M) :
    example_8_20_F_inv (example_8_20_F p) = p := by
  rcases p.property with ⟨hy, hxy⟩
  have hy0 : (p : R2) 1 ≠ 0 := ne_of_gt hy
  have hxy0 : (p : R2) 0 + (p : R2) 1 ≠ 0 := ne_of_gt hxy
  apply Subtype.ext
  ext i
  fin_cases i
  · -- The first inverse coordinate simplifies to the original `x`.
    simp [example_8_20_F_apply, example_8_20_F_inv_apply]
    field_simp [hy0, hxy0]
    ring
  · -- The second inverse coordinate simplifies to the original `y`.
    simp [example_8_20_F_apply, example_8_20_F_inv_apply]
    field_simp [hy0, hxy0]

/-- The explicit inverse formula of Example 8.20 is a right inverse for `example_8_20_F`. -/
theorem example_8_20_F_right_inv (q : example_8_20_N) :
    example_8_20_F (example_8_20_F_inv q) = q := by
  rcases q.property with ⟨hu, hv⟩
  have hu0 : (q : R2) 0 ≠ 0 := ne_of_gt hu
  have hv0 : (q : R2) 1 ≠ 0 := ne_of_gt hv
  apply Subtype.ext
  ext i
  fin_cases i
  · -- The first forward coordinate of the inverse point is `u`.
    simp [example_8_20_F_apply, example_8_20_F_inv_apply]
  · -- The second forward coordinate of the inverse point is `v`.
    simp [example_8_20_F_apply, example_8_20_F_inv_apply]
    field_simp [hu0, hv0]
    ring

/-- The ambient coordinate formula `F(x,y) = (x + y, x / y + 1)` from Example 8.20. -/
private def example_8_20_FAmbient (p : R2) : R2 :=
  !₂[p 0 + p 1, p 0 / p 1 + 1]

/-- The ambient coordinate formula for the inverse map `F⁻¹(u,v) = (u - u / v, u / v)`. -/
private def example_8_20_FInvAmbient (q : R2) : R2 :=
  !₂[q 0 - q 0 / q 1, q 0 / q 1]

/-- The forward coordinate map of Example 8.20 is smooth on the open submanifold `M`. -/
theorem example_8_20_F_contMDiff :
    ContMDiff (𝓡 2) (𝓡 2) ∞ example_8_20_F := by
  let toR2 : (Fin 2 → ℝ) ≃L[ℝ] R2 :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm
  have h0 : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (fun p : example_8_20_M ↦ (p : R2) 0) := by
    simpa [Function.comp] using
      ((PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0).contDiff.contMDiff.comp
        (contMDiff_subtype_val : ContMDiff (𝓡 2) (𝓡 2) ∞ (Subtype.val : example_8_20_M → R2)))
  have h1 : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (fun p : example_8_20_M ↦ (p : R2) 1) := by
    simpa [Function.comp] using
      ((PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1).contDiff.contMDiff.comp
        (contMDiff_subtype_val : ContMDiff (𝓡 2) (𝓡 2) ∞ (Subtype.val : example_8_20_M → R2)))
  have hPi :
      ContMDiff (𝓡 2) 𝓘(ℝ, Fin 2 → ℝ) ∞
        (fun p : example_8_20_M ↦
          fun i : Fin 2 ↦ (((example_8_20_F p : example_8_20_N) : R2) i)) := by
    refine contMDiff_pi_space.2 ?_
    intro i
    fin_cases i
    · -- The first coordinate is the sum of the two smooth coordinate projections.
      simpa [example_8_20_F_apply] using h0.add h1
    · -- The second coordinate is `x / y + 1`, smooth on the open source region where `y > 0`.
      have hdiv :
          ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (fun p : example_8_20_M ↦ (p : R2) 0 / (p : R2) 1) := by
        exact h0.div₀ h1 (fun p ↦ ne_of_gt p.property.1)
      simpa [example_8_20_F_apply] using
        hdiv.add (contMDiff_const : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (fun _ : example_8_20_M ↦ (1 : ℝ)))
  have hSub :
      ContMDiff (𝓡 2) (𝓡 2) ∞ ((Subtype.val : example_8_20_N → R2) ∘ example_8_20_F) := by
    refine (toR2.contDiff.contMDiff.comp hPi).congr ?_
    intro p
    simp [toR2, Function.comp, example_8_20_F_apply]
  exact (ContMDiff.subtypeVal_comp_iff example_8_20_N example_8_20_F).1 hSub

/-- The inverse coordinate map of Example 8.20 is smooth on the open submanifold `N`. -/
theorem example_8_20_F_inv_contMDiff :
    ContMDiff (𝓡 2) (𝓡 2) ∞ example_8_20_F_inv := by
  let toR2 : (Fin 2 → ℝ) ≃L[ℝ] R2 :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm
  have h0 : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (fun q : example_8_20_N ↦ (q : R2) 0) := by
    simpa [Function.comp] using
      ((PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0).contDiff.contMDiff.comp
        (contMDiff_subtype_val : ContMDiff (𝓡 2) (𝓡 2) ∞ (Subtype.val : example_8_20_N → R2)))
  have h1 : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (fun q : example_8_20_N ↦ (q : R2) 1) := by
    simpa [Function.comp] using
      ((PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1).contDiff.contMDiff.comp
        (contMDiff_subtype_val : ContMDiff (𝓡 2) (𝓡 2) ∞ (Subtype.val : example_8_20_N → R2)))
  have hPi :
      ContMDiff (𝓡 2) 𝓘(ℝ, Fin 2 → ℝ) ∞
        (fun q : example_8_20_N ↦
          fun i : Fin 2 ↦ (((example_8_20_F_inv q : example_8_20_M) : R2) i)) := by
    refine contMDiff_pi_space.2 ?_
    intro i
    fin_cases i
    · -- The first inverse coordinate is `u - u / v`.
      have hdiv :
          ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (fun q : example_8_20_N ↦ (q : R2) 0 / (q : R2) 1) := by
        exact h0.div₀ h1 (fun q ↦ ne_of_gt q.property.2)
      simpa [example_8_20_F_inv_apply] using h0.sub hdiv
    · -- The second inverse coordinate is the smooth quotient `u / v`.
      have hdiv :
          ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (fun q : example_8_20_N ↦ (q : R2) 0 / (q : R2) 1) := by
        exact h0.div₀ h1 (fun q ↦ ne_of_gt q.property.2)
      simpa [example_8_20_F_inv_apply] using hdiv
  have hSub :
      ContMDiff (𝓡 2) (𝓡 2) ∞ ((Subtype.val : example_8_20_M → R2) ∘ example_8_20_F_inv) := by
    refine (toR2.contDiff.contMDiff.comp hPi).congr ?_
    intro q
    simp [toR2, Function.comp, example_8_20_F_inv_apply]
  exact (ContMDiff.subtypeVal_comp_iff example_8_20_M example_8_20_F_inv).1 hSub

/-- The map `F` of Example 8.20 packaged as a diffeomorphism between the two open submanifolds. -/
def example_8_20_diffeomorph : example_8_20_M ≃ₘ⟮𝓡 2, 𝓡 2⟯ example_8_20_N where
  toEquiv :=
    { toFun := example_8_20_F
      invFun := example_8_20_F_inv
      left_inv := example_8_20_F_left_inv
      right_inv := example_8_20_F_right_inv }
  contMDiff_toFun := example_8_20_F_contMDiff
  contMDiff_invFun := example_8_20_F_inv_contMDiff

/-- The ambient coordinate vector for `X = y^2 ∂/∂x` at a point of the open submanifold `M`. -/
private def example_8_20_XAmbient (p : example_8_20_M) : TangentSpace (𝓡 2) (p : R2) :=
  (fromTangentSpace (p : R2)).symm !₂[(((p : R2) 1) ^ 2), (0 : ℝ)]

/-- The vector field `X = y^2 ∂/∂x` on `M`, obtained by transporting the ambient coordinate vector
through the inclusion `example_8_20_M ↪ ℝ²`. -/
def example_8_20_X (p : example_8_20_M) : TangentSpace (𝓡 2) p :=
  (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : example_8_20_M → R2) p).inverse (example_8_20_XAmbient p)

/-- Pushing `example_8_20_X` forward along the inclusion `example_8_20_M ↪ ℝ²` recovers its
ambient coordinate vector. -/
theorem mfderiv_subtype_val_example_8_20_X (p : example_8_20_M) :
    mfderiv (𝓡 2) (𝓡 2) (Subtype.val : example_8_20_M → R2) p (example_8_20_X p) =
      example_8_20_XAmbient p := by
  simpa [example_8_20_X] using
    (mfderiv_open_subset_inclusion_isInvertible example_8_20_M p).self_apply_inverse
      (example_8_20_XAmbient p)

/-- In ambient Euclidean coordinates, `example_8_20_X` has components `(y^2, 0)`. -/
theorem fromTangentSpace_example_8_20_X (p : example_8_20_M) :
    fromTangentSpace (p : R2)
      (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : example_8_20_M → R2) p (example_8_20_X p)) =
        !₂[(((p : R2) 1) ^ 2), (0 : ℝ)] := by
  simpa [example_8_20_XAmbient] using
    congrArg (fromTangentSpace (p : R2)) (mfderiv_subtype_val_example_8_20_X p)

/-- Helper for Example 8.20: differentiating the ambient coordinate formula of `F` along
`X = y^2 ∂/∂x` produces the coordinate vector `(y^2, y)`. -/
private theorem example_8_20_forward_ambient_deriv_on_X (p : example_8_20_M) :
    fromTangentSpace (example_8_20_F p : R2)
      (mfderiv (𝓡 2) (𝓡 2) (Subtype.val ∘ example_8_20_F) p (example_8_20_X p)) =
        !₂[(((p : R2) 1) ^ 2), (p : R2) 1] := by
  let proj0 : R2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0
  let proj1 : R2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1
  have hy0 : (p : R2) 1 ≠ 0 := ne_of_gt p.property.1
  have h0 : HasFDerivAt (fun q : R2 ↦ q 0) proj0 (p : R2) := by
    -- The first coordinate projection differentiates to the first-coordinate linear map.
    simpa [proj0] using
      (PiLp.hasFDerivAt_apply
        (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (f := (p : R2)) 0)
  have h1 : HasFDerivAt (fun q : R2 ↦ q 1) proj1 (p : R2) := by
    -- The second coordinate projection differentiates to the second-coordinate linear map.
    simpa [proj1] using
      (PiLp.hasFDerivAt_apply
        (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (f := (p : R2)) 1)
  have hInv :
      HasFDerivAt (fun q : R2 ↦ (q 1)⁻¹)
        ((ContinuousLinearMap.toSpanSingleton ℝ (-((p : R2) 1 ^ 2)⁻¹)).comp proj1) (p : R2) := by
    -- Differentiate the reciprocal of the second coordinate at the source point.
    simpa [proj1] using
      (hasFDerivAt_inv (𝕜 := ℝ) (x := (p : R2) 1) hy0).comp (p : R2) h1
  have hFirst :
      HasFDerivAt (fun q : R2 ↦ example_8_20_FAmbient q 0) (proj0 + proj1) (p : R2) := by
    -- The first coordinate is the sum `x + y`.
    simpa [example_8_20_FAmbient, proj0, proj1] using h0.add h1
  have hSecond :
      HasFDerivAt (fun q : R2 ↦ example_8_20_FAmbient q 1)
        (((p : R2) 0) • ((ContinuousLinearMap.toSpanSingleton ℝ (-((p : R2) 1 ^ 2)⁻¹)).comp
            proj1) +
          ((p : R2) 1)⁻¹ • proj0) (p : R2) := by
    -- Rewrite `x / y + 1` as `x * y⁻¹ + 1` and differentiate product-wise.
    simpa [example_8_20_FAmbient, div_eq_mul_inv, proj0, proj1] using
      (h0.mul hInv).add_const (1 : ℝ)
  let f' : Fin 2 → R2 →L[ℝ] ℝ := fun i =>
    match i with
    | 0 => proj0 + proj1
    | 1 =>
        ((p : R2) 0) • ((ContinuousLinearMap.toSpanSingleton ℝ (-((p : R2) 1 ^ 2)⁻¹)).comp proj1) +
          ((p : R2) 1)⁻¹ • proj0
  let toR2 : (Fin 2 → ℝ) ≃L[ℝ] R2 :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm
  have hAmbientPi :
      HasFDerivAt (fun q : R2 ↦ fun i : Fin 2 ↦ example_8_20_FAmbient q i)
        (ContinuousLinearMap.pi f') (p : R2) := by
    -- Assemble the ambient derivative in plain product coordinates first.
    refine hasFDerivAt_pi.2 ?_
    intro i
    fin_cases i
    · simpa [f'] using hFirst
    · simpa [f'] using hSecond
  have hAmbient :
      HasFDerivAt example_8_20_FAmbient
        (toR2.toContinuousLinearMap.comp (ContinuousLinearMap.pi f')) (p : R2) := by
    -- Transport the derivative from product coordinates back to the `PiLp` model space `R2`.
    simpa [toR2, Function.comp] using (toR2.comp_hasFDerivAt_iff.2 hAmbientPi)
  have hAmbientMDiff : MDifferentiableAt (𝓡 2) (𝓡 2) example_8_20_FAmbient (p : R2) := by
    exact hAmbient.hasMFDerivAt.mdifferentiableAt
  have hNeZero : (∞ : ℕ∞ω) ≠ 0 := by
    simp
  have hSubMDiff :
      MDifferentiableAt (𝓡 2) (𝓡 2) (Subtype.val : example_8_20_M → R2) p :=
    (contMDiff_subtype_val :
      ContMDiff (𝓡 2) (𝓡 2) ∞ (Subtype.val : example_8_20_M → R2)).mdifferentiableAt hNeZero
  have hComp :
      (Subtype.val ∘ example_8_20_F) =
        example_8_20_FAmbient ∘ (Subtype.val : example_8_20_M → R2) := rfl
  -- Route correction: compute through `example_8_20_FAmbient`, then identify `example_8_20_X`
  -- with its ambient coordinates via the open-subtype inclusion.
  rw [hComp]
  rw [mfderiv_comp_apply (x := p) (g := example_8_20_FAmbient)
    (f := (Subtype.val : example_8_20_M → R2)) hAmbientMDiff hSubMDiff (example_8_20_X p)]
  rw [mfderiv_subtype_val_example_8_20_X p]
  have hEval :
      fderiv ℝ example_8_20_FAmbient (p : R2) !₂[(((p : R2) 1) ^ 2), (0 : ℝ)] =
        !₂[(((p : R2) 1) ^ 2), (p : R2) 1] := by
    rw [hAmbient.fderiv]
    ext i
    fin_cases i
    · -- The derivative of `x + y` on the vector `(y^2, 0)` is `y^2`.
      change ((ContinuousLinearMap.pi f') !₂[(((p : R2) 1) ^ 2), (0 : ℝ)] 0) = ((p : R2) 1) ^ 2
      simp [f', proj0, proj1]
    · -- The derivative of `x / y + 1` on the vector `(y^2, 0)` is `y`.
      change ((ContinuousLinearMap.pi f') !₂[(((p : R2) 1) ^ 2), (0 : ℝ)] 1) = (p : R2) 1
      simp [f', proj0, proj1]
      field_simp [hy0]
  simpa [example_8_20_XAmbient, mfderiv_eq_fderiv] using hEval

/-- Helper for Example 8.20: the explicit pushforward vector field is `example_8_20_F`-related
to `example_8_20_X`. -/
private theorem example_8_20_pushforward_related :
    VectorField.f_related (example_8_20_F : example_8_20_M → example_8_20_N)
      example_8_20_X
      (((example_8_20_diffeomorph _* example_8_20_X) :
        ∀ q : example_8_20_N, TangentSpace (𝓡 2) q)) := by
  change VectorField.f_related (example_8_20_F : example_8_20_M → example_8_20_N)
    example_8_20_X
    (VectorField.mpullback (𝓡 2) (𝓡 2) example_8_20_diffeomorph.symm example_8_20_X)
  refine ⟨example_8_20_F_contMDiff, ?_⟩
  intro p
  have hsymm : example_8_20_diffeomorph.symm (example_8_20_F p) = p := by
    simpa [example_8_20_diffeomorph] using example_8_20_F_left_inv p
  rw [VectorField.mpullback_apply, hsymm, eq_comm]
  have hNeZero : (∞ : ℕ∞ω) ≠ 0 := by
    simp
  let e :
      TangentSpace (𝓡 2) (example_8_20_F p) ≃L[ℝ]
        TangentSpace (𝓡 2) (example_8_20_diffeomorph.symm (example_8_20_F p)) :=
    example_8_20_diffeomorph.symm.mfderivToContinuousLinearEquiv hNeZero (example_8_20_F p)
  have hcoe :
      ↑(example_8_20_diffeomorph.symm.mfderivToContinuousLinearEquiv hNeZero (example_8_20_F p)) =
        mfderiv (𝓡 2) (𝓡 2) example_8_20_diffeomorph.symm (example_8_20_F p) :=
    example_8_20_diffeomorph.symm.mfderivToContinuousLinearEquiv_coe
      (x := example_8_20_F p) hNeZero
  have hInvLinear :
      ContinuousLinearMap.IsInvertible
        (mfderiv (𝓡 2) (𝓡 2) example_8_20_diffeomorph.symm (example_8_20_F p)) := by
    have he : ↑e = mfderiv (𝓡 2) (𝓡 2) example_8_20_diffeomorph.symm (example_8_20_F p) := by
      simpa [e] using hcoe.symm
    exact ⟨e, he⟩
  have hPushEq :
      (mfderiv (𝓡 2) (𝓡 2) example_8_20_diffeomorph.symm (example_8_20_F p)).inverse
          (example_8_20_X p) =
        (mfderiv (𝓡 2) (𝓡 2) example_8_20_F p) (example_8_20_X p) := by
    have h :
        mfderiv (𝓡 2) (𝓡 2) (example_8_20_diffeomorph.symm ∘ example_8_20_F) p
            (example_8_20_X p) =
        mfderiv (𝓡 2) (𝓡 2) example_8_20_diffeomorph.symm (example_8_20_F p)
          ((mfderiv (𝓡 2) (𝓡 2) example_8_20_F p) (example_8_20_X p)) := by
      -- Differentiate the identity `F.symm ∘ F = id` at the source point.
      exact mfderiv_comp_apply
        (x := p)
        (g := example_8_20_diffeomorph.symm)
        (f := example_8_20_F)
        (example_8_20_diffeomorph.symm.contMDiff.mdifferentiableAt hNeZero)
        (example_8_20_F_contMDiff.mdifferentiableAt hNeZero)
        (example_8_20_X p)
    have hcomp :
        example_8_20_diffeomorph.symm ∘ example_8_20_F = id := by
      funext x
      simpa [example_8_20_diffeomorph] using example_8_20_F_left_inv x
    rw [hcomp, mfderiv_id] at h
    exact (ContinuousLinearMap.IsInvertible.inverse_apply_eq hInvLinear).2 h
  exact hPushEq

/-- Helper for Example 8.20: pushing the relatedness identity through the target inclusion
identifies the pushed-forward vector with the ambient derivative of `Subtype.val ∘ example_8_20_F`.
-/
private theorem example_8_20_pushforward_ambient_eq_forward_deriv (p : example_8_20_M) :
    mfderiv (𝓡 2) (𝓡 2) (Subtype.val : example_8_20_N → R2) (example_8_20_F p)
      ((((example_8_20_diffeomorph _* example_8_20_X) :
          ∀ q : example_8_20_N, TangentSpace (𝓡 2) q) (example_8_20_F p))) =
    mfderiv (𝓡 2) (𝓡 2) (Subtype.val ∘ example_8_20_F) p (example_8_20_X p) := by
  have hRelated := VectorField.f_related_apply example_8_20_pushforward_related p
  have hNeZero : (∞ : ℕ∞ω) ≠ 0 := by
    simp
  have hSubMDiff :
      MDifferentiableAt (𝓡 2) (𝓡 2) (Subtype.val : example_8_20_N → R2) (example_8_20_F p) :=
    (contMDiff_subtype_val :
      ContMDiff (𝓡 2) (𝓡 2) ∞ (Subtype.val : example_8_20_N → R2)).mdifferentiableAt hNeZero
  have hFMDiff : MDifferentiableAt (𝓡 2) (𝓡 2) example_8_20_F p :=
    example_8_20_F_contMDiff.mdifferentiableAt hNeZero
  -- Push the pointwise relatedness identity through the inclusion `N ↪ ℝ²`, then apply the chain
  -- rule once to collapse the transport.
  calc
    mfderiv (𝓡 2) (𝓡 2) (Subtype.val : example_8_20_N → R2) (example_8_20_F p)
        ((((example_8_20_diffeomorph _* example_8_20_X) :
            ∀ q : example_8_20_N, TangentSpace (𝓡 2) q) (example_8_20_F p)))
      =
        mfderiv (𝓡 2) (𝓡 2) (Subtype.val : example_8_20_N → R2) (example_8_20_F p)
          ((mfderiv (𝓡 2) (𝓡 2) example_8_20_F p) (example_8_20_X p)) := by
            simpa using congrArg
              (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : example_8_20_N → R2) (example_8_20_F p))
              hRelated.symm
    _ = mfderiv (𝓡 2) (𝓡 2) (Subtype.val ∘ example_8_20_F) p (example_8_20_X p) := by
          symm
          simpa using
            (mfderiv_comp_apply (x := p) (g := (Subtype.val : example_8_20_N → R2))
              (f := example_8_20_F) hSubMDiff hFMDiff (example_8_20_X p))

/-- Example 8.20: for `F(x,y) = (x + y, x/y + 1)` from `M` to `N` and the vector field
`X = y^2 ∂/∂x` on `M`, Lee's pushforward vector field
`example_8_20_diffeomorph _* example_8_20_X` has ambient coordinate expression
`(u^2 / v^2, u / v)` on `N`. -/
theorem example_8_20_pushforward_formula (q : example_8_20_N) :
    fromTangentSpace (q : R2)
      (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : example_8_20_N → R2) q
        ((example_8_20_diffeomorph _* example_8_20_X) q)) =
      !₂[(((q : R2) 0) ^ 2) / (((q : R2) 1) ^ 2), ((q : R2) 0) / ((q : R2) 1)] := by
  let p : example_8_20_M := example_8_20_F_inv q
  have hv0 : (q : R2) 1 ≠ 0 := ne_of_gt q.property.2
  have hAtPreimage :
      fromTangentSpace (example_8_20_F p : R2)
        (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : example_8_20_N → R2) (example_8_20_F p)
          ((((example_8_20_diffeomorph _* example_8_20_X) :
              ∀ r : example_8_20_N, TangentSpace (𝓡 2) r) (example_8_20_F p)))) =
        !₂[(((p : R2) 1) ^ 2), (p : R2) 1] := by
    -- Rewrite the pushforward through the inclusion and reuse the ambient derivative computation.
    rw [example_8_20_pushforward_ambient_eq_forward_deriv p]
    exact example_8_20_forward_ambient_deriv_on_X p
  have hFq : example_8_20_F p = q := by
    simpa [p] using example_8_20_F_right_inv q
  have hAtQ :
      fromTangentSpace (q : R2)
        (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : example_8_20_N → R2) q
          ((example_8_20_diffeomorph _* example_8_20_X) q)) =
        !₂[((((q : R2) 0) / ((q : R2) 1)) ^ (2 : ℕ)), ((q : R2) 0) / ((q : R2) 1)] := by
    -- Evaluate the preimage-point computation at `p = F⁻¹(q)`.
    have hAtQ' := hAtPreimage
    rw [hFq] at hAtQ'
    simpa [p, example_8_20_F_inv_apply] using hAtQ'
  have hsquare :
      ((((q : R2) 0) / ((q : R2) 1)) ^ (2 : ℕ)) =
        (((q : R2) 0) ^ (2 : ℕ)) / (((q : R2) 1) ^ (2 : ℕ)) := by
    field_simp [hv0]
  calc
    fromTangentSpace (q : R2)
        (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : example_8_20_N → R2) q
          ((example_8_20_diffeomorph _* example_8_20_X) q))
      = !₂[((((q : R2) 0) / ((q : R2) 1)) ^ (2 : ℕ)), ((q : R2) 0) / ((q : R2) 1)] := hAtQ
    _ = !₂[(((q : R2) 0) ^ (2 : ℕ)) / (((q : R2) 1) ^ (2 : ℕ)), ((q : R2) 0) / ((q : R2) 1)] := by
          ext i
          fin_cases i
          · exact hsquare
          · rfl
