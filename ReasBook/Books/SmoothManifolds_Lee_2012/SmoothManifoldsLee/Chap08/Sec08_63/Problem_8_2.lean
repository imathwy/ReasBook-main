import Mathlib
import SmoothManifolds_Lee_2012.Chap08.Sec08_54.Example_8_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open NormedSpace

noncomputable section

-- Domain sampling pass:
-- * primary domain: smooth real-valued functions on punctured real normed spaces and their
--   directional derivatives;
-- * inspected owner declarations: the project declarations `euler_vector_field` and
--   `fromTangentSpace_euler_vector_field` from `Example_8_3`, together with mathlib's
--   `ContDiffOn` and `fderivWithin`;
-- * core/canonical owner: the Euler vector field itself;
-- * primitive source-facing data: smoothness on the punctured space and the positive
--   homogeneity law;
-- * bridge/view API: the coordinate-direction formula is recovered from
--   `fromTangentSpace_euler_vector_field`.

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {c : ℝ} {f : E → ℝ}

/-- Helper for Problem 8-2: on the punctured open set, the within-derivative agrees with the
ordinary Fréchet derivative. -/
lemma puncturedFderiv_eq_fderiv (f : E → ℝ) (x : E) (hx : x ≠ 0) :
    fderivWithin ℝ f ({0} : Set E)ᶜ x = fderiv ℝ f x := by
  -- The punctured domain is open, so there is no within-set correction at `x ≠ 0`.
  have hx_mem : x ∈ ({0} : Set E)ᶜ := by
    simpa
  rw [fderivWithin_of_isOpen isOpen_compl_singleton hx_mem]

/-- Helper for Problem 8-2: the radial curve `t ↦ f (t • x)` has derivative
`(fderiv ℝ f x) x` at `t = 1`. -/
lemma hasDerivAt_radialCurve
    (hf_smooth : ContDiffOn ℝ ∞ f ({0} : Set E)ᶜ)
    (x : E) (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ ↦ f (t • x)) ((fderiv ℝ f x) x) 1 := by
  -- Smoothness on the punctured set gives differentiability of `f` at `x`.
  have hx_mem : x ∈ ({0} : Set E)ᶜ := by
    simpa
  have hpunctured_nhds : ({0} : Set E)ᶜ ∈ 𝓝 x :=
    isOpen_compl_singleton.mem_nhds hx_mem
  have hdiffAt : DifferentiableAt ℝ f x := by
    exact (hf_smooth.contDiffAt hpunctured_nhds).differentiableAt (by simp)
  -- Differentiate the scalar radial map `t ↦ t • x` and compose with `f`.
  have hsmul : HasDerivAt (fun t : ℝ ↦ t • x) x 1 := by
    simpa using (hasDerivAt_id : HasDerivAt id 1 (1 : ℝ)).smul_const x
  simpa [Function.comp] using hdiffAt.hasFDerivAt.comp_hasDerivAt hsmul

/-- Helper for Problem 8-2: near `t = 1`, positive homogeneity rewrites the radial curve as the
scalar model curve `t ↦ Real.rpow t c * f x`. -/
lemma radialHomogeneityEventuallyEq
    (hf_homogeneous :
      ∀ ⦃t : ℝ⦄, 0 < t →
        ∀ ⦃x : E⦄, x ≠ 0 →
          f (t • x) = Real.rpow t c * f x)
    (x : E) (hx : x ≠ 0) :
    (fun t : ℝ ↦ f (t • x)) =ᶠ[𝓝 1] (fun t ↦ Real.rpow t c * f x) := by
  -- Around `t = 1`, all nearby scalars are positive, so the homogeneity formula applies.
  filter_upwards [Ioi_mem_nhds zero_lt_one] with t ht
  exact hf_homogeneous ht hx

/-- Helper for Problem 8-2: the model homogeneous scalar curve has derivative `c * f x` at
`t = 1`. -/
lemma hasDerivAt_homogeneousScalarCurve (c : ℝ) (f : E → ℝ) (x : E) :
    HasDerivAt (fun t : ℝ ↦ Real.rpow t c * f x) (c * f x) 1 := by
  -- Differentiate `t ↦ t^c` at `1` and then pull out the constant factor `f x`.
  have hrpow : HasDerivAt (fun t : ℝ ↦ Real.rpow t c) (c * Real.rpow 1 (c - 1)) 1 := by
    simpa using (Real.hasDerivAt_rpow_const (x := 1) (p := c) (Or.inl one_ne_zero))
  simpa [Real.one_rpow] using hrpow.mul_const (f x)

/-- Problem 8-2: Euler's homogeneous function theorem. If `f` is smooth on the punctured real
normed space `E \ {0}` and positively homogeneous of degree `c`, then differentiating `f` along
the Euler vector field of Example 8.3 yields `c • f` pointwise away from the origin. For
`E = EuclideanSpace ℝ (Fin n)`, this is the textbook `ℝⁿ \ {0}` statement. -/
theorem euler_homogeneous_function_theorem
    (hf_smooth : ContDiffOn ℝ ∞ f ({0} : Set E)ᶜ)
    (hf_homogeneous :
      ∀ ⦃t : ℝ⦄, 0 < t →
        ∀ ⦃x : E⦄, x ≠ 0 →
          f (t • x) = Real.rpow t c * f x)
    (x : E) (hx : x ≠ 0) :
    fderivWithin ℝ f ({0} : Set E)ᶜ x (fromTangentSpace x (euler_vector_field x)) = c * f x :=
  by
  -- Rewrite the tangent direction and the within-derivative into the ordinary derivative at `x`.
  rw [puncturedFderiv_eq_fderiv f x hx]
  rw [fromTangentSpace_euler_vector_field]
  -- Compare the derivative of the radial curve with the derivative of its homogeneous model.
  have hradial :
      HasDerivAt (fun t : ℝ ↦ f (t • x)) ((fderiv ℝ f x) x) 1 :=
    hasDerivAt_radialCurve hf_smooth x hx
  have hmodel :
      HasDerivAt (fun t : ℝ ↦ Real.rpow t c * f x) (c * f x) 1 :=
    hasDerivAt_homogeneousScalarCurve c f x
  have heq :
      (fun t : ℝ ↦ f (t • x)) =ᶠ[𝓝 1] (fun t ↦ Real.rpow t c * f x) :=
    radialHomogeneityEventuallyEq hf_homogeneous x hx
  have hmodel_radial :
      HasDerivAt (fun t : ℝ ↦ f (t • x)) (c * f x) 1 :=
    hmodel.congr_of_eventuallyEq heq.symm
  exact hradial.unique hmodel_radial

/-- Under the canonical tangent-space identification from Example 8.3, the intrinsic Euler-field
formula becomes the usual `x`-direction statement. -/
theorem euler_homogeneous_function_theorem_coord
    (hf_smooth : ContDiffOn ℝ ∞ f ({0} : Set E)ᶜ)
    (hf_homogeneous :
      ∀ ⦃t : ℝ⦄, 0 < t →
        ∀ ⦃x : E⦄, x ≠ 0 →
          f (t • x) = Real.rpow t c * f x)
    (x : E) (hx : x ≠ 0) :
    fderivWithin ℝ f ({0} : Set E)ᶜ x x = c * f x := by
  simpa using euler_homogeneous_function_theorem hf_smooth hf_homogeneous x hx

end
