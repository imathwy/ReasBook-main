import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_21.Definition_4_21_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_24.Example_4_19
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_31.Definition_5_31_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search note: no `lean_leansearch` tool was available in this environment; the
-- statement was matched against the local figure-eight API in `Example_4_19`, the earlier
-- immersed-submanifold infrastructure, and mathlib's periodicity API.

open Topology

open Manifold

open scoped ContDiff Manifold

local notation "Plane" => ℝ × ℝ

/-- Helper for Example 5.28: the parameter value `0` lies in the interval `(-π, π)`. -/
theorem figureEightCurve_zero_mem_parameterInterval :
    (0 : ℝ) ∈ Set.Ioo (-Real.pi) Real.pi := by
  -- Both inequalities are immediate from the positivity of `π`.
  constructor
  · simpa using neg_lt_zero.mpr Real.pi_pos
  · simpa using Real.pi_pos

/-- Helper for Example 5.28: the parameter interval is nonempty, with distinguished point `0`. -/
instance : Nonempty (Set.Ioo (-Real.pi) Real.pi) :=
  ⟨⟨0, figureEightCurve_zero_mem_parameterInterval⟩⟩

/-- Helper for Example 5.28: a nonzero continuous linear map out of the one-dimensional source
`ℝ` is injective. -/
theorem continuous_linearMap_injective_of_ne_zero_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : ℝ →L[ℝ] E} (hL : L ≠ 0) :
    Function.Injective L := by
  -- Reduce to the corresponding linear-map fact for the source module `ℝ`.
  exact LinearMap.injective_of_ne_zero (f := L.toLinearMap) <| by
    intro hzero
    exact hL <| ContinuousLinearMap.ext fun x ↦ DFunLike.congr_fun hzero x

/-- Helper for Example 5.28: the parameter interval `(-π, π)` inherits the charted-space
structure coming from its open inclusion into `ℝ`. -/
noncomputable instance instChartedSpace_parameterInterval :
    ChartedSpace ℝ (Set.Ioo (-Real.pi) Real.pi) := by
  let U : TopologicalSpace.Opens ℝ := ⟨Set.Ioo (-Real.pi) Real.pi, isOpen_Ioo⟩
  -- Use the canonical open-subtype charted space so the standard open-subset API applies.
  change ChartedSpace ℝ U
  infer_instance

/-- Helper for Example 5.28: with the induced charts, the parameter interval `(-π, π)` is a smooth
boundaryless `1`-manifold. -/
instance instIsManifold_parameterInterval :
    IsManifold (𝓘(ℝ)) (⊤ : WithTop ℕ∞) (Set.Ioo (-Real.pi) Real.pi) := by
  let U : TopologicalSpace.Opens ℝ := ⟨Set.Ioo (-Real.pi) Real.pi, isOpen_Ioo⟩
  -- Re-express the interval as the canonical open subtype of `ℝ`.
  change IsManifold (𝓘(ℝ)) (⊤ : WithTop ℕ∞) U
  infer_instance

/-- Helper for Example 5.28: the open-interval inclusion into `ℝ` is an `∞`-immersion. -/
theorem figureEightCurve_parameterInterval_subtype_val_isImmersion :
    IsImmersion 𝓘(ℝ) 𝓘(ℝ) ∞
      (Subtype.val : Set.Ioo (-Real.pi) Real.pi → ℝ) := by
  let U : TopologicalSpace.Opens ℝ := ⟨Set.Ioo (-Real.pi) Real.pi, isOpen_Ioo⟩
  -- The canonical open-subtype inclusion is an immersion for every differentiability order.
  change IsImmersion 𝓘(ℝ) 𝓘(ℝ) ∞ (Subtype.val : U → ℝ)
  simpa [U] using Manifold.IsImmersion.of_opens (I := 𝓘(ℝ)) (n := ∞) U

/-- Helper for Example 5.28: the ambient figure-eight derivative never vanishes on `ℝ`. -/
theorem figureEightCurveMap_fderiv_ne_zero_real (t : ℝ) :
    fderiv ℝ figureEightCurveMap t ≠ 0 := by
  have hfderiv :
      fderiv ℝ figureEightCurveMap t =
        (1 : ℝ →L[ℝ] ℝ).smulRight (2 * Real.cos (2 * t), Real.cos t) := by
    -- Rewrite the Fréchet derivative using the explicit velocity vector of the ambient curve.
    simpa using (figureEightCurveMap_hasDerivAt t).hasFDerivAt.fderiv
  intro hzero
  have hvec_zero : (2 * Real.cos (2 * t), Real.cos t) = (0, 0) := by
    -- Evaluating the derivative at `1` recovers the velocity vector itself.
    have happly : (fderiv ℝ figureEightCurveMap t) 1 = 0 := by
      simp [hzero]
    rw [hfderiv, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, one_smul] at happly
    simpa using happly
  have hcoord₁ : 2 * Real.cos (2 * t) = 0 := congrArg Prod.fst hvec_zero
  have hcoord₂ : Real.cos t = 0 := congrArg Prod.snd hvec_zero
  have hcos_two_zero : Real.cos (2 * t) = 0 := by
    nlinarith [hcoord₁]
  have hsin_sq : Real.sin t ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq t, hcoord₂]
  have hcos_two_neg : Real.cos (2 * t) = -1 := by
    -- The double-angle identity forces `cos (2t) = -1` once `cos t = 0`.
    rw [Real.cos_two_mul]
    nlinarith [hcoord₂, hsin_sq]
  linarith [hcos_two_zero, hcos_two_neg]

/-- Helper for Example 5.28: the manifold derivative of the ambient figure-eight map is injective
at every real parameter because its Fréchet derivative never vanishes. -/
theorem figureEightCurveMap_mfderiv_injective_real (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) figureEightCurveMap t) := by
  have hNonzero : mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) figureEightCurveMap t ≠ 0 := by
    -- On Euclidean spaces, the manifold derivative agrees with the usual Fréchet derivative.
    rw [mfderiv_eq_fderiv]
    exact figureEightCurveMap_fderiv_ne_zero_real t
  -- A nonzero linear map out of the one-dimensional source `ℝ` must be injective.
  exact continuous_linearMap_injective_of_ne_zero_real (E := Plane) hNonzero

/-- Helper for Example 5.28: the ambient extension `G(t) = (sin (2t), sin t)` is an
`∞`-immersion on all of `ℝ`. -/
theorem figureEightCurveMap_isImmersion :
    IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ∞ figureEightCurveMap := by
  have hcurveMap :
      ContMDiff 𝓘(ℝ) 𝓘(ℝ, Plane) ∞ figureEightCurveMap := by
    -- Convert the known Euclidean `C^∞` regularity into the manifold formulation.
    rw [contMDiff_iff_contDiff]
    simpa using figureEightCurveMap_contDiff
  -- The top-order immersion criterion reduces the goal to injectivity of the manifold derivative.
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv hcurveMap).2 ?_
  intro t
  exact figureEightCurveMap_mfderiv_injective_real t

/-- Helper for Example 5.28: the inclusion of the parameter interval into `ℝ` is an
`∞`-immersion. -/
theorem figureEightCurve_isImmersion :
    IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ∞ figureEightCurve := by
  -- The restricted parametrization is the ambient immersion composed with the open inclusion.
  simpa [figureEightCurve, Function.comp] using
    Manifold.IsImmersion.comp figureEightCurveMap_isImmersion
      figureEightCurve_parameterInterval_subtype_val_isImmersion

/-- Helper for Example 5.28: the restricted parametrization should also be available at the
canonical `ω`-regularity level used by `ImmersedSubmanifold`. -/
theorem figureEightCurve_isImmersion_top :
    IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) figureEightCurve := by
  -- Route correction: the derivative criterion in the repo closes the `∞`-level immersion, but
  -- the immersed-submanifold packaging needs the outer `ω` regularity instead.
  -- TODO: prove this by the source-faithful branch-local straightening route, using the nonzero
  -- coordinate derivative to build an explicit `ω`-smooth codomain chart and then restricting it
  -- along the open inclusion `(-π, π) ↪ ℝ`.
  sorry

/-- Helper for Example 5.28: the figure-eight immersion defines an immersed submanifold of the
plane. -/
noncomputable abbrev figureEightCurveImmersedSubmanifold :
    ImmersedSubmanifold 𝓘(ℝ, Plane) Plane :=
  figureEightCurve_isImmersion_top.toImmersedSubmanifold figureEightCurve_injective

/-- Helper for Example 5.28: the underlying subset of the immersed figure-eight is the image of
the parametrization `figureEightCurve`. -/
theorem figureEightCurveImmersedSubmanifold_carrier :
    figureEightCurveImmersedSubmanifold.carrier = Set.range figureEightCurve :=
  rfl

/-- Helper for Example 5.28: the ambient figure-eight parametrization repeats with period
`2π`. -/
theorem figureEightCurveMap_periodic : Function.Periodic figureEightCurveMap (2 * Real.pi) := by
  intro t
  -- Check both coordinates after rewriting the first argument as a `2π`-shift.
  ext
  · have harg : 2 * (t + 2 * Real.pi) = 2 * t + 2 * (2 * Real.pi) := by
      ring
    rw [figureEightCurveMap, figureEightCurveMap, harg]
    simpa using Real.sin_add_nat_mul_two_pi (2 * t) 2
  · -- The second coordinate is the standard `2π`-periodicity of `sin`.
    rw [figureEightCurveMap, figureEightCurveMap]
    simpa using Real.sin_add_two_pi t

/-- Helper for Example 5.28: the periodic extension has the same range as the original
parametrization on `(-π, π)`. -/
theorem figureEightCurveMap_range_eq_range_figureEightCurve :
    Set.range figureEightCurveMap = Set.range figureEightCurve := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    -- Move the parameter into a single fundamental interval and then use the closed-interval API.
    rcases figureEightCurveMap_periodic.exists_mem_Ioc Real.two_pi_pos t (-Real.pi) with
      ⟨u, hu, hperiodic⟩
    have hu_closed : u ∈ Set.Icc (-Real.pi) Real.pi := by
      have hu' : u ∈ Set.Icc (-Real.pi) (-Real.pi + 2 * Real.pi) := Set.Ioc_subset_Icc_self hu
      constructor
      · exact hu'.1
      · nlinarith [hu'.2]
    have hu_range : figureEightCurveMap u ∈ Set.range figureEightCurve := by
      rw [← figureEightCurve_closed_range_eq_restricted_range]
      exact ⟨⟨u, hu_closed⟩, rfl⟩
    rw [hperiodic]
    exact hu_range
  · rintro ⟨t, rfl⟩
    -- Any point already reached by the restricted parametrization is certainly reached globally.
    exact ⟨t, (figureEightCurve_eq_figureEightCurveMap t).symm⟩

/-- Helper for Example 5.28: the sequence `π - 1/(n+1)` stays inside the original parameter
interval `(-π, π)`. -/
theorem figureEightCurveApproachPi_mem_parameterInterval (n : ℕ) :
    Real.pi - 1 / (n + 1 : ℝ) ∈ Set.Ioo (-Real.pi) Real.pi := by
  have hfrac_pos : 0 < 1 / (n + 1 : ℝ) := by
    positivity
  have hfrac_le_one : 1 / (n + 1 : ℝ) ≤ 1 := by
    simpa [one_div] using (Nat.cast_inv_le_one (α := ℝ) (n + 1))
  have hone_lt_two_pi : (1 : ℝ) < 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hfrac_lt_two_pi : 1 / (n + 1 : ℝ) < 2 * Real.pi := by
    exact lt_of_le_of_lt hfrac_le_one hone_lt_two_pi
  -- The upper bound uses positivity of `1 / (n + 1)`, and the lower bound uses
  -- `1 / (n + 1) < 2π`.
  constructor
  · nlinarith
  · nlinarith

/-- Helper for Example 5.28: along the interior sequence approaching `π`, the chosen inverse
branch agrees with the original parameter. -/
theorem figureEightCurve_invFun_comp_approach_pi_eq (n : ℕ) :
    Function.invFun figureEightCurve (figureEightCurveMap (Real.pi - 1 / (n + 1 : ℝ))) =
      ⟨Real.pi - 1 / (n + 1 : ℝ), figureEightCurveApproachPi_mem_parameterInterval n⟩ := by
  -- On the interior interval, `invFun` is the genuine left inverse of the injective
  -- parametrization `figureEightCurve`.
  simpa [figureEightCurve_eq_figureEightCurveMap] using
    (Function.leftInverse_invFun figureEightCurve_injective
      ⟨Real.pi - 1 / (n + 1 : ℝ), figureEightCurveApproachPi_mem_parameterInterval n⟩)

/-- Helper for Example 5.28: at the endpoint `π`, the periodic extension hits the double point
corresponding to the interior parameter `0`. -/
theorem figureEightCurve_invFun_comp_at_pi_eq_zero :
    Function.invFun figureEightCurve (figureEightCurveMap Real.pi) =
      ⟨0, figureEightCurve_zero_mem_parameterInterval⟩ := by
  have hpi_eq_zero : figureEightCurveMap Real.pi = figureEightCurveMap 0 := by
    -- Evaluate the periodic extension at `π` and at `0` coordinatewise.
    simp [figureEightCurveMap, Real.sin_pi, Real.sin_two_pi]
  -- Rewrite the endpoint value to the interior parameter `0`, where `invFun` is a left inverse.
  rw [hpi_eq_zero]
  simpa [figureEightCurve_eq_figureEightCurveMap] using
    (Function.leftInverse_invFun figureEightCurve_injective
      ⟨0, figureEightCurve_zero_mem_parameterInterval⟩)

/-- Example 5.28 (1): the extended figure-eight map `G(t) = (sin (2t), sin t)` still lands in the
carrier of the immersed figure-eight submanifold. -/
theorem figureEightCurveMap_mem_figureEightCurveImmersedSubmanifold_carrier (t : ℝ) :
    figureEightCurveMap t ∈ figureEightCurveImmersedSubmanifold.carrier := by
  -- Identify the immersed carrier with the original figure-eight image and use the range equality.
  rw [figureEightCurveImmersedSubmanifold_carrier]
  rw [← figureEightCurveMap_range_eq_range_figureEightCurve]
  exact ⟨t, rfl⟩

/-- Example 5.28 (2): when the figure-eight is given the topology induced by the immersion
`β : (-π, π) → ℝ²`, the lifted map `β⁻¹ ∘ G`, represented here by
`Function.invFun figureEightCurve ∘ figureEightCurveMap`, is not continuous at `π`. -/
theorem figureEightCurve_invFun_comp_figureEightCurveMap_not_continuousAt_pi :
    ¬ ContinuousAt (Function.invFun figureEightCurve ∘ figureEightCurveMap) Real.pi := by
  intro hcont
  let u : ℕ → ℝ := fun n ↦ Real.pi - 1 / (n + 1 : ℝ)
  let liftVal : ℝ → ℝ := fun t ↦
    (((Function.invFun figureEightCurve (figureEightCurveMap t)) :
      Set.Ioo (-Real.pi) Real.pi) : ℝ)
  have hcont_val :
      ContinuousAt liftVal Real.pi := by
    -- Compose the assumed continuity with the subtype projection to reduce to an `ℝ`-valued map.
    simpa [liftVal, Function.comp] using (continuous_subtype_val.continuousAt.comp hcont)
  have hu_tendsto : Filter.Tendsto u Filter.atTop (𝓝 Real.pi) := by
    -- The sequence `π - 1 / (n + 1)` approaches `π` because `1 / (n + 1) → 0`.
    have hdiv : Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1 : ℝ)) Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [u] using (Filter.Tendsto.sub tendsto_const_nhds hdiv)
  have hvalue_tendsto :
      Filter.Tendsto (fun n ↦ liftVal (u n)) Filter.atTop (𝓝 (liftVal Real.pi)) :=
    hcont_val.tendsto.comp hu_tendsto
  have hat_pi_val : liftVal Real.pi = 0 := by
    -- The value at `π` is the branch-point parameter `0`.
    simpa [liftVal] using congrArg Subtype.val figureEightCurve_invFun_comp_at_pi_eq_zero
  have hvalue_zero_tendsto :
      Filter.Tendsto (fun n ↦ liftVal (u n)) Filter.atTop (𝓝 0) := by
    simpa [hat_pi_val] using hvalue_tendsto
  have hu_eq : (fun n ↦ liftVal (u n)) = u := by
    -- Along the interior sequence, the chosen inverse branch simply returns the parameter itself.
    funext n
    simpa [liftVal, u] using
      congrArg Subtype.val (figureEightCurve_invFun_comp_approach_pi_eq n)
  have hu_zero_tendsto : Filter.Tendsto u Filter.atTop (𝓝 0) := by
    rw [← hu_eq]
    exact hvalue_zero_tendsto
  have hpi_eq_zero : Real.pi = 0 := tendsto_nhds_unique hu_tendsto hu_zero_tendsto
  -- The unique-limit comparison contradicts the positivity of `π`.
  linarith [Real.pi_pos, hpi_eq_zero]
