import Mathlib

universe u

open scoped Manifold

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the manifold API was checked directly against `Mathlib.Geometry.Manifold.Complex` and
-- `Mathlib.Geometry.Manifold.MFDeriv.Atlas`, with the intrinsic one-form owner provided by
-- `Mathlib.Geometry.Manifold.MFDeriv.NormedSpace`.

-- Declarations for this item will be appended below by the statement pipeline.

/-- The chartwise coefficient of a manifold `1`-form on a complex manifold, obtained by evaluating
the form on the chart inverse's tangent image of the basis vector `1`. -/
noncomputable def chartCoeff
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (ω : (x : X) → TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ) (x : X) : ℂ → ℂ :=
  fun z ↦ ω ((extChartAt 𝓘(ℂ) x).symm z)
    (mfderivWithin 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) x).symm (Set.range (𝓘(ℂ))) z
      ((NormedSpace.fromTangentSpace z).symm 1))

/-- Definition VI.4-extra-15: a holomorphic differential form on a complex manifold is an
intrinsic manifold `1`-form whose coefficient in every preferred complex chart is holomorphic. The
textbook change-of-coordinates rule is then a derived consequence of the one-form owner. -/
structure HolomorphicDifferentialForm (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] where
  toOneForm : (x : X) → TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ
  holomorphic_coeff : ∀ x, DifferentiableOn ℂ (chartCoeff toOneForm x) ((extChartAt 𝓘(ℂ) x).target)

/-- A holomorphic differential form can be used as its underlying manifold `1`-form. -/
instance {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] :
    CoeFun (HolomorphicDifferentialForm X)
      (fun _ ↦ (x : X) → TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ) where
  coe ω := ω.toOneForm

namespace HolomorphicDifferentialForm

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

/-- The chartwise coefficient function of a holomorphic differential form. -/
noncomputable def coeff (ω : HolomorphicDifferentialForm X) (x : X) : ℂ → ℂ :=
  chartCoeff ω x

/-- The chartwise coefficient of a holomorphic differential form is holomorphic on the preferred
complex chart target. -/
theorem coeff_holomorphic (ω : HolomorphicDifferentialForm X) (x : X) :
    DifferentiableOn ℂ (ω.coeff x) ((extChartAt 𝓘(ℂ) x).target) :=
  ω.holomorphic_coeff x

/-- Cartan section25 0018_Definition_VI_4_extra_15: the coefficient functions of a holomorphic
differential form satisfy the chart transition formula on every overlap of preferred complex
charts. -/
theorem coeff_change_apply (ω : HolomorphicDifferentialForm X) {x y w : X}
    (hx : w ∈ (extChartAt 𝓘(ℂ) x).source) (hy : w ∈ (extChartAt 𝓘(ℂ) y).source) :
    ω.coeff y ((extChartAt 𝓘(ℂ) y) w) =
      ω.coeff x ((extChartAt 𝓘(ℂ) x) w) *
        deriv ((extChartAt 𝓘(ℂ) x) ∘ (extChartAt 𝓘(ℂ) y).symm) ((extChartAt 𝓘(ℂ) y) w) := by
  let g : ℂ → ℂ := (extChartAt 𝓘(ℂ) x) ∘ (extChartAt 𝓘(ℂ) y).symm
  let zy : ℂ := (extChartAt 𝓘(ℂ) y) w
  let zx : ℂ := (extChartAt 𝓘(ℂ) x) w
  have hleft : (extChartAt 𝓘(ℂ) y).symm zy = w := by
    simpa [zy] using (extChartAt 𝓘(ℂ) y).left_inv hy
  have hright : (extChartAt 𝓘(ℂ) x).symm zx = w := by
    simpa [zx] using (extChartAt 𝓘(ℂ) x).left_inv hx
  have hwx : w ∈ (chartAt ℂ x).source := by
    simpa [← extChartAt_source (I := 𝓘(ℂ))] using hx
  have houter : MDifferentiableAt (𝓘(ℂ)) (𝓘(ℂ)) (extChartAt 𝓘(ℂ) x) w := by
    exact mdifferentiableAt_extChartAt (I := 𝓘(ℂ)) (x := x) (y := w) hwx
  have houter_at_preimage : MDifferentiableAt (𝓘(ℂ)) (𝓘(ℂ)) (extChartAt 𝓘(ℂ) x)
      ((extChartAt 𝓘(ℂ) y).symm zy) := by
    rw [hleft]
    exact houter
  have hinner : MDifferentiableWithinAt (𝓘(ℂ)) (𝓘(ℂ)) (extChartAt 𝓘(ℂ) y).symm
      (Set.range (𝓘(ℂ))) zy := by
    simpa [zy] using
      (mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℂ)) ((extChartAt 𝓘(ℂ) y).map_source hy))
  have huy : UniqueMDiffWithinAt (𝓘(ℂ)) (Set.range (𝓘(ℂ))) zy := by
    simpa [zy] using
      (UniqueDiffWithinAt.uniqueMDiffWithinAt ((𝓘(ℂ)).uniqueDiffWithinAt_image (x := zy)))
  -- First identify the chart transition map as an honest complex-differentiable map on the model.
  have hdiff_g : DifferentiableAt ℂ g zy := by
    have hsymm : MDifferentiableAt (𝓘(ℂ)) (𝓘(ℂ)) (extChartAt 𝓘(ℂ) y).symm zy := by
      simpa [zy] using
        (mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℂ))
          ((extChartAt 𝓘(ℂ) y).map_source hy))
    have hmdiff_g : MDifferentiableAt (𝓘(ℂ)) (𝓘(ℂ)) g zy := by
      exact houter_at_preimage.comp zy hsymm
    exact MDifferentiableAt.differentiableAt hmdiff_g
  -- Then the chain rule expresses the transition derivative through the inverse chart of `y`.
  have hchain :
      mfderivWithin 𝓘(ℂ) 𝓘(ℂ) g (Set.range (𝓘(ℂ))) zy =
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) x) w).comp
          (mfderivWithin 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) y).symm (Set.range (𝓘(ℂ))) zy) := by
    simpa [g, Function.comp] using
      (mfderiv_comp_mfderivWithin_of_eq (I := 𝓘(ℂ)) (I' := 𝓘(ℂ)) (I'' := 𝓘(ℂ))
        (x := zy) (y := w) (g := extChartAt 𝓘(ℂ) x) (f := (extChartAt 𝓘(ℂ) y).symm)
        (s := Set.range (𝓘(ℂ))) houter hinner huy hleft)
  have hchain_apply :
      mfderivWithin 𝓘(ℂ) 𝓘(ℂ) g (Set.range (𝓘(ℂ))) zy
          ((NormedSpace.fromTangentSpace zy).symm 1) =
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) x) w)
          (mfderivWithin 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) y).symm (Set.range (𝓘(ℂ))) zy
            ((NormedSpace.fromTangentSpace zy).symm 1)) :=
    congrArg (fun e ↦ e ((NormedSpace.fromTangentSpace zy).symm 1)) hchain
  have hcomp_id :
      (mfderivWithin 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) x).symm (Set.range (𝓘(ℂ))) zx).comp
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) x) w) =
      ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ) w) := by
    simpa [zx] using
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := 𝓘(ℂ)) (x := x)
        (y := w) hx)
  -- Evaluating the transition derivative on the basis vector `1` produces the scalar `deriv g zy`.
  have hbasis :
      mfderiv 𝓘(ℂ) 𝓘(ℂ) g zy ((NormedSpace.fromTangentSpace zy).symm 1) =
        (NormedSpace.fromTangentSpace (g zy)).symm (deriv g zy) := by
    apply (NormedSpace.fromTangentSpace (g zy)).injective
    rw [mfderiv_eq_fderiv]
    rw [hdiff_g.hasDerivAt.hasFDerivAt.fderiv]
    change (ContinuousLinearMap.toSpanSingleton ℂ (deriv g zy))
        ((NormedSpace.fromTangentSpace zy) ((NormedSpace.fromTangentSpace zy).symm 1)) =
      deriv g zy
    simp
  have hmfderivWithin_g :
      mfderivWithin 𝓘(ℂ) 𝓘(ℂ) g (Set.range (𝓘(ℂ))) zy = mfderiv 𝓘(ℂ) 𝓘(ℂ) g zy := by
    exact mfderivWithin_eq_mfderiv huy (DifferentiableAt.mdifferentiableAt hdiff_g)
  have hbasisWithin :
      mfderivWithin 𝓘(ℂ) 𝓘(ℂ) g (Set.range (𝓘(ℂ))) zy
          ((NormedSpace.fromTangentSpace zy).symm 1) =
        (NormedSpace.fromTangentSpace (g zy)).symm (deriv g zy) := by
    rw [hmfderivWithin_g]
    exact hbasis
  have hgzy : g zy = zx := by
    simpa [g, zx] using congrArg (extChartAt 𝓘(ℂ) x) hleft
  let L : ℂ →L[ℂ] ℂ :=
    (ω w).comp (mfderivWithin 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) x).symm (Set.range (𝓘(ℂ))) zx) ∘L
      (NormedSpace.fromTangentSpace zx).symm.toContinuousLinearMap
  -- Finally, pull the scalar `deriv g zy` out through the composed linear map `L`.
  have hL : L (deriv g zy) = deriv g zy * L 1 := by
    calc
      L (deriv g zy) = L (deriv g zy • (1 : ℂ)) := by simp
      _ = deriv g zy • L 1 := by rw [map_smul]
      _ = deriv g zy * L 1 := by simp
  calc
    ω.coeff y zy
        = ω w
            (mfderivWithin 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) y).symm (Set.range (𝓘(ℂ))) zy
              ((NormedSpace.fromTangentSpace zy).symm 1)) := by
          rw [coeff, chartCoeff, hleft]
    _ = ω w
          (((mfderivWithin 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) x).symm (Set.range (𝓘(ℂ))) zx).comp
              (mfderiv 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) x) w))
            (mfderivWithin 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) y).symm (Set.range (𝓘(ℂ))) zy
              ((NormedSpace.fromTangentSpace zy).symm 1))) := by
          rw [hcomp_id]
          rfl
    _ = ω w
          ((mfderivWithin 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) x).symm (Set.range (𝓘(ℂ))) zx)
            (mfderivWithin 𝓘(ℂ) 𝓘(ℂ) g (Set.range (𝓘(ℂ))) zy
              ((NormedSpace.fromTangentSpace zy).symm 1))) := by
          rw [ContinuousLinearMap.comp_apply, hchain_apply.symm]
    _ = ω w
          ((mfderivWithin 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) x).symm (Set.range (𝓘(ℂ))) zx)
            ((NormedSpace.fromTangentSpace zx).symm (deriv g zy))) := by
          rw [hbasisWithin, hgzy]
    _ = L (deriv g zy) := by
          rfl
    _ = deriv g zy * L 1 := hL
    _ = deriv g zy * ω.coeff x zx := by
          rw [coeff, chartCoeff, hright]
          rfl
    _ = ω.coeff x zx * deriv g zy := by
          rw [mul_comm]

end HolomorphicDifferentialForm
