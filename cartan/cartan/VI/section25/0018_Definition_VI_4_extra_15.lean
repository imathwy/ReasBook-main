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

/-- The coefficient functions of a holomorphic differential form satisfy the chart transition
formula on every overlap of preferred complex charts. -/
theorem coeff_change_apply (ω : HolomorphicDifferentialForm X) {x y w : X}
    (hx : w ∈ (extChartAt 𝓘(ℂ) x).source) (hy : w ∈ (extChartAt 𝓘(ℂ) y).source) :
    ω.coeff y ((extChartAt 𝓘(ℂ) y) w) =
      ω.coeff x ((extChartAt 𝓘(ℂ) x) w) *
        deriv ((extChartAt 𝓘(ℂ) x) ∘ (extChartAt 𝓘(ℂ) y).symm) ((extChartAt 𝓘(ℂ) y) w) := sorry

end HolomorphicDifferentialForm
