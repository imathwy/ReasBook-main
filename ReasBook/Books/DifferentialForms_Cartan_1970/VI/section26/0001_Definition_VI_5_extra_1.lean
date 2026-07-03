import Mathlib.Geometry.Manifold.Complex

open scoped Manifold

universe u uE uH uY

-- Domain sampling: this item sits in the one-dimensional complex-manifold domain. The relevant
-- owner declarations inspected before this repair were:
-- * the chapter-local `ComplexManifold` / `ComplexManifoldStructure` owner layer from
--   `section25/0005_Definition_VI_4_extra_5.lean`, which records the textbook Hausdorff
--   semantics of complex manifolds;
-- * mathlib's operational holomorphic interface `MDifferentiable` on `ChartedSpace` /
--   `IsManifold`;
-- * the immediate downstream section-26 use in `0009_Theorem_VI_5_extra_9.lean`.
-- The primitive data of a spread surface is the total-space topology/manifold structure,
-- connectedness, and the holomorphic projection. The Hausdorff condition belongs to the complex-
-- manifold owner layer already fixed in section 25, so it must be part of this source-facing
-- owner as well.

/-- Definition VI.5-extra-1: a Riemann surface spread over a complex manifold `Y` is a connected
one-dimensional complex manifold `X` equipped with a nonconstant holomorphic map `X → Y`. -/
structure RiemannSurfaceOver
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℂ E H) [I.Boundaryless]
    (Y : Type uY) [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I 1 Y] [T2Space Y] where
  carrier : Type u
  topology : TopologicalSpace carrier
  t2Space : T2Space carrier
  chartedSpace : ChartedSpace ℂ carrier
  isManifold : IsManifold 𝓘(ℂ) 1 carrier
  connected : ConnectedSpace carrier
  projection : carrier → Y
  mdiff_projection : MDifferentiable 𝓘(ℂ) I projection
  nonconstant_projection : ∃ x₁ x₂ : carrier, projection x₁ ≠ projection x₂

section

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
    {Y : Type uY} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I 1 Y] [T2Space Y]

/-- A Riemann surface over `Y` can be used as its total-space type. -/
instance : CoeSort (RiemannSurfaceOver I Y) (Type u) where
  coe X := X.carrier

attribute [instance] RiemannSurfaceOver.topology
attribute [instance] RiemannSurfaceOver.t2Space
attribute [instance] RiemannSurfaceOver.chartedSpace
attribute [instance] RiemannSurfaceOver.isManifold
attribute [instance] RiemannSurfaceOver.connected

end
