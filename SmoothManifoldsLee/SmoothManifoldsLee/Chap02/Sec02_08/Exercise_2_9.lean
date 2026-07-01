import Mathlib.Geometry.Manifold.ContMDiff.Defs

-- Declarations for this item will be appended below by the statement pipeline.

universe u_𝕜 uE uH uM uE' uH' uM'

open Set ChartedSpace IsManifold
open scoped Manifold ContDiff

variable
  {𝕜 : Type u_𝕜} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type uH} [TopologicalSpace H]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type uH'} [TopologicalSpace H']
  {M' : Type uM'} [TopologicalSpace M'] [ChartedSpace H' M']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}

/-- Exercise 2.9: for any pair of smooth charts on the source and target manifolds, the coordinate
representation of a smooth map is smooth on the overlap where both charts are defined. -/
-- Proof sketch: apply `contMDiffOn_iff_of_mem_maximalAtlas'` to the set
-- `e.source ∩ F ⁻¹' e'.source`, using `hF.contMDiffOn`.
theorem contDiffOn_coord_repr_of_contMDiff
    [IsManifold I ∞ M] [IsManifold I' ∞ M']
    {F : M → M'} {e : OpenPartialHomeomorph M H} {e' : OpenPartialHomeomorph M' H'}
    (hF : ContMDiff I I' ∞ F)
    (he : e ∈ maximalAtlas I ∞ M) (he' : e' ∈ maximalAtlas I' ∞ M') :
    ContDiffOn 𝕜 ∞ (e'.extend I' ∘ F ∘ (e.extend I).symm)
      (e.extend I '' (e.source ∩ F ⁻¹' e'.source)) := by
  let s : Set M := e.source ∩ F ⁻¹' e'.source
  have hs : s ⊆ e.source := fun _ hx ↦ hx.1
  have hFs : MapsTo F s e'.source := fun _ hx ↦ hx.2
  simpa [s] using (contMDiffOn_iff_of_mem_maximalAtlas' he he' hs hFs).1 hF.contMDiffOn
