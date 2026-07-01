import SmoothManifoldsLee.Chap01.Sec01_02.Definition_1_2_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open ChartedSpace

universe u𝕜 uE uH uM

namespace OpenPartialHomeomorph

/-- Definition 1.2-extra-3 (source-facing): a smooth atlas on `M` is a collection of charts whose
domains cover `M`, with pairwise compatibility expressed through the canonical smooth structure
groupoid. By `Definition_1_2_extra_2`, this is equivalent to Lee's "disjoint or smooth transition
map" wording. -/
class IsSmoothAtlas {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    {M : Type uM} [TopologicalSpace M]
    (A : Set (OpenPartialHomeomorph M H)) : Prop where
  cover (x : M) : ∃ e ∈ A, x ∈ e.source
  compatible {e e' : OpenPartialHomeomorph M H} (he : e ∈ A) (he' : e' ∈ A) :
    e.symm ≫ₕ e' ∈ contDiffGroupoid ∞ I

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M]
variable {I : ModelWithCorners 𝕜 E H}

variable [ChartedSpace H M]

/-- For the charted-space atlas, being a smooth atlas is exactly the canonical smooth
compatibility condition `HasGroupoid`. -/
theorem isSmoothAtlas_atlas_iff :
    IsSmoothAtlas I (atlas H M) ↔ HasGroupoid M (contDiffGroupoid ∞ I) := by
  constructor
  · intro h
    exact ⟨fun he he' ↦ h.compatible he he'⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro x
      exact ⟨chartAt H x, chart_mem_atlas H x, mem_chart_source H x⟩
    · intro e e' he he'
      exact h.compatible he he'

/-- Any charted-space atlas compatible with the smooth structure groupoid is a smooth atlas. -/
instance [HasGroupoid M (contDiffGroupoid ∞ I)] :
    IsSmoothAtlas I (atlas H M) where
  cover x := ⟨chartAt H x, chart_mem_atlas H x, mem_chart_source H x⟩
  compatible he he' := HasGroupoid.compatible he he'

end OpenPartialHomeomorph
