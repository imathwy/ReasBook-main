import Mathlib
import SmoothManifolds_Lee_2012.Chap04.Sec04_21.Exercise_4_3
import SmoothManifolds_Lee_2012.Chap04.Sec04_22.Proposition_4_8
import SmoothManifolds_Lee_2012.Chap07.Sec07_53.Problem_7_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff
open Manifold

universe uE uH uG
universe u𝕜

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable [ContMDiffMul I ∞ G]

/-- Problem 7-1: for any Lie group `G`, the multiplication map `m : G × G → G`,
`m (g, h) = g * h`, is a smooth submersion. More generally, smooth multiplication alone suffices. -/
theorem lie_group_multiplication_isSmoothSubmersion :
    IsSmoothSubmersion (I.prod I) I (fun p : G × G ↦ p.1 * p.2) := by
  simpa [Function.comp] using
    (prod_snd_isSmoothSubmersion.comp_isLocalDiffeomorph
      multiplication_shear_isLocalDiffeomorph)
