import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u𝕜 uE uH uG

-- Domain sampling: the core owner is `LieGroup I ∞ G`, with primitive smooth multiplication
-- `ContMDiffMul I ∞ G` and derived inversion/division API from
-- `Mathlib.Geometry.Manifold.Algebra.LieGroup`.

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G] [IsManifold I ∞ G]

/-- Proposition 7.1. If `G` is a smooth manifold with a group structure such that the map
`G × G → G` given by `(g, h) ↦ g * h⁻¹` is smooth, then `G` is a Lie group. -/
theorem lieGroup_of_contMDiff_mul_inv
    (hdiv : ContMDiff (I.prod I) I ∞ fun p : G × G ↦ p.1 * p.2⁻¹) :
    LieGroup I ∞ G := by
  have hinv : ContMDiff I I ∞ (fun g : G ↦ g⁻¹) := by
    simpa using
      (show ContMDiff I I ∞ (fun g : G ↦ 1 * g⁻¹) from
        hdiv.comp (contMDiff_const.prodMk contMDiff_id))
  have hmul : ContMDiff (I.prod I) I ∞ fun p : G × G ↦ p.1 * p.2 := by
    simpa using
      (show ContMDiff (I.prod I) I ∞ (fun p : G × G ↦ p.1 * (p.2⁻¹)⁻¹) from
        hdiv.comp (contMDiff_fst.prodMk (hinv.comp contMDiff_snd)))
  exact { contMDiff_mul := hmul, contMDiff_inv := hinv }
