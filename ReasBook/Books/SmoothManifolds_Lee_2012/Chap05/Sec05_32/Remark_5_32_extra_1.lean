import SmoothManifolds_Lee_2012.Chap05.Sec05_32.Corollary_5_30
import SmoothManifolds_Lee_2012.Chap05.Sec05_32.Definition_5_32_extra_2

open scoped ContDiff Manifold

universe u𝕜 uE uH uM uE' uH'

section EmbeddedSubmanifoldsAreWeaklyEmbedded

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ⊤ M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners 𝕜 E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J ⊤ S] [IsEmbeddedSubmanifold I J S]

/-- Remark 5.32-extra-1: every embedded submanifold is weakly embedded. -/
instance : IsWeaklyEmbeddedSubmanifold I J S where
  toBoundarylessManifold := inferInstance
  isImmersion_subtype_val := IsEmbeddedSubmanifold.isSmoothEmbedding_subtype_val.isImmersion
  contMDiff_toSubtype := by
    intro E'' _ _ H'' _ N _ _ K _ F hF hFS
    exact contMDiff_toSubtype_of_isEmbeddedSubmanifold hF hFS

end EmbeddedSubmanifoldsAreWeaklyEmbedded
