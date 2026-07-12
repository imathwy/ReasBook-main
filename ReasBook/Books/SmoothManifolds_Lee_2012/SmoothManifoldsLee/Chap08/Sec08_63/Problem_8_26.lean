import Mathlib.Algebra.Lie.Ideal
import SmoothManifolds_Lee_2012.Chap08.Sec08_61.Definition_8_61_extra_1
import SmoothManifolds_Lee_2012.Chap08.Sec08_62.Theorem_8_46

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold ContDiff ContMDiffMonoidMorphism

-- Domain sampling pass:
-- * source-facing owner: `LieSubgroup I`;
-- * core/canonical owners: `GroupLieAlgebra` and `LieHom.ker`;
-- * bridge/view: `ContMDiffMonoidMorphism.inducedLieAlgebraHomomorphism`.
-- The kernel statement is therefore phrased for a Lie subgroup structure on `ker F`, rather than
-- restating topology, charts, Lie-group data, and immersion data on the raw subgroup.

section

universe u𝕜 uE uH uG uE' uH' uG'

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [CompleteSpace E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable {G' : Type uG'} [Group G'] [TopologicalSpace G'] [ChartedSpace H' G']
variable [LieGroup I ∞ G] [LieGroup J ∞ G']
variable [LieGroup I (minSmoothness 𝕜 3) G] [LieGroup J (minSmoothness 𝕜 3) G']

namespace LieSubgroup

/-- Problem 8-26: if `K` is a Lie subgroup structure on `ker F`, then under the identification of
Theorem 8.46 its Lie algebra coincides with the kernel of the induced Lie algebra homomorphism
`F_*`. -/
theorem groupLieSubalgebra_eq_ker_inducedLieAlgebraHomomorphism
    (K : @LieSubgroup 𝕜 _ E _ _ H _ G _ _ _ I) [CompleteSpace K.ModelSpace]
    [LieGroup (modelWithCornersSelf 𝕜 K.ModelSpace) (minSmoothness 𝕜 3) K.carrier]
    (F : ContMDiffMonoidMorphism I J ∞ G G') (hK : K.carrier = F.toMonoidHom.ker) :
    groupLieSubalgebra K =
      ((LieHom.ker (F_*)) :
        LieSubalgebra 𝕜 (GroupLieAlgebra I G)) :=
  sorry

end LieSubgroup

end
