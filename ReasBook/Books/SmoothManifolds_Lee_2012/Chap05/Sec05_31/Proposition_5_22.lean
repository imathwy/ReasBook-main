import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Topology.Sets.Opens
import SmoothManifolds_Lee_2012.Chap05.Sec05_31.Definition_5_31_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace
open scoped Manifold

universe u𝕜 uE uH uM

namespace Manifold
namespace ImmersedSubmanifold

section

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I (⊤ : WithTop ℕ∞) M]

-- Semantic recall note: `lean_leansearch` was unavailable in this session, so the statement
-- surface was verified against the local `Theorem_4_25` and `ImmersedSubmanifold` APIs.
/-- Proposition 5.22 (Immersed Submanifolds Are Locally Embedded): for each point `p` of an
immersed submanifold `S` of `M`, there is an open neighborhood `U` of `p` in `S` such that the
restricted inclusion `U → M` is a smooth embedding. Hence `U` is an embedded submanifold of `M`
in the source sense. -/
theorem exists_open_neighborhood_isSmoothEmbedding (S : ImmersedSubmanifold I M) (p : S) :
    ∃ U : Opens S, p ∈ U ∧
      IsSmoothEmbedding (modelWithCornersSelf 𝕜 S.ModelSpace) I (⊤ : WithTop ℕ∞)
        (S.inclusion ∘ (Subtype.val : U → S)) := sorry

end

end ImmersedSubmanifold
end Manifold
