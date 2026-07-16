import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_21.Exercise_4_4
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_28.Definition_5_28_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_28.Definition_5_28_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

section ConstantRankLevelSets

universe u𝕜 uE uE' uH uH' uM uN

open Manifold

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ∞ M]
variable {J : ModelWithCorners 𝕜 E' H'} [IsManifold J ∞ N]

-- Semantic search note: `lean_leansearch` was unavailable in this environment, so the statement
-- shape was matched against the local constant-rank API from `Exercise_4_4`, the embedded
-- submanifold API from `Definition_5_28_extra_1`, and the nearby level-set precedent in
-- `Corollary_5_13`.
-- Proof sketch: apply the constant-rank theorem pointwise on the level set to obtain local slice
-- coordinates of codimension `r`, then package the resulting manifold structure on the fiber.
/-- Theorem 5.12 (1) (Constant-Rank Level Set Theorem): each level set of a smooth constant-rank
map carries a smooth embedded submanifold structure whose codimension is the constant rank. -/
theorem constant_rank_level_set_has_embedded_submanifold_structure {r : ℕ} {Φ : M → N}
    (hΦsmooth : ContMDiff I J ∞ Φ) (hΦrank : HasConstantRank I J Φ r) (c : N) :
    let k : ℕ := Module.finrank 𝕜 E - r
    let S : Set M := Φ ⁻¹' {c}
    let K :=
      modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin k))
    ∃ cs : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) S,
        ∃ hs : IsManifold K ∞ S,
        let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) S := cs
        let _ : IsManifold K ∞ S := hs
        ∃ hS : IsEmbeddedSubmanifold I K S, hS.codimension = r := sorry

-- Proof sketch: the level set is the preimage of the closed singleton `{c}` under the continuous
-- map `Φ`, so it is closed in `M`; combine this with the embedded-submanifold structure from (1).
/-- Theorem 5.12 (2) (Constant-Rank Level Set Theorem): each level set of a smooth constant-rank
map is properly embedded in the ambient manifold. -/
theorem constant_rank_level_set_isProperlyEmbedded [T1Space N] {r : ℕ} {Φ : M → N}
    (hΦsmooth : ContMDiff I J ∞ Φ) (hΦrank : HasConstantRank I J Φ r) (c : N) :
    (Φ ⁻¹' {c}).IsProperlyEmbedded := sorry

end ConstantRankLevelSets
