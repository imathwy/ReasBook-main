import Mathlib.Geometry.Manifold.SmoothEmbedding

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so local chapter
-- precedents and mathlib's `Manifold.IsImmersion` / `Manifold.IsSmoothEmbedding` APIs were
-- inspected directly.

open scoped ContDiff Manifold

namespace Manifold

section

universe uE uE' uH uH' uM uN

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners ℝ E H}
variable {J : ModelWithCorners ℝ E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- Theorem 4.25 (Local Embedding Theorem): a smooth map is a smooth immersion if and only if
every point of the source has an open neighborhood on which the restricted map is a smooth
embedding. -/
theorem isImmersion_iff_forall_exists_open_restriction_isSmoothEmbedding {F : M → N} :
    IsImmersion I J ∞ F ↔
      ∀ p : M, ∃ U : TopologicalSpace.Opens M, p ∈ U ∧
        IsSmoothEmbedding I J ∞ (F ∘ (Subtype.val : U → M)) := sorry

end

end Manifold
