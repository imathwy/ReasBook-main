import Mathlib
import SmoothManifoldsLee.Chap04.Sec04_21.Definition_4_21_extra_1

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so local chapter
-- precedents and mathlib APIs were inspected directly.

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

/-- Proposition 4.1 (1): if the manifold derivative of a smooth map is surjective at `p`, then
`p` has an open neighborhood on which the restricted map is a smooth submersion. -/
theorem exists_open_restriction_isSmoothSubmersion_of_surjective_mfderiv {F : M → N} {p : M}
    (hF : ContMDiff I J ∞ F) (hp : Function.Surjective (mfderiv I J F p)) :
    ∃ U : TopologicalSpace.Opens M, p ∈ U ∧
      IsSmoothSubmersion I J (F ∘ (Subtype.val : U → M)) := sorry

/-- Proposition 4.1 (2): if the manifold derivative of a smooth map is injective at `p`, then
`p` has an open neighborhood on which the restricted map is a smooth immersion. -/
theorem exists_open_restriction_isImmersion_of_injective_mfderiv {F : M → N} {p : M}
    (hF : ContMDiff I J ∞ F) (hp : Function.Injective (mfderiv I J F p)) :
    ∃ U : TopologicalSpace.Opens M, p ∈ U ∧
      IsImmersion I J ∞ (F ∘ (Subtype.val : U → M)) := sorry

end

end Manifold
