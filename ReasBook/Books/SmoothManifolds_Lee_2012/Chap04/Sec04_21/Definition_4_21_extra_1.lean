import SmoothManifolds_Lee_2012.Chap04.Sec04_21.Exercise_4_4

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool unavailable in this environment; local precedents used:
-- `Manifold.HasConstantRank` from `Exercise_4_4`, `Manifold.IsSmoothSubmersion` from the imported
-- section chain, and mathlib's `Manifold.IsImmersion`.

noncomputable section

open scoped ContDiff Manifold

namespace Manifold

universe uE uE' uH uH' uM uN

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
variable {J : ModelWithCorners ℝ E' H'} [IsManifold J ∞ N]

/-- Definition 4.21-extra-1 (1): the rank of `F` at `p` is the dimension of the image of its
manifold derivative at `p`. -/
theorem rank_at_eq_finrank_range_mfderiv {F : M → N} {p : M} :
    rankAt I J F p = Module.finrank ℝ ((mfderiv I J F p).range) := sorry

/-- Definition 4.21-extra-1 (2): a map has constant rank `r` exactly when its pointwise rank is
equal to `r` at every point. -/
theorem has_constant_rank_iff_forall_rank_at_eq {F : M → N} {r : ℕ} :
    HasConstantRank I J F r ↔ ∀ p : M, rankAt I J F p = r := sorry

/-- Definition 4.21-extra-1 (3): a map has full rank at `p` when its pointwise rank reaches the
smaller of the source and target manifold dimensions. -/
def has_full_rank_at (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
    (F : M → N) (p : M) : Prop :=
  rankAt I J F p = min (Module.finrank ℝ E) (Module.finrank ℝ E')

/-- `has_full_rank_at` means that the pointwise rank equals the minimum of the source and target
model-space dimensions. -/
theorem has_full_rank_at_iff_rank_at_eq_min_finrank {F : M → N} {p : M} :
    has_full_rank_at I J F p ↔
      rankAt I J F p = min (Module.finrank ℝ E) (Module.finrank ℝ E') := sorry

/-- Definition 4.21-extra-1 (4): a map has full rank when it has full rank at every point. -/
def has_full_rank (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
    (F : M → N) : Prop :=
  ∀ p : M, has_full_rank_at I J F p

/-- Full rank is a pointwise condition. -/
theorem has_full_rank_iff_forall_has_full_rank_at {F : M → N} :
    has_full_rank I J F ↔ ∀ p : M, has_full_rank_at I J F p := sorry

/-- Definition 4.21-extra-1 (5): for a smooth map, being a smooth submersion is equivalent to
surjectivity of the manifold derivative at every point. -/
theorem is_smooth_submersion_iff_forall_surjective_mfderiv {F : M → N}
    (hF : ContMDiff I J ∞ F) :
    IsSmoothSubmersion I J F ↔ ∀ p : M, Function.Surjective (mfderiv I J F p) := sorry

/-- A smooth submersion has full rank at every point. -/
theorem IsSmoothSubmersion.has_full_rank {F : M → N} (hF : IsSmoothSubmersion I J F) :
    has_full_rank I J F := sorry

/-- Definition 4.21-extra-1 (6): for a smooth map, being a smooth immersion is equivalent to
injectivity of the manifold derivative at every point. -/
theorem is_immersion_iff_forall_injective_mfderiv {F : M → N}
    (hF : ContMDiff I J ∞ F) :
    IsImmersion I J ∞ F ↔ ∀ p : M, Function.Injective (mfderiv I J F p) := sorry

/-- A smooth immersion has full rank at every point. -/
theorem IsImmersion.has_full_rank {F : M → N} (hF : IsImmersion I J ∞ F) :
    has_full_rank I J F := sorry

end

end Manifold
