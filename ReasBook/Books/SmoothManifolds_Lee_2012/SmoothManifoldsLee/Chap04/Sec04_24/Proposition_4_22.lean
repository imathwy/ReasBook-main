import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Topology.Maps.Proper.Basic

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool unavailable in this environment; local precedents used:
-- `Proposition_4_8`, `Exercise_4_9`, `Problem_4_2`, and mathlib's
-- `Manifold.IsSmoothEmbedding` / `IsProperMap` APIs.

open scoped Manifold ContDiff

universe uE uE' uH uH' uM uN

section GeneralCases

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners ℝ E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
variable {F : M → N}

/-- Proposition 4.22 (1): an injective smooth immersion that is an open map is a smooth
embedding. -/
theorem smooth_embedding_of_injective_isImmersion_isOpenMap
    (h_inj : Function.Injective F)
    (hF : Manifold.IsImmersion I J ∞ F)
    (h_open : IsOpenMap F) :
    Manifold.IsSmoothEmbedding I J ∞ F := sorry

/-- Proposition 4.22 (2): an injective smooth immersion that is a closed map is a smooth
embedding. -/
theorem smooth_embedding_of_injective_isImmersion_isClosedMap
    (h_inj : Function.Injective F)
    (hF : Manifold.IsImmersion I J ∞ F)
    (h_closed : IsClosedMap F) :
    Manifold.IsSmoothEmbedding I J ∞ F := sorry

/-- Proposition 4.22 (3): an injective smooth immersion that is proper is a smooth embedding. -/
theorem smooth_embedding_of_injective_isImmersion_isProperMap
    (h_inj : Function.Injective F)
    (hF : Manifold.IsImmersion I J ∞ F)
    (h_proper : IsProperMap F) :
    Manifold.IsSmoothEmbedding I J ∞ F := sorry

/-- Proposition 4.22 (4): if the source manifold is compact, then an injective smooth immersion is
a smooth embedding. -/
theorem smooth_embedding_of_compact_source_injective_isImmersion
    [CompactSpace M] [T2Space N]
    (h_inj : Function.Injective F)
    (hF : Manifold.IsImmersion I J ∞ F) :
    Manifold.IsSmoothEmbedding I J ∞ F := sorry

end GeneralCases

section EqualDimensionCase

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners ℝ E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
variable {F : M → N}

/-- Proposition 4.22 (5): if the source manifold has empty boundary and the source and target have
the same dimension, then an injective smooth immersion is a smooth embedding. -/
theorem smooth_embedding_of_injective_isImmersion_boundaryless_of_eq_finrank
    (h_dim : Module.finrank ℝ E = Module.finrank ℝ E')
    (h_inj : Function.Injective F)
    (hF : Manifold.IsImmersion I J ∞ F) :
    Manifold.IsSmoothEmbedding I J ∞ F := sorry

end EqualDimensionCase
