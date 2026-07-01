import SmoothManifoldsLee.Chap05.Sec05_28.Definition_5_28_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-- Corollary 5.6: a compact subset of a Hausdorff space is properly embedded. In particular, any
compact embedded submanifold of a Hausdorff ambient space is properly embedded. -/
-- Proof sketch: a compact subset of a Hausdorff space is closed, and closed subsets are properly
-- embedded.
theorem IsCompact.isProperlyEmbedded {M : Type u}
    [TopologicalSpace M] [T2Space M] {S : Set M} (hS : IsCompact S) :
    S.IsProperlyEmbedded :=
  hS.isClosed.isProperlyEmbedded
