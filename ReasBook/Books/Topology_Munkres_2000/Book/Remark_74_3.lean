module

import Mathlib.Geometry.Manifold.SmoothEmbedding

public section

/- Remark 74.3: A self-intersecting picture of the `m`-fold projective plane in `ℝ³`
is described smoothly by an immersion rather than an embedding. The canonical
mathlib notions are `Manifold.IsImmersion` and `Manifold.IsSmoothEmbedding`. -/
#check Manifold.IsImmersion
#check Manifold.IsSmoothEmbedding
#check Manifold.IsSmoothEmbedding.isImmersion
