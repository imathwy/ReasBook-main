import Mathlib.Geometry.Manifold.ContMDiffMap

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

universe uE uH uS

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {S : Type uS} [TopologicalSpace S] [ChartedSpace H S]

/- Notation 5.34-extra-1: for a charted space, and in particular for a smooth manifold, modeled by
`I`, the notation `C^∞⟮I, S; ℝ⟯` is the canonical type of smooth real-valued functions on `S`.
Thus the book's convention `f ∈ C^∞(S)` refers to smoothness on `S` itself, not merely to the
existence of local smooth extensions from the ambient subset. -/
#check (C^∞⟮I, S; ℝ⟯)
