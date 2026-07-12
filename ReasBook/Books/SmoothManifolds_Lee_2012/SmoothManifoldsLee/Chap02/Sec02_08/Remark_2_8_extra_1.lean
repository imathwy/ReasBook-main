import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Tactic.Recall

open scoped Manifold ContDiff

universe uE uH uM uE' uH' uN

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]

variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {I' : ModelWithCorners ℝ E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]

variable {k : ℕ}

/- Remark 2.8-extra-1: in Lean, a smooth "function" on a manifold is a smooth map whose codomain
is `ℝ` or `EuclideanSpace ℝ (Fin k)` (formalizing the textbook `ℝ^k` case), while a smooth "map"
may have any manifold codomain. The core/canonical owner is the bundled smooth-map type
`ContMDiffMap`, and the function-valued cases below are its standard specializations. -/
recall ContMDiffMap

/- Real-valued smooth functions are the scalar specialization of `ContMDiffMap`. -/
#check (C^∞⟮I, M; ℝ⟯)

-- For the textbook vector-valued case, take `1 < k`; `EuclideanSpace ℝ (Fin k)` is Lean's
-- canonical model for `ℝ^k`.
#check (C^∞⟮I, M; 𝓘(ℝ, EuclideanSpace ℝ (Fin k)), EuclideanSpace ℝ (Fin k)⟯)

/- Smooth maps with arbitrary manifold codomain use the same owner with a general target model. -/
#check (C^∞⟮I, M; I', N⟯)
