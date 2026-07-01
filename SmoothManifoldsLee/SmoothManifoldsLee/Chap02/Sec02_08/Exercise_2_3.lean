import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

-- Declarations for this item will be appended below by the statement pipeline.

universe uE uH uM

open Set ChartedSpace IsManifold
open scoped ContDiff Manifold

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

-- Proof sketch: use the canonical source-chart bridge
-- `contMDiffOn_iff_source_of_mem_maximalAtlas` on the domain `e.source`, then convert the
-- Euclidean `ContMDiffOn` conclusion to `ContDiffOn`.
/-- Exercise 2.3: if `f : M → ℝ^k` is smooth, then for every smooth chart `e` on `M`, the
chart-written expression `f ∘ (e.extend I).symm` is smooth on the chart image
`e.extend I '' e.source`. This is the manifold-with-corners form of the textbook statement that
`f ∘ φ⁻¹` is smooth on `φ(U)`. -/
theorem smooth_chart_representation_of_contMDiff
    {k : ℕ} {f : M → EuclideanSpace ℝ (Fin k)} {e : OpenPartialHomeomorph M H}
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ f)
    (he : e ∈ maximalAtlas I ∞ M) :
    ContDiffOn ℝ ∞ (f ∘ (e.extend I).symm) (e.extend I '' e.source) := by
  have hwritten :
      ContMDiffOn
        𝓘(ℝ, E)
        𝓘(ℝ, EuclideanSpace ℝ (Fin k))
        ∞
        (f ∘ (e.extend I).symm)
        (e.extend I '' e.source) :=
    (contMDiffOn_iff_source_of_mem_maximalAtlas he Subset.rfl).1 <| hf.contMDiffOn.mono Subset.rfl
  exact hwritten.contDiffOn
