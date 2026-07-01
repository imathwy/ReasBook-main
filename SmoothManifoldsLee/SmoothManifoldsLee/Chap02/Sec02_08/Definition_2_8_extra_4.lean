import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

-- Declarations for this item will be appended below by the statement pipeline.

open Set ChartedSpace IsManifold
open scoped Manifold ContDiff

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I (∞ : ℕ∞ω) M]
variable {k : ℕ} {f : M → EuclideanSpace ℝ (Fin k)} {x x' : M}

/- Definition 2.8-extra-4: for a map from a smooth manifold to `ℝ^k`, the coordinate
representation in the preferred smooth chart centered at `x` is mathlib's
`writtenInExtChartAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) x f`, which is the conjugated map
`f ∘ (extChartAt I x).symm` on the chart image. For an arbitrary smooth chart `e` in the maximal
atlas, the corresponding coordinate representation is `f ∘ (e.extend I).symm`. -/
#check (writtenInExtChartAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) x f)

/-
Smoothness at a point is equivalent to smoothness of the coordinate representation in any smooth
chart from the maximal atlas containing that point. This is exactly
`contMDiffWithinAt_iff_source_of_mem_maximalAtlas` specialized to the Euclidean target model and
the set `univ`; since the chart representative is now a map between normed spaces, the canonical
owner for its smoothness is `ContDiffWithinAt`.
-/
#check contMDiffWithinAt_iff_source_of_mem_maximalAtlas
#check contMDiffWithinAt_iff_contDiffWithinAt

/-- A smooth map into `ℝ^k` has a smooth coordinate representation in every smooth chart from the
maximal atlas whose source contains the point. -/
theorem smooth_coordinate_representation_of_contMDiffAt
    {e : OpenPartialHomeomorph M H}
    (hf : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (∞ : ℕ∞ω) f x')
    (he : e ∈ maximalAtlas I (∞ : ℕ∞ω) M)
    (hx : x' ∈ e.source) :
    ContDiffWithinAt ℝ ∞ (f ∘ (e.extend I).symm) (range I) (e.extend I x') := by
  have hf' : ContMDiffWithinAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (∞ : ℕ∞ω) f univ x' :=
    hf.contMDiffWithinAt
  have hcoord :
      ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (∞ : ℕ∞ω)
        (f ∘ (e.extend I).symm) (range I) (e.extend I x') := by
    simpa [preimage_univ, univ_inter] using
      (show
        ContMDiffWithinAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (∞ : ℕ∞ω) f univ x' ↔
          ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (∞ : ℕ∞ω)
            (f ∘ (e.extend I).symm) ((e.extend I).symm ⁻¹' (univ : Set M) ∩ range I)
            (e.extend I x')
        from contMDiffWithinAt_iff_source_of_mem_maximalAtlas he hx).1 hf'
  exact hcoord.contDiffWithinAt
