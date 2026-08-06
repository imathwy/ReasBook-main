import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Proposition_21_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Proposition_21_4_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Lemma_20_4_1

open AlgebraicTopology
open scoped Manifold

noncomputable section

-- Chapter 21 already fixes the canonical owners `rSingularHomology`,
-- `ROrientedManifoldWithBoundary`, `manifoldBoundary`, and `manifoldBoundaryInclusion`. This file
-- keeps only the source-facing middle-dimensional boundary-kernel surface built from those owners.

/-- The middle-dimensional boundary homology `H_m(∂M; K)` of a `(2 * m + 1)`-dimensional manifold
with boundary. -/
abbrev middleBoundaryHomology (K : Type) [Field K] (m : ℕ) (M : Type)
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (2 * m + 1)) M] : ModuleCat K :=
  rSingularHomology K m (TopCat.of (manifoldBoundary (2 * m + 1) M))

/-- The middle-dimensional homology `H_m(M; K)` of a `(2 * m + 1)`-dimensional manifold with
boundary. -/
abbrev middleManifoldHomology (K : Type) [Field K] (m : ℕ) (M : Type)
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (2 * m + 1)) M] : ModuleCat K :=
  rSingularHomology K m (TopCat.of M)

/-- The morphism on middle-dimensional singular homology induced by the inclusion `∂M ↪ M`. -/
abbrev middleBoundaryHomologyMap (K : Type) [Field K] (m : ℕ) (M : Type)
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (2 * m + 1)) M] :
    middleBoundaryHomology K m M ⟶ middleManifoldHomology K m M :=
  rSingularHomologyMap K m (manifoldBoundaryInclusion (2 * m + 1) M)

/-- The kernel of the middle-dimensional boundary map `H_m(∂M; K) ⟶ H_m(M; K)`. -/
abbrev middleBoundaryHomologyKernel (K : Type) [Field K] (m : ℕ) (M : Type)
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (2 * m + 1)) M] :
    Submodule K (middleBoundaryHomology K m M) :=
  LinearMap.ker (middleBoundaryHomologyMap K m M).hom

/-- If `H_m(∂M; K)` carries an alternating nondegenerate bilinear form whose orthogonal
complement of `ker(H_m(∂M; K) ⟶ H_m(M; K))` is exactly that kernel, then the kernel has half the
dimension of `H_m(∂M; K)`. This is the linear-algebra reduction used in Problem 21.6.3 once the
geometric manifold hypotheses have produced the pairing. -/
theorem middleBoundaryHomologyKernel_finrank_eq_half_of_pairing (K : Type) [Field K] (m : ℕ)
    (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (2 * m + 1)) M]
    [FiniteDimensional K (middleBoundaryHomology K m M)]
    (pairing : LinearMap.BilinForm K (middleBoundaryHomology K m M))
    (hpairingAlt : pairing.IsAlt) (hpairingNondegenerate : pairing.Nondegenerate)
    (hkernel :
      middleBoundaryHomologyKernel K m M =
        pairing.orthogonal (middleBoundaryHomologyKernel K m M)) :
    2 * Module.finrank K (middleBoundaryHomologyKernel K m M) =
      Module.finrank K (middleBoundaryHomology K m M) := sorry

/-- Problem 21.6.3. For a compact orientable odd-dimensional manifold with boundary, the
middle-dimensional kernel of `H_m(∂M; K) ⟶ H_m(M; K)` has half the dimension of `H_m(∂M; K)`
over the field `K`. The compact Hausdorff second-countable manifold hypotheses from the chapter
setup are kept explicit through `ChartedSpace (EuclideanHalfSpace (2 * m + 1)) M` and
`IsManifold (𝓡∂ (2 * m + 1)) (2 * m + 1) M`, while orientability with boundary is recorded by the
source-facing witness `Nonempty (ROrientedManifoldWithBoundary ℤ (2 * m + 1) M)`. The induced
alternating pairing hypotheses remain a helper layer for the proof rather than a public
assumption of the source-facing statement. -/
theorem middleBoundaryHomologyKernel_finrank_eq_half (K : Type) [Field K] (m : ℕ) (M : Type)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace (2 * m + 1)) M]
    [IsManifold (𝓡∂ (2 * m + 1)) (2 * m + 1) M]
    (h_orientable : Nonempty (ROrientedManifoldWithBoundary ℤ (2 * m + 1) M)) :
    2 * Module.finrank K (middleBoundaryHomologyKernel K m M) =
      Module.finrank K (middleBoundaryHomology K m M) := sorry
