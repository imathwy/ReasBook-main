import Mathlib.Topology.Compactness.Compact
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Theorem_14_5_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Lemma_20_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Lemma_20_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Lemma_20_4_3

-- Semantic recall via `lean_leansearch`: no single mathlib theorem surfaced for the whole
-- Chapter 20 reduction. The proof route is organized by the chapter-local owners
-- `exists_compactSubspace_of_rSingularHomologyClass`,
-- `isZero_rSingularHomology_openSubsetEuclideanSpace_of_lt`,
-- `isZero_rSingularHomology_openSubsetEuclideanSpace_of_pos_of_le`,
-- `eq_zero_of_forall_relativeToLocalTopHomologyMap_eq_zero_openSubsetEuclideanSpace`, together
-- with mathlib's compactness extraction lemma `IsCompact.elim_finite_subcover` and the
-- Mayer-Vietoris exactness package `pairHomologyMayerVietorisExact₁/₂/₃`.

/- Proof step 20.4.4. The vanishing theorem is proved by first reducing an arbitrary homology
class to one supported on a compact subspace, then extracting a finite subcover of that compact
support by coordinate balls, and finally running Mayer-Vietoris induction over that finite cover.
In the current formalization, the compact-support reduction is `Lemma 20.4.1`, the coordinate-ball
vanishing and top-degree local detection inputs are `Lemma 20.4.2` and `Lemma 20.4.3`, finite
subcover extraction is `IsCompact.elim_finite_subcover`, and the induction step is organized by
the Chapter 14 Mayer-Vietoris exactness package. -/
#check exists_compactSubspace_of_rSingularHomologyClass
#check IsCompact.elim_finite_subcover
#check isZero_rSingularHomology_openSubsetEuclideanSpace_of_lt
#check isZero_rSingularHomology_openSubsetEuclideanSpace_of_pos_of_le
#check eq_zero_of_forall_relativeToLocalTopHomologyMap_eq_zero_openSubsetEuclideanSpace
#check pairHomologyMayerVietorisExact₁
#check pairHomologyMayerVietorisExact₂
#check pairHomologyMayerVietorisExact₃
