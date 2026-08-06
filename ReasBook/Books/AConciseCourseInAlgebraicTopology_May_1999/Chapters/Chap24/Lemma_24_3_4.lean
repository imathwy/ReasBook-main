import Mathlib.Algebra.Ring.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.VectorBundle.Constructions
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_3_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.ProjectiveBundleTopologicalKTheory

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ProjectiveBundleNotation

-- The reusable projective-bundle `K`-theory owner lives in
-- `ProjectiveBundleTopologicalKTheory`; this lemma adds the Chapter 24 injectivity statements that
-- also need the Chapter 18 singular-cohomology pullback surface.

section

variable {X : Type} [TopologicalSpace X]
variable {n : ℕ} {E : ComplexPlaneBundle n X}

/-- The ordinary-cohomology pullback map in degree `q` induced by `projectiveBundleProjMap`. -/
noncomputable abbrev projectiveBundleCohomologyPullbackMap
    (E : ComplexPlaneBundle n X)
    (q : ℕ) :
    singularCohomologyClasses ℤ (TopCat.of X) q →
      singularCohomologyClasses ℤ (TopCat.of (P(E))) q :=
  singularCohomologyPullback ℤ (projectiveBundleProjMap E) q

variable [Fact (0 < n)]

/-- Lemma 24.3.4 (1): for a projective bundle `P(E) → X`, pullback along
`projectiveBundleProjMap` is injective on integral singular cohomology in every degree when
`0 < n`. -/
theorem projectiveBundleCohomologyPullback_injective
    (q : ℕ) :
    Function.Injective (projectiveBundleCohomologyPullbackMap E q) :=
  sorry

/-- Lemma 24.3.4 (2): for a projective bundle `P(E) → X`, the actual pullback map on topological
`K`-theory induced by `projectiveBundleProjMap` is injective when `0 < n`. -/
theorem projectiveBundleKTheoryPullback_injective
    [CompactSpace X] [CompactSpace (P(E))]
    [topologicalKTheory : ProjectiveBundleTopologicalKTheory E] :
    Function.Injective topologicalKTheory.pullback := sorry

/-- For the canonical `K(X)`-algebra structure on `K(P(E))` induced by
`ProjectiveBundleTopologicalKTheory E`, the algebra map is injective. -/
theorem projectiveBundleKTheory_algebraMap_injective
    [CompactSpace X] [CompactSpace (P(E))]
    [topologicalKTheory : ProjectiveBundleTopologicalKTheory E] :
    Function.Injective (algebraMap (complexKTheory X) (complexKTheory (P(E)))) := by
  simpa [ProjectiveBundleTopologicalKTheory.algebraMap_eq_pullback] using
    (projectiveBundleKTheoryPullback_injective : Function.Injective topologicalKTheory.pullback)

end
