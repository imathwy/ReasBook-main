import SmoothManifoldsLee.Chap01.Sec01_05.Definition_1_5_extra_1
import SmoothManifoldsLee.Chap01.Sec01_04.Lemma_1_35

-- Declarations for this item will be appended below by the statement pipeline.
-- Domain sampling: the primary domain here is the `ChartedSpaceCore` owner API from `Lemma_1_35`.
-- The relevant canonical declarations are
-- `ChartedSpaceCore.eq_toTopologicalSpace_of_chartedSpace`,
-- `ChartedSpaceCore.toTopologicalSpace_t2Space`,
-- `ChartedSpaceCore.toTopologicalSpace_secondCountableTopology`, and
-- `ChartedSpaceCore.toChartedSpace_isManifold`.
-- For manifolds with boundary, the chapter's source-facing owner is `ℍ^n`
-- with model `leeBoundaryModelWithCorners n`; the positive-dimensional half-space model is only
-- the downstream specialization of that owner.

open scoped Manifold

universe u

section Exercise_1_43

variable {n : ℕ} {M : Type u}
variable (c : ChartedSpaceCore (ℍ^{n}) M)

section

variable [TopologicalSpace M] [ChartedSpace (ℍ^{n}) M]

/- Exercise 1.43 (1) is the boundary-model specialization of
`ChartedSpaceCore.eq_toTopologicalSpace_of_chartedSpace`. -/
#check c.eq_toTopologicalSpace_of_chartedSpace

end

/- Exercise 1.43 (2) is the boundary-model specialization of
`ChartedSpaceCore.toTopologicalSpace_t2Space`. -/
#check c.toTopologicalSpace_t2Space

/- Exercise 1.43 (3) is the boundary-model specialization of
`ChartedSpaceCore.toTopologicalSpace_secondCountableTopology`. -/
#check c.toTopologicalSpace_secondCountableTopology

/- Exercise 1.43 (4) is the boundary-model specialization of
`ChartedSpaceCore.toChartedSpace_isManifold` with model `leeBoundaryModelWithCorners n`. -/
#check c.toChartedSpace_isManifold (leeBoundaryModelWithCorners n)

end Exercise_1_43
