import Mathlib.Geometry.Manifold.Complex

open scoped Manifold
open TopologicalSpace

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the owner abstraction was checked directly against mathlib's open-subset manifold API:
-- `TopologicalSpace.Opens.chartAt_eq` and `TopologicalSpace.Opens.instChartedSpace` in
-- `HasGroupoid.lean`, together with the induced `IsManifold` instance in
-- `IsManifold/Basic.lean`. The present item is `source-facing`: its main content is the explicit
-- restriction formula for charts on an open subset, while the manifold structure is a companion
-- consequence of that canonical owner API.

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]
variable (U : Opens X)

/- Definition VI.4-extra-6: if `X` is a complex manifold and `U` is an open subset of `X`, then
the canonical chart on `U` at `x : U` is exactly the restriction of the ambient chart at
`x.1 : X`. This is the source-facing chart-restriction content of the induced complex structure on
`U : Opens X`. -/
#check TopologicalSpace.Opens.chartAt_eq

/- Every open subset of a complex manifold is again a complex manifold. -/
#check (inferInstance : IsManifold I 1 U)

end
