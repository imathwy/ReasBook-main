import Mathlib
import StacksProject_2024.Chap28.Definition_28_7_1
import StacksProject_2024.Chap29.Lemma_29_51_9
import StacksProject_2024.Chap31.Lemma_31_17_8

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall note: `lean_leansearch` is not exposed in this environment. The owner/API choice
-- was verified against the local Chapter 31 norm owner `Norm`, the Chapter 29 degree owner
-- `Scheme.Hom.functionFieldDegree`, and the Chapter 28 scheme-normality owner `Scheme.isNormal`.

/-- Lemma 31.17.7: let `π : X ⟶ Y` be a finite surjective morphism with `X` and `Y` integral and
`Y` normal. Then there exists a norm of degree `[R(X) : R(Y)]` for `π`. Here the degree is the
existing function-field degree `π.functionFieldDegree`, and surjectivity is recorded on
the underlying map of points. -/
theorem exists_norm_of_isFinite_of_surjective_of_isNormal
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsFinite π] [Algebra Y.functionField X.functionField]
    [FiniteDimensional Y.functionField X.functionField]
    (hπsurj : Function.Surjective π.base) (hY : Y.isNormal) :
    ∃ N : Norm π, IsNorm π π.functionFieldDegree N := sorry

end AlgebraicGeometry.Scheme
