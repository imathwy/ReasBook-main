import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_13_12
import StacksProject_2024.stacks_project.Chap31.Definition_31_23_4
import StacksProject_2024.stacks_project.Chap31.Definition_31_34_1

open AlgebraicGeometry
open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry nonZeroDivisors

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced only the ambient pullback and locally-ringed-space
-- morphism owners, while local Chapter 31 inspection fixed the source-facing owners actually used
-- here: `Scheme.IdealSheafData.pullbackDefined` for divisor pullback, the nonzerodivisor
-- denominator system from `Definition_31_23_1`/`Lemma_31_24_2` for meromorphic pullback, and the
-- blowup owner `IsBlowup`.

/-- Lemma 31.32.11 (1): if `b : X' ⟶ X` is a blowup of `X` in a closed subscheme, then the
pullback of any effective Cartier divisor on `X` is defined along `b` in the sense of
Definition `31.13.12`. -/
@[stacks 0809]
theorem pullbackDefined_of_isBlowup
    {X X' : Scheme.{u}} {I : X.IdealSheafData}
    (b : X' ⟶ X) [IsBlowup b I]
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D] :
    Scheme.IdealSheafData.pullbackDefined D b := sorry

/-- Lemma 31.32.11 (2): if `b : X' ⟶ X` is a blowup of `X` in a closed subscheme, then pullbacks
of meromorphic functions are defined for `b` in the sense of Definition `31.23.4`, with regular
sections formalized by the nonzerodivisor denominator systems on open subsets. -/
@[stacks 0809]
theorem pullbacksMeromorphicFunctionsDefined_of_isBlowup
    {X X' : Scheme.{u}} {I : X.IdealSheafData}
    (b : X' ⟶ X) [IsBlowup b I] :
    LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined b.1 := sorry

end AlgebraicGeometry
