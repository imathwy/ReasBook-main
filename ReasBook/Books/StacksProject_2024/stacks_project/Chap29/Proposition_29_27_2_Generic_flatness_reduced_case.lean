import Mathlib
import StacksProject_2024.stacks_project.Chap29.Proposition_29_27_1_Generic_flatness

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Semantic recall / owner check:
`lean_leansearch` surfaced the canonical scheme-morphism flatness owner
`AlgebraicGeometry.Flat`, and local precedent in Proposition 29.27.1 packages the whole
generic-flatness conclusion as `GenericFlatnessOn f ℱ U`.  The reduced-base case has the same
conclusion as the integral-base generic-flatness statement, with the base hypothesis changed from
`IsIntegral S` to `IsReduced S`. -/

section

variable {X S : Scheme.{u}}

/-- Proposition 29.27.2 (Generic flatness, reduced case): let `f : X ⟶ S` be a morphism of
schemes and let `ℱ` be a quasi-coherent `\mathcal O_X`-module. Assume `S` is reduced, `f` is of
finite type, and `ℱ` is of finite type. Then there exists an open dense subscheme `U ⊆ S` such
that `X_U → U` is flat and of finite presentation and `ℱ|_{X_U}` is flat over `U` and of finite
presentation over `\mathcal O_{X_U}`. -/
@[stacks 052B]
theorem exists_dense_open_genericFlatness_of_reduced
    (f : X ⟶ S) [IsReduced S] [Scheme.Hom.FiniteType f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] :
    ∃ U : S.Opens, Dense (U : Set S) ∧ GenericFlatnessOn f ℱ U := sorry

end

end AlgebraicGeometry.Scheme.Modules
