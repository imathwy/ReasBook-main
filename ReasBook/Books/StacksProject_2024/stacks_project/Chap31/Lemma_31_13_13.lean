import Mathlib
import StacksProject_2024.Chap29.Definition_29_50_1
import StacksProject_2024.Chap31.Definition_31_2_1
import StacksProject_2024.Chap31.Definition_31_4_1
import StacksProject_2024.Chap31.Definition_31_5_1
import StacksProject_2024.Chap31.Definition_31_13_12

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

-- Semantic recall: `lean_leansearch` confirmed the mathlib morphism owners `IsDominant` and
-- `Flat`; the local Chapter 29/31 source-facing owners for the pointwise hypotheses are
-- `genericPointsOfIrreducibleComponents`, `Scheme.weakAss`, `Scheme.associatedPoints`, and
-- `Scheme.embeddedPoints`, while divisor pullback-definedness is
-- `Scheme.IdealSheafData.pullbackDefined`.

/-- Lemma 31.13.13 (1): let `f : X ⟶ Y` be a morphism of schemes and let `D ⊆ Y` be an effective
Cartier divisor. If every weakly associated point of `X` maps outside the support `D.support`,
then the pullback of `D` by `f` is defined. -/
@[stacks 02OO]
theorem pullbackDefined_of_weakAss_outside_support
    {X Y : Scheme.{u}} (f : X ⟶ Y) (D : Y.IdealSheafData) [IsEffectiveCartierDivisor D]
    (hweak : ∀ x : X, x ∈ X.weakAss → f.base x ∉ D.support) :
    pullbackDefined D f := sorry

/-- Lemma 31.13.13 (2): let `f : X ⟶ Y` be a dominant morphism of integral schemes and let
`D ⊆ Y` be an effective Cartier divisor. Then the pullback of `D` by `f` is defined. -/
@[stacks 02OO]
theorem pullbackDefined_of_isIntegral_of_isDominant
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
    (D : Y.IdealSheafData) [IsEffectiveCartierDivisor D] :
    pullbackDefined D f := sorry

/-- Lemma 31.13.13 (3): let `f : X ⟶ Y` be a morphism of schemes and let `D ⊆ Y` be an effective
Cartier divisor. If `X` is reduced and every generic point of an irreducible component of `X`
maps outside the support `D.support`, then the pullback of `D` by `f` is defined. -/
@[stacks 02OO]
theorem pullbackDefined_of_genericPointsOfIrreducibleComponents_outside_support_of_isReduced
    {X Y : Scheme.{u}} [IsReduced X] (f : X ⟶ Y) (D : Y.IdealSheafData)
    [IsEffectiveCartierDivisor D]
    (hgeneric :
      ∀ ξ : X, ξ ∈ genericPointsOfIrreducibleComponents X → f.base ξ ∉ D.support) :
    pullbackDefined D f := sorry

/-- Lemma 31.13.13 (4): let `f : X ⟶ Y` be a morphism of schemes and let `D ⊆ Y` be an effective
Cartier divisor. If `X` is locally Noetherian and every associated point of `X` maps outside the
support `D.support`, then the pullback of `D` by `f` is defined. -/
@[stacks 02OO]
theorem pullbackDefined_of_associatedPoints_outside_support_of_isLocallyNoetherian
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ Y) (D : Y.IdealSheafData)
    [IsEffectiveCartierDivisor D]
    (hassoc : ∀ x : X, x ∈ X.associatedPoints → f.base x ∉ D.support) :
    pullbackDefined D f := sorry

/-- Lemma 31.13.13 (5): let `f : X ⟶ Y` be a morphism of schemes and let `D ⊆ Y` be an effective
Cartier divisor. If `X` is locally Noetherian, has no embedded points, and every generic point of
an irreducible component of `X` maps outside the support `D.support`, then the pullback of `D` by
`f` is defined. -/
@[stacks 02OO]
theorem pullbackDefined_of_embeddedPoints_eq_empty_of_genericPointsOfIrreducibleComponents_outside_support
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ Y) (D : Y.IdealSheafData)
    [IsEffectiveCartierDivisor D] (hembedded : X.embeddedPoints = (∅ : Set X))
    (hgeneric :
      ∀ ξ : X, ξ ∈ genericPointsOfIrreducibleComponents X → f.base ξ ∉ D.support) :
    pullbackDefined D f := sorry

/-- Lemma 31.13.13 (6): let `f : X ⟶ Y` be a flat morphism of schemes and let `D ⊆ Y` be an
effective Cartier divisor. Then the pullback of `D` by `f` is defined. -/
@[stacks 02OO]
theorem pullbackDefined_of_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (D : Y.IdealSheafData)
    [IsEffectiveCartierDivisor D] :
    pullbackDefined D f := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
