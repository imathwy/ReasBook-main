import Mathlib
import StacksProject_2024.Chap29.Definition_29_50_1
import StacksProject_2024.Chap31.Definition_31_2_1
import StacksProject_2024.Chap31.Definition_31_4_1
import StacksProject_2024.Chap31.Definition_31_5_1
import StacksProject_2024.Chap31.Definition_31_23_4

open AlgebraicGeometry
open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry nonZeroDivisors

universe u

namespace AlgebraicGeometry

-- Semantic recall / local owner check:
-- - `lean_leansearch` surfaced the canonical morphism-property owners `IsDominant` and `Flat`.
-- - The nearby analogue `Lemma_31_13_13` fixes the source-facing pointwise hypotheses as
--   `Scheme.weakAss`, `Scheme.associatedPoints`, `Scheme.embeddedPoints`, and
--   `genericPointsOfIrreducibleComponents`.
-- - For meromorphic pullback-definedness, the existing owner is
--   `LocallyRingedSpace.Hom.pullbacksMeromorphicFunctionsDefined`, with regular sections on an
--   open subset recorded by `nonZeroDivisors` in its ring of regular functions.

/-- Lemma 31.23.5 (1): let `f : X ⟶ Y` be a morphism of schemes. If every weakly associated point
of `X` maps to a generic point of an irreducible component of `Y`, then pullbacks of meromorphic
functions are defined for `f`. Here regular meromorphic functions on an open subset are formalized
by the nonzerodivisors in its ring of sections. -/
@[stacks 02OU]
theorem pullbacksMeromorphicFunctionsDefined_of_weakAss_toGenericPointOfIrreducibleComponent
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hweak : ∀ x : X, x ∈ X.weakAss → f.base x ∈ genericPointsOfIrreducibleComponents Y) :
    LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined f.1 := sorry

/-- Lemma 31.23.5 (2): if `f : X ⟶ Y` is a dominant morphism of integral schemes, then pullbacks
of meromorphic functions are defined for `f`. The pullback-definedness predicate is the
nonzerodivisor-based owner from Definition `31.23.4`. -/
@[stacks 02OU]
theorem pullbacksMeromorphicFunctionsDefined_of_isIntegral_of_isDominant
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] :
    LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined f.1 := sorry

/-- Lemma 31.23.5 (3): let `f : X ⟶ Y` be a morphism of schemes. If `X` is integral and the
generic point of `X` maps to a generic point of an irreducible component of `Y`, then pullbacks
of meromorphic functions are defined for `f`. -/
@[stacks 02OU]
theorem pullbacksMeromorphicFunctionsDefined_of_isIntegral_of_genericPoint_toGenericPointOfIrreducibleComponent
    {X Y : Scheme.{u}} [IsIntegral X] (f : X ⟶ Y)
    (hgeneric : f.base (genericPoint X) ∈ genericPointsOfIrreducibleComponents Y) :
    LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined f.1 := sorry

/-- Lemma 31.23.5 (4): let `f : X ⟶ Y` be a morphism of schemes. If `X` is reduced and every
generic point of an irreducible component of `X` maps to a generic point of an irreducible
component of `Y`, then pullbacks of meromorphic functions are defined for `f`. -/
@[stacks 02OU]
theorem pullbacksMeromorphicFunctionsDefined_of_isReduced_of_genericPointsOfIrreducibleComponents_toGenericPointsOfIrreducibleComponents
    {X Y : Scheme.{u}} [IsReduced X] (f : X ⟶ Y)
    (hgeneric :
      ∀ ξ : X,
        ξ ∈ genericPointsOfIrreducibleComponents X →
          f.base ξ ∈ genericPointsOfIrreducibleComponents Y) :
    LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined f.1 := sorry

/-- Lemma 31.23.5 (5): let `f : X ⟶ Y` be a morphism of schemes. If `X` is locally Noetherian and
every associated point of `X` maps to a generic point of an irreducible component of `Y`, then
pullbacks of meromorphic functions are defined for `f`. -/
@[stacks 02OU]
theorem pullbacksMeromorphicFunctionsDefined_of_isLocallyNoetherian_of_associatedPoints_toGenericPointsOfIrreducibleComponents
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ Y)
    (hassoc :
      ∀ x : X, x ∈ X.associatedPoints → f.base x ∈ genericPointsOfIrreducibleComponents Y) :
    LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined f.1 := sorry

/-- Lemma 31.23.5 (6): let `f : X ⟶ Y` be a morphism of schemes. If `X` is locally Noetherian,
has no embedded points, and every generic point of an irreducible component of `X` maps to a
generic point of an irreducible component of `Y`, then pullbacks of meromorphic functions are
defined for `f`. The no-embedded-points hypothesis is formalized as `X.embeddedPoints = ∅`. -/
@[stacks 02OU]
theorem pullbacksMeromorphicFunctionsDefined_of_isLocallyNoetherian_of_embeddedPoints_eq_empty_of_genericPointsOfIrreducibleComponents_toGenericPointsOfIrreducibleComponents
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ Y)
    (hembedded : X.embeddedPoints = (∅ : Set X))
    (hgeneric :
      ∀ ξ : X,
        ξ ∈ genericPointsOfIrreducibleComponents X →
          f.base ξ ∈ genericPointsOfIrreducibleComponents Y) :
    LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined f.1 := sorry

/-- Lemma 31.23.5 (7): if `f : X ⟶ Y` is a flat morphism of schemes, then pullbacks of
meromorphic functions are defined for `f`, with regular sections formalized by nonzerodivisors on
open subsets. -/
@[stacks 02OU]
theorem pullbacksMeromorphicFunctionsDefined_of_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined f.1 := sorry

end AlgebraicGeometry
