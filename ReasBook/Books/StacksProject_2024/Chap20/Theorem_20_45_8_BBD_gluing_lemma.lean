import Mathlib
import stacks_project.Chap20.Lemma_20_45_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {𝓑 : Set (Opens X.carrier)}

namespace OpenFamilyDerivedGluing

-- Proof sketch: well-order a chain of unions of basis opens whose union is `X`. Use the finite
-- gluing step on successor stages and the transfinite gluing construction on limit stages, while
-- the negative-Ext uniqueness lemma identifies the stagewise solutions uniquely and makes the
-- transition isomorphisms compose correctly.
/-- Theorem 20.45.8 (BBD gluing lemma): if the basis opens in `𝓑` cover `X`, pairwise
intersections are unions of basis opens contained in the intersection, and the prescribed local
derived objects have vanishing negative self-Ext groups, then the gluing datum admits a global
solution. This global realization is unique up to a unique isomorphism compatible with the basis
identifications. -/
theorem exists_globalSolution_uniqueUpToUniqueIso
    (glue : OpenFamilyDerivedGluing X 𝓑)
    (hcover : BasisCoversSpace X 𝓑)
    (hinter : BasisIntersectionsGenerated X 𝓑)
    (hneg : OpenFamilyDerivedGluing.NegativeSelfExtVanishing glue) :
    ∃ S : OpenFamilyDerivedGluing.GlobalSolution glue,
      ∀ T : OpenFamilyDerivedGluing.GlobalSolution glue,
        ∃! e : S.obj ≅ T.obj,
          ∀ ⦃U : Opens X.carrier⦄ (hU : U ∈ 𝓑),
            (moduleRestrictionToOpenDerived X U).mapIso e ≪≫ T.iso hU =
              S.iso hU := sorry

end OpenFamilyDerivedGluing

end

end AlgebraicGeometry.RingedSpace
