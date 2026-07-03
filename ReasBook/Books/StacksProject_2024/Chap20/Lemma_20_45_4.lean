import Mathlib
import stacks_project.Chap20.Situation_20_45_3

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

-- Proof sketch: apply Lemma `20.45.2` to the degree-zero derived-Hom presheaf of two global
-- solutions. The basiswise negative Ext vanishing forces that presheaf to be a sheaf, so the
-- local comparison isomorphisms glue to a unique global isomorphism.
/-- Lemma 20.45.4 (1): if the basis opens in `𝓑` cover `X`, pairwise intersections are unions of
basis opens contained in the intersection, and the local objects of the gluing problem have
vanishing negative self-Ext groups, then any two global solutions are uniquely isomorphic in a way
compatible with the gluing data. -/
theorem openFamilyDerivedGluing_solution_uniqueIso
    (glue : OpenFamilyDerivedGluing X 𝓑)
    (hcover : BasisCoversSpace X 𝓑)
    (hinter : BasisIntersectionsGenerated X 𝓑)
    (hneg : OpenFamilyDerivedGluing.NegativeSelfExtVanishing glue) :
    ∀ S T : OpenFamilyDerivedGluing.GlobalSolution glue, ∃! e : S.obj ≅ T.obj,
      ∀ ⦃U : Opens X.carrier⦄ (hU : U ∈ 𝓑),
        (moduleRestrictionToOpenDerived X U).mapIso e ≪≫ T.iso hU =
          S.iso hU := sorry

-- Proof sketch: apply the same derived-Hom sheaf argument as in part `(1)` to one global
-- solution against itself. The local negative self-Ext vanishing hypothesis implies that the
-- negative derived endomorphism groups vanish on every basis open, hence globally as well.
/-- Lemma 20.45.4 (2): under the same hypotheses, every global solution has vanishing negative
self-Ext groups. -/
theorem openFamilyDerivedGluing_negative_selfExt_isZero
    (glue : OpenFamilyDerivedGluing X 𝓑)
    (hcover : BasisCoversSpace X 𝓑)
    (hinter : BasisIntersectionsGenerated X 𝓑)
    (hneg : OpenFamilyDerivedGluing.NegativeSelfExtVanishing glue) :
    ∀ S : OpenFamilyDerivedGluing.GlobalSolution glue, ∀ i : ℤ, i < 0 →
      Subsingleton (S.obj ⟶ (shiftFunctor (DerivedCategory (RingedSpace.Modules X)) i).obj S.obj) := sorry

end

end AlgebraicGeometry.RingedSpace
