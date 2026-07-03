import Mathlib
import StacksProject_2024.Chap20.Situation_20_45_3

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

/-- Restrict an isomorphism over `U ⊓ V` to a smaller open `W ≤ U ⊓ V`, identifying the two-step
restrictions with the direct restrictions from `U` and `V` to `W`. -/
noncomputable def overlapIsoRestrictFrom
    {U V W : Opens X.carrier}
    {A : moduleDerivedOnOpen X U} {B : moduleDerivedOnOpen X V}
    (e : (derivedRestrictionBetweenOpens X inf_le_left).obj A ≅
      (derivedRestrictionBetweenOpens X inf_le_right).obj B)
    (hW : W ≤ U ⊓ V) :
    (derivedRestrictionBetweenOpens X (hW.trans inf_le_left)).obj A ≅
      (derivedRestrictionBetweenOpens X (hW.trans inf_le_right)).obj B :=
  ((derivedRestrictionBetweenOpensCompIso (X := X) hW inf_le_left).app A).symm ≪≫
    (Functor.mapIso (derivedRestrictionBetweenOpens X hW) e) ≪≫
      (derivedRestrictionBetweenOpensCompIso (X := X) hW inf_le_right).app B

-- Proof sketch: apply Lemma `20.45.4` to the restricted system on `U ⊓ V`, whose basis consists
-- of those `U' ∈ 𝓑` contained in `U ⊓ V`. The two restricted objects `K_U|_{U ⊓ V}` and
-- `K_V|_{U ⊓ V}` are both solutions, so the lemma gives a unique compatible isomorphism.
/-- The overlap restrictions of two basis members are uniquely isomorphic once the hypotheses of
Lemma `20.45.4` are imposed on the gluing system. -/
theorem overlapIso_existsUnique
    (glue : OpenFamilyDerivedGluing X 𝓑)
    (hcover : BasisCoversSpace X 𝓑)
    (hinter : BasisIntersectionsGenerated X 𝓑)
    (hneg : OpenFamilyDerivedGluing.NegativeSelfExtVanishing glue)
    {U V : Opens X.carrier} (hU : U ∈ 𝓑) (hV : V ∈ 𝓑) :
    ∃! e :
        (derivedRestrictionBetweenOpens X inf_le_left).obj (glue.obj hU) ≅
          (derivedRestrictionBetweenOpens X inf_le_right).obj (glue.obj hV),
      ∀ ⦃U' : Opens X.carrier⦄ (hU' : U' ∈ 𝓑) (hU'UV : U' ≤ U ⊓ V),
        overlapIsoRestrictFrom e hU'UV ≪≫
            glue.ρ hV hU' (hU'UV.trans inf_le_right) =
          glue.ρ hU hU' (hU'UV.trans inf_le_left) := sorry

/-- The canonical comparison isomorphism between the restrictions of `K_U` and `K_V` to
`U ⊓ V`, characterized by compatibility with the maps to every basis open inside `U ⊓ V`. -/
noncomputable def overlapIso
    (glue : OpenFamilyDerivedGluing X 𝓑)
    (hcover : BasisCoversSpace X 𝓑)
    (hinter : BasisIntersectionsGenerated X 𝓑)
    (hneg : OpenFamilyDerivedGluing.NegativeSelfExtVanishing glue)
    {U V : Opens X.carrier} (hU : U ∈ 𝓑) (hV : V ∈ 𝓑) :
    (derivedRestrictionBetweenOpens X inf_le_left).obj (glue.obj hU) ≅
      (derivedRestrictionBetweenOpens X inf_le_right).obj (glue.obj hV) :=
  Classical.choose (overlapIso_existsUnique glue hcover hinter hneg hU hV)

-- Proof sketch: unpack the unique-existence statement defining `overlapIso`; the chosen witness
-- inherits exactly the compatibility condition recorded there.
/-- The canonical overlap isomorphism restricts to the prescribed maps `ρ^U_{U'}` and
`ρ^V_{U'}` on every basis open `U' ⊆ U ⊓ V`. -/
theorem overlapIso_spec
    (glue : OpenFamilyDerivedGluing X 𝓑)
    (hcover : BasisCoversSpace X 𝓑)
    (hinter : BasisIntersectionsGenerated X 𝓑)
    (hneg : OpenFamilyDerivedGluing.NegativeSelfExtVanishing glue)
    {U V : Opens X.carrier} (hU : U ∈ 𝓑) (hV : V ∈ 𝓑) :
    ∀ ⦃U' : Opens X.carrier⦄ (hU' : U' ∈ 𝓑) (hU'UV : U' ≤ U ⊓ V),
      overlapIsoRestrictFrom (glue.overlapIso hcover hinter hneg hU hV) hU'UV ≪≫
          glue.ρ hV hU' (hU'UV.trans inf_le_right) =
        glue.ρ hU hU' (hU'UV.trans inf_le_left) := sorry

-- Proof sketch: restrict the three canonical overlap isomorphisms to `U ⊓ V ⊓ W`. Both the direct
-- map `ρ_{U,W}` and the composite `ρ_{U,V}` followed by `ρ_{V,W}` satisfy the same compatibility
-- with all basis opens contained in the triple intersection, so uniqueness from
-- `overlapIso_existsUnique` identifies them.
/-- Remark 20.45.5: the canonical overlap isomorphisms for a basis gluing datum satisfy the usual
cocycle condition on triple intersections, so the family `(K_U, ρ_{U,V})` behaves as a descent
datum for the open covering `X = ⋃_{U ∈ 𝓑} U`. -/
theorem overlapIso_cocycle
    (glue : OpenFamilyDerivedGluing X 𝓑)
    (hcover : BasisCoversSpace X 𝓑)
    (hinter : BasisIntersectionsGenerated X 𝓑)
    (hneg : OpenFamilyDerivedGluing.NegativeSelfExtVanishing glue)
    {U V W : Opens X.carrier}
    (hU : U ∈ 𝓑) (hV : V ∈ 𝓑) (hW : W ∈ 𝓑) :
    overlapIsoRestrictFrom (glue.overlapIso hcover hinter hneg hU hW)
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right) =
      overlapIsoRestrictFrom (glue.overlapIso hcover hinter hneg hU hV) inf_le_left ≪≫
        overlapIsoRestrictFrom (glue.overlapIso hcover hinter hneg hV hW)
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right) := sorry

end OpenFamilyDerivedGluing

end

end AlgebraicGeometry.RingedSpace
