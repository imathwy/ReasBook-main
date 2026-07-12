import Mathlib
import StacksProject_2024.Chap06.Definition_6_30_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite TopologicalSpace TopCat TopCat.Presheaf Functor.Final

noncomputable section

universe u v

variable {X : TopCat.{v}}
variable {C : Type u} [Category.{v} C]
variable {B : Set (Opens X)}

/-- The full subcategory of basis opens containing the point `x`. -/
abbrev BasisOpenNhds (B : Set (Opens X)) (x : X) :=
  ObjectProperty.FullSubcategory fun U : BasisOpen B ↦ x ∈ U.1

/-- The inclusion of basis neighborhoods of `x` into the category of basis opens. -/
abbrev basisOpenNhdsInclusion (B : Set (Opens X)) (x : X) :
    BasisOpenNhds B x ⥤ BasisOpen B :=
  ObjectProperty.ι fun U : BasisOpen B ↦ x ∈ U.1

/-- The inclusion of basis neighborhoods of `x` into the category of all open neighborhoods of
`x`. -/
abbrev basisOpenNhdsToOpenNhds (B : Set (Opens X)) (x : X) : BasisOpenNhds B x ⥤ OpenNhds x where
  obj U := ⟨(basisOpenInclusion B).obj ((basisOpenNhdsInclusion B x).obj U), U.2⟩
  map {U V} i :=
    show ((basisOpenInclusion B).obj ((basisOpenNhdsInclusion B x).obj U)) ⟶
        ((basisOpenInclusion B).obj ((basisOpenNhdsInclusion B x).obj V)) from
      (basisOpenInclusion B).map ((basisOpenNhdsInclusion B x).map i)

/-- Basis neighborhoods containing `x` are final among all neighborhoods of `x` when `B` is a
topological basis. -/
instance basisOpenNhdsToOpenNhds_final (hB : Opens.IsBasis B) (x : X) :
    Functor.Final (basisOpenNhdsToOpenNhds B x).op := sorry

namespace BasisSiteSheaf

variable {hB : Opens.IsBasis B}

/-- The underlying presheaf of a sheaf on the basis `B`. -/
abbrev presheaf (F : BasisSiteSheaf C B hB) : (BasisOpen B)ᵒᵖ ⥤ C :=
  F.1

variable [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion B).op) C]

private noncomputable abbrev basisSiteSheafComparisonEquiv (hB : Opens.IsBasis B) :
    BasisSiteSheaf C B hB ≌ TopCat.Sheaf C X :=
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hB
  (basisOpenInclusion B).sheafInducedTopologyEquivOfIsCoverDense
    (Opens.grothendieckTopology X) C

/-- The sheaf on `X` obtained by extending a sheaf on the basis `B` along the dense inclusion of
basis opens into all opens. -/
abbrev extend (F : BasisSiteSheaf C B hB) : TopCat.Sheaf C X := by
  exact (basisSiteSheafComparisonEquiv (C := C) hB).functor.obj F

/-- The diagram of sections of a basis sheaf over basis opens containing `x`. -/
abbrev stalkDiagram (F : BasisSiteSheaf C B hB) (x : X) :
    (BasisOpenNhds B x)ᵒᵖ ⥤ C :=
  (basisOpenNhdsInclusion B x).op ⋙ F.presheaf

/-- The diagram obtained by evaluating the extended sheaf `F.extend` on basis neighborhoods of
`x`. -/
abbrev extendStalkDiagram (F : BasisSiteSheaf C B hB) (x : X) :
    (BasisOpenNhds B x)ᵒᵖ ⥤ C :=
  (basisOpenNhdsToOpenNhds B x).op ⋙ (OpenNhds.inclusion x).op ⋙ F.extend.presheaf

/-- The component over a basis open of the canonical restriction comparison from `F` to the
restriction of `F.extend` back to the basis. -/
abbrev restrictExtendComponentHom (F : BasisSiteSheaf C B hB)
    (U : (BasisOpen B)ᵒᵖ) :
    F.presheaf.obj U ⟶ ((basisOpenInclusion B).op ⋙ F.extend.presheaf).obj U := by
  simpa [presheaf, extend] using
    ((basisSiteSheafComparisonEquiv (C := C) hB).unitIso.app F).hom.1.app U

/-- The component over a basis open of the inverse restriction comparison from `F.extend` back to
`F`. -/
abbrev restrictExtendComponentInv (F : BasisSiteSheaf C B hB)
    (U : (BasisOpen B)ᵒᵖ) :
    ((basisOpenInclusion B).op ⋙ F.extend.presheaf).obj U ⟶ F.presheaf.obj U := by
  simpa [presheaf, extend] using
    ((basisSiteSheafComparisonEquiv (C := C) hB).unitIso.app F).inv.1.app U

-- Proof sketch: this is the componentwise naturality of the unit transformation of the
-- dense-subsite comparison equivalence, rewritten using the explicit description of `F.extend` on
-- basis opens.
/-- The restriction comparison from `F` to `F.extend` is natural in the basis open. -/
theorem restrictExtendHom_naturality (F : BasisSiteSheaf C B hB)
    {U V : (BasisOpen B)ᵒᵖ}
    (i : U ⟶ V) :
    F.presheaf.map i ≫ F.restrictExtendComponentHom V =
      F.restrictExtendComponentHom U ≫
        ((basisOpenInclusion B).op ⋙ F.extend.presheaf).map i :=
  sorry

-- Proof sketch: this is the componentwise naturality of the inverse of the unit transformation of
-- the dense-subsite comparison equivalence.
/-- The inverse restriction comparison from `F.extend` back to `F` is natural in the basis open. -/
theorem restrictExtendInv_naturality (F : BasisSiteSheaf C B hB)
    {U V : (BasisOpen B)ᵒᵖ}
    (i : U ⟶ V) :
    ((basisOpenInclusion B).op ⋙ F.extend.presheaf).map i ≫
        F.restrictExtendComponentInv V =
      F.restrictExtendComponentInv U ≫ F.presheaf.map i := sorry

-- Proof sketch: these are the componentwise inverse identities of the unit isomorphism of the
-- dense-subsite comparison equivalence.
/-- On each basis open, the forward and inverse restriction comparison maps compose to the
identity on `F`. -/
theorem restrictExtend_component_hom_inv_id (F : BasisSiteSheaf C B hB)
    (U : (BasisOpen B)ᵒᵖ) :
    F.restrictExtendComponentHom U ≫ F.restrictExtendComponentInv U =
      𝟙 (F.presheaf.obj U) := sorry

-- Proof sketch: these are the componentwise inverse identities of the unit isomorphism of the
-- dense-subsite comparison equivalence.
/-- On each basis open, the inverse and forward restriction comparison maps compose to the identity
on the restriction of `F.extend`. -/
theorem restrictExtend_component_inv_hom_id (F : BasisSiteSheaf C B hB)
    (U : (BasisOpen B)ᵒᵖ) :
    F.restrictExtendComponentInv U ≫ F.restrictExtendComponentHom U =
      𝟙 (((basisOpenInclusion B).op ⋙ F.extend.presheaf).obj U) := sorry

/-- The canonical restriction comparison from a basis sheaf to the restriction of its extension. -/
abbrev restrictExtendHom (F : BasisSiteSheaf C B hB) :
    F.presheaf ⟶ (basisOpenInclusion B).op ⋙ F.extend.presheaf where
  app U := F.restrictExtendComponentHom U
  naturality := fun {_ _} i ↦ F.restrictExtendHom_naturality i

/-- The inverse restriction comparison from the restriction of `F.extend` back to the original
basis sheaf. -/
abbrev restrictExtendInv (F : BasisSiteSheaf C B hB) :
    (basisOpenInclusion B).op ⋙ F.extend.presheaf ⟶ F.presheaf where
  app U := F.restrictExtendComponentInv U
  naturality := fun {_ _} i ↦ F.restrictExtendInv_naturality i

/-- The original basis sheaf `F` is canonically isomorphic to the restriction of its extension
`F.extend` back to the basis. -/
abbrev restrictExtendIso (F : BasisSiteSheaf C B hB) :
    F.presheaf ≅ (basisOpenInclusion B).op ⋙ F.extend.presheaf where
  hom := F.restrictExtendHom
  inv := F.restrictExtendInv
  hom_inv_id := by
    ext U
    simpa using F.restrictExtend_component_hom_inv_id U
  inv_hom_id := by
    ext U
    simpa using F.restrictExtend_component_inv_hom_id U

/-- The basis stalk diagram of `F` is canonically isomorphic to the basis-neighborhood diagram
obtained from `F.extend`. -/
abbrev stalkDiagramIso (F : BasisSiteSheaf C B hB) (x : X) :
    F.stalkDiagram x ≅ F.extendStalkDiagram x := by
  simpa [stalkDiagram, extendStalkDiagram] using
    Functor.isoWhiskerLeft (basisOpenNhdsInclusion B x).op F.restrictExtendIso

variable [HasColimits C]

/-- The stalk of a sheaf on the basis `B` at `x`, computed as the colimit over basis
neighborhoods of `x`. -/
abbrev stalk (F : BasisSiteSheaf C B hB) (x : X) : C :=
  colimit (F.stalkDiagram x)

/-- The canonical comparison morphism from the basis stalk of `F` at `x` to the stalk at `x` of
the extended sheaf `F.extend`. -/
abbrev stalkComparison (F : BasisSiteSheaf C B hB) (x : X) :
    F.stalk x ⟶ Presheaf.stalk F.extend.presheaf x := by
  letI : Functor.Final (basisOpenNhdsToOpenNhds B x).op :=
    basisOpenNhdsToOpenNhds_final hB x
  let G := F.extend.presheaf
  exact (HasColimit.isoOfNatIso (F.stalkDiagramIso x)).hom ≫
    (colimitIso (basisOpenNhdsToOpenNhds B x).op ((OpenNhds.inclusion x).op ⋙ G)).hom

end BasisSiteSheaf

variable {hB : Opens.IsBasis B}
variable [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion B).op) C]
variable [HasColimits C]

-- Proof sketch: the unit isomorphism of the dense-subsite comparison identifies `F` with the
-- restriction of `F.extend` to basis opens, giving a comparison between the two basis-neighborhood
-- diagrams. Since basis neighborhoods are final in all neighborhoods of `x`, the induced colimit
-- map from `F.stalk x` to `F.extend.presheaf.stalk x` is an isomorphism.
/-- Basis extension preserves stalks: the canonical comparison morphism from the basis stalk `F_x`
to the stalk of the extended sheaf `F_x^{ext}` is an isomorphism. -/
theorem basis_sheaf_stalkComparison_isIso (F : BasisSiteSheaf C B hB)
    (x : X) :
    IsIso (BasisSiteSheaf.stalkComparison F x) := sorry
