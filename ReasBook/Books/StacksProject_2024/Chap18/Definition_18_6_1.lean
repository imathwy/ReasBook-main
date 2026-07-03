import Mathlib
import stacks_project.Chap07.Definition_7_14_1
import stacks_project.Chap07.Lemma_7_14_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

/-- Definition 18.6.1: a ringed site is a site together with a sheaf of rings on it. -/
structure RingedSite where
  carrier : Type u
  [str : Category.{v} carrier]
  siteTopology : GrothendieckTopology carrier
  structureSheaf : Sheaf siteTopology RingCat.{max u v}

/-- A ringed site coerces to its underlying category of objects. -/
instance : CoeSort RingedSite (Type u) where
  coe X := X.carrier

attribute [instance] RingedSite.str

namespace RingedSite

/-- A site with a sheaf of commutative rings, viewed as a ringed site through the canonical
forgetful functor `CommRingCat ⥤ RingCat`. -/
abbrev ofCommRingSheaf
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    RingedSite.{u, v} where
  carrier := C
  siteTopology := J
  structureSheaf := (sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪

/-- A morphism of ringed sites, recorded by the underlying morphism of sites together with the
adjoint form `\mathcal O_Y \to f_* \mathcal O_X` of the structure-sheaf map. -/
structure Hom (X Y : RingedSite.{u, v}) where
  base : Y ⥤ X
  [isMorphismOfSites : IsMorphismOfSites Y.siteTopology X.siteTopology base]
  structureSheafMap :
    Y.structureSheaf ⟶
      (base.sheafPushforwardContinuous RingCat.{max u v}
        Y.siteTopology X.siteTopology).obj X.structureSheaf

attribute [instance] Hom.isMorphismOfSites

variable {X Y Z : RingedSite.{u, v}}

/-- The identity morphism of a ringed site. -/
noncomputable def Hom.id (X : RingedSite.{u, v}) : Hom X X where
  base := 𝟭 X
  isMorphismOfSites := by infer_instance
  structureSheafMap := 𝟙 X.structureSheaf

/-- Composition of morphisms of ringed sites. The underlying site morphism is the composite of
the underlying morphisms of sites, and the structure-sheaf map is `g^\sharp \circ f^\sharp` in
the adjoint pushforward form used in Lean. -/
noncomputable def Hom.comp (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := g.base ⋙ f.base
  isMorphismOfSites :=
    isMorphismOfSites_comp g.base f.base Z.siteTopology Y.siteTopology X.siteTopology
  structureSheafMap :=
    g.structureSheafMap ≫
      (g.base.sheafPushforwardContinuous RingCat.{max u v}
        Z.siteTopology Y.siteTopology).map f.structureSheafMap

instance : CategoryStruct RingedSite where
  Hom X Y := Hom X Y
  id := Hom.id
  comp f g := Hom.comp f g

end RingedSite
