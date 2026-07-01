import Mathlib
import stacks_project.Chap04.Lemma_4_33_7
import stacks_project.Chap21.Situation_21_38_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Functor.Fiber

noncomputable section

universe u v

namespace CategoryTheory
namespace FibredCategoryOver

section

variable (X : RingedSite.{u, v}) (P : FibredCategoryOver X)

/-- The restriction of an abelian sheaf on the total site to the opposite of the fiber over `V`.
-/
private noncomputable abbrev fiberRestrictionPresheaf
    (ℱ : Sheaf (inheritedTopology X.siteTopology P) AddCommGrpCat.{max u v})
    (V : X) :
    (P.p.Fiber V)ᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  ((Functor.Fiber.fiberInclusion : P.p.Fiber V ⥤ P.S).op) ⋙ ℱ.1

/-- The value at `V` of the fiberwise-colimit presheaf attached to `ℱ`. -/
private noncomputable abbrev fiberwiseColimitPresheafObj
    (ℱ : Sheaf (inheritedTopology X.siteTopology P) AddCommGrpCat.{max u v})
    (V : Xᵒᵖ) : AddCommGrpCat.{max u v} :=
  colimit (fiberRestrictionPresheaf X P ℱ (unop V))

/-- The map on sections induced by the chosen strongly cartesian lift over `f : V ⟶ U`. -/
private noncomputable abbrev fiberwiseColimitRestrictionNatTransApp
    (ℱ : Sheaf (inheritedTopology X.siteTopology P) AddCommGrpCat.{max u v})
    {U V : X} (f : V ⟶ U) (x : (P.p.Fiber U)ᵒᵖ) :
    (fiberRestrictionPresheaf X P ℱ U).obj x ⟶
      (((canonicalPullbackChoice P.p).pullbackFunctor f).op ⋙
        fiberRestrictionPresheaf X P ℱ V).obj x :=
  ℱ.1.map (op ((canonicalPullbackChoice P.p).map f x.unop))

-- Proof sketch: for a morphism in the fiber over `U`, naturality is the contravariant functoriality
-- of `ℱ.1` applied to the commutative square determined by the chosen pullback functor on fibers.
/-- The chosen pullback maps define a natural transformation from restriction over `U` to the
pullback of the restriction over `V`. -/
private theorem fiberwiseColimitRestrictionNatTrans_naturality
    (ℱ : Sheaf (inheritedTopology X.siteTopology P) AddCommGrpCat.{max u v})
    {U V : X} (f : V ⟶ U) :
    ∀ {x y : (P.p.Fiber U)ᵒᵖ} (g : x ⟶ y),
      (fiberRestrictionPresheaf X P ℱ U).map g ≫
          fiberwiseColimitRestrictionNatTransApp X P ℱ f y =
        fiberwiseColimitRestrictionNatTransApp X P ℱ f x ≫
          ((((canonicalPullbackChoice P.p).pullbackFunctor f).op ⋙
            fiberRestrictionPresheaf X P ℱ V).map g) := sorry

/-- The natural transformation on fiber restrictions induced by the chosen pullback functor over
`f : V ⟶ U`. -/
private noncomputable def fiberwiseColimitRestrictionNatTrans
    (ℱ : Sheaf (inheritedTopology X.siteTopology P) AddCommGrpCat.{max u v})
    {U V : X} (f : V ⟶ U) :
    fiberRestrictionPresheaf X P ℱ U ⟶
      ((canonicalPullbackChoice P.p).pullbackFunctor f).op ⋙
        fiberRestrictionPresheaf X P ℱ V where
  app x := fiberwiseColimitRestrictionNatTransApp X P ℱ f x
  naturality := fun {_ _} g ↦ fiberwiseColimitRestrictionNatTrans_naturality X P ℱ f g

/-- The cocone leg from an object of the fiber over `U` to the colimit over the fiber over `V`
attached to `f : V ⟶ U`. -/
private noncomputable abbrev fiberwiseColimitRestrictionCoconeApp
    (ℱ : Sheaf (inheritedTopology X.siteTopology P) AddCommGrpCat.{max u v})
    {U V : X} (f : V ⟶ U) (x : (P.p.Fiber U)ᵒᵖ) :
    (fiberRestrictionPresheaf X P ℱ U).obj x ⟶ fiberwiseColimitPresheafObj X P ℱ (op V) :=
  fiberwiseColimitRestrictionNatTransApp X P ℱ f x ≫
    colimit.ι (fiberRestrictionPresheaf X P ℱ V)
      (((canonicalPullbackChoice P.p).pullbackFunctor f).op.obj x)

-- Proof sketch: the cocone legs are the natural-transformation components above followed by the
-- universal cocone morphisms into the colimit over the target fiber.
/-- The comparison maps to the target-fiber colimit are natural in objects of the source fiber. -/
private theorem fiberwiseColimitRestrictionCocone_naturality
    (ℱ : Sheaf (inheritedTopology X.siteTopology P) AddCommGrpCat.{max u v})
    {U V : X} (f : V ⟶ U) :
    ∀ {x y : (P.p.Fiber U)ᵒᵖ} (g : x ⟶ y),
      (fiberRestrictionPresheaf X P ℱ U).map g ≫
          fiberwiseColimitRestrictionCoconeApp X P ℱ f y =
        fiberwiseColimitRestrictionCoconeApp X P ℱ f x := sorry

/-- The cocone over the restricted diagram on the fiber over `U` with vertex the colimit over the
fiber over `V`, induced by pullback along `f : V ⟶ U`. -/
private noncomputable def fiberwiseColimitRestrictionCocone
    (ℱ : Sheaf (inheritedTopology X.siteTopology P) AddCommGrpCat.{max u v})
    {U V : X} (f : V ⟶ U) :
    Cocone (fiberRestrictionPresheaf X P ℱ U) where
  pt := fiberwiseColimitPresheafObj X P ℱ (op V)
  ι :=
    { app := fiberwiseColimitRestrictionCoconeApp X P ℱ f
      naturality := fun {_ _} g ↦ fiberwiseColimitRestrictionCocone_naturality X P ℱ f g }

/-- The restriction map on the fiberwise-colimit presheaf induced by `f : V ⟶ U`. -/
private noncomputable abbrev fiberwiseColimitPresheafMap
    (ℱ : Sheaf (inheritedTopology X.siteTopology P) AddCommGrpCat.{max u v})
    {U V : Xᵒᵖ} (f : U ⟶ V) :
    fiberwiseColimitPresheafObj X P ℱ U ⟶ fiberwiseColimitPresheafObj X P ℱ V :=
  show fiberwiseColimitPresheafObj X P ℱ U ⟶ fiberwiseColimitPresheafObj X P ℱ V from
    colimit.desc (fiberRestrictionPresheaf X P ℱ (unop U))
      (fiberwiseColimitRestrictionCocone X P ℱ f.unop)

-- Proof sketch: for the identity arrow, the canonical pullback functor on the fiber is naturally
-- isomorphic to the identity, so the induced colimit map is the identity.
/-- The restriction map of the fiberwise-colimit presheaf is the identity on identity arrows. -/
private theorem fiberwiseColimitPresheaf_map_id
    (ℱ : Sheaf (inheritedTopology X.siteTopology P) AddCommGrpCat.{max u v})
    (U : Xᵒᵖ) :
    fiberwiseColimitPresheafMap X P ℱ (𝟙 U) =
      𝟙 (fiberwiseColimitPresheafObj X P ℱ U) := sorry

-- Proof sketch: compose the cocones coming from the chosen pullback functors along `g` and `f`,
-- then use the universal property of the colimit over the source fiber.
/-- The restriction maps of the fiberwise-colimit presheaf respect composition. -/
private theorem fiberwiseColimitPresheaf_map_comp
    (ℱ : Sheaf (inheritedTopology X.siteTopology P) AddCommGrpCat.{max u v})
    {U V W : Xᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    fiberwiseColimitPresheafMap X P ℱ (f ≫ g) =
      fiberwiseColimitPresheafMap X P ℱ f ≫
        fiberwiseColimitPresheafMap X P ℱ g := sorry

/-- The presheaf on the base site sending `V` to the colimit of the restriction of `ℱ` to the
fiber over `V`. -/
private noncomputable def fiberwiseColimitPresheaf
    (ℱ : Sheaf (inheritedTopology X.siteTopology P) AddCommGrpCat.{max u v}) :
    Xᵒᵖ ⥤ AddCommGrpCat.{max u v} where
  obj := fiberwiseColimitPresheafObj X P ℱ
  map := fiberwiseColimitPresheafMap X P ℱ
  map_id := fiberwiseColimitPresheaf_map_id X P ℱ
  map_comp := fiberwiseColimitPresheaf_map_comp X P ℱ

-- Proof sketch: compare morphisms from the sheafification of the fiberwise-colimit presheaf into
-- any abelian sheaf on `X` with compatible families of morphisms from `ℱ` on the fibers, and then
-- identify those with morphisms from `ℱ` into the inverse image along `π`.
/-- Lemma 21.38.8: for an abelian sheaf `ℱ` on the total site of a fibred category `P` over the
ringed site `X`, the lower shriek `π_! ℱ` is the sheaf associated to the presheaf sending an
object `V` of the base to the colimit of the restriction of `ℱ` over the opposite of the fiber
category `P.p.Fiber V`. -/
theorem lowerShriek_is_sheafification_of_fiberwiseColimitPresheaf
    [Functor.IsContinuous P.p (inheritedTopology X.siteTopology P) X.siteTopology]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [((P.p.sheafPushforwardContinuous
      AddCommGrpCat.{max u v}
      (inheritedTopology X.siteTopology P)
      X.siteTopology).IsRightAdjoint)]
    (ℱ : Sheaf (inheritedTopology X.siteTopology P) AddCommGrpCat.{max u v}) :
    IsIsomorphic
      ((P.p.sheafPullback
          AddCommGrpCat.{max u v}
          (inheritedTopology X.siteTopology P)
          X.siteTopology).obj ℱ)
      ((presheafToSheaf X.siteTopology AddCommGrpCat.{max u v}).obj
        (fiberwiseColimitPresheaf X P ℱ)) := sorry

end

end FibredCategoryOver
end CategoryTheory
