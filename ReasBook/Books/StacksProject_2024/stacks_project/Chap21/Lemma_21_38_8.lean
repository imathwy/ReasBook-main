import StacksProject_2024.Chap04.Lemma_4_33_7
import StacksProject_2024.Chap08.Lemma_8_10_3

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

variable {C : Type u} [Category.{v} C] (P : FibredCategoryOver C)

/- Domain-style sampling for Lemma 21.38.8:
- primary domain: lower shriek on abelian sheaves over the inherited site of a fibred category,
  and its presentation by fiberwise colimits;
- sampled owner declarations:
  `Functor.sheafPullback`,
  `Functor.sheafAdjunctionContinuous`,
  `Functor.sheafPushforwardContinuous`,
  `Limits.colimit.pre`;
- best owner abstraction: the source-facing theorem should be stated on the canonical lower-shriek
  owner `P.p.sheafPullback AddCommGrpCat Jₚ J`, while the supporting primitive data
  is the restriction of a presheaf on `P.S` to a fiber and the pullback comparison between such
  restrictions;
- primitive data: a presheaf `ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat`, an object `V : C`, and a morphism
  `f : V ⟶ U` in the base site;
- derived API: the pullback-induced natural transformation on fiber restrictions and the
  fiberwise-colimit presheaf on `C`.

Source/core/bridge triage:
- `source-facing`: `fiberwiseColimitPresheaf` and
  `lowerShriek_is_sheafification_of_fiberwiseColimitPresheaf`;
- `core/canonical`: `P.p.sheafPullback AddCommGrpCat Jₚ J`;
- `bridge/view`: `fiberRestrictionPresheaf`, `fiberPullbackPrecomp`,
  `fiberRestrictionComparison`, and the intermediate cocone maps used to define
  `fiberwiseColimitPresheaf`. -/

/-- The restriction of an abelian presheaf on the total site to the opposite of the fiber over
`V`. This is the primitive bridge from abelian presheaves on the total site to presheaves on a
single fiber, and it is reused by the fiberwise homology constructions in the next lemmas. -/
abbrev fiberRestrictionPresheaf
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v})
    (V : C) :
    (P.p.Fiber V)ᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  ((fiberInclusion : P.p.Fiber V ⥤ P.S).op) ⋙ ℱ

/-- Evaluating `fiberRestrictionPresheaf P ℱ V` at a fiber object just evaluates `ℱ` at the
underlying total-site object. -/
theorem fiberRestrictionPresheaf_obj
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v})
    (V : C) (x : (P.p.Fiber V)ᵒᵖ) :
    (fiberRestrictionPresheaf P ℱ V).obj x = ℱ.obj (op x.unop.1) :=
  rfl

/-- On a morphism in the fiber over `V`, `fiberRestrictionPresheaf P ℱ V` acts by the corresponding
restriction map of `ℱ` on the total site. -/
theorem fiberRestrictionPresheaf_map
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v})
    (V : C) {x y : (P.p.Fiber V)ᵒᵖ} (g : x ⟶ y) :
    (fiberRestrictionPresheaf P ℱ V).map g = ℱ.map (op g.unop.1) :=
  rfl

/-- Precomposition along the canonical pullback functor between fibers over a morphism in the base
site. -/
def fiberPullbackPrecomp {U V : C} (f : V ⟶ U) :
    ((P.p.Fiber V)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤
      ((P.p.Fiber U)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) :=
  (Functor.whiskeringLeft (P.p.Fiber U)ᵒᵖ (P.p.Fiber V)ᵒᵖ AddCommGrpCat.{max u v}).obj
    (((canonicalPullbackChoice P.p).pullbackFunctor f).op)

section

variable (J : GrothendieckTopology C)

local notation "Jₚ" => inheritedTopology J P

/-- The value at `V` of the fiberwise-colimit presheaf attached to `ℱ`. -/
private def fiberwiseColimitPresheafObj
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v})
    (V : Cᵒᵖ) : AddCommGrpCat.{max u v} :=
  colimit (fiberRestrictionPresheaf P ℱ (unop V))

/-- The map on sections induced by the canonical cartesian pullback lift over `f : V ⟶ U`. -/
private def fiberRestrictionComparisonApp
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v})
    {U V : C} (f : V ⟶ U) (x : (P.p.Fiber U)ᵒᵖ) :
    (fiberRestrictionPresheaf P ℱ U).obj x ⟶
      ((fiberPullbackPrecomp P f).obj (fiberRestrictionPresheaf P ℱ V)).obj x :=
  ℱ.map (op ((canonicalPullbackChoice P.p).map f x.unop))

-- Proof sketch: for a morphism in the fiber over `U`, naturality is the contravariant functoriality
-- of `ℱ.1` applied to the factorization property of the canonical cartesian pullback map on
-- fibers.
/-- The canonical pullback maps define a natural transformation from restriction over `U` to the
pullback of the restriction over `V`. -/
private theorem fiberRestrictionComparison_naturality
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v})
    {U V : C} (f : V ⟶ U) :
    ∀ {x y : (P.p.Fiber U)ᵒᵖ} (g : x ⟶ y),
      (fiberRestrictionPresheaf P ℱ U).map g ≫
          fiberRestrictionComparisonApp P ℱ f y =
        fiberRestrictionComparisonApp P ℱ f x ≫
          ((fiberPullbackPrecomp P f).obj (fiberRestrictionPresheaf P ℱ V)).map g := by
  intro x y g
  let hc := canonicalPullbackChoice P.p
  have hfac :
      ((hc.pullbackFunctor f).map g.unop).1 ≫ hc.map f x.unop =
        hc.map f y.unop ≫ g.unop.1 := by
    letI : P.p.IsStronglyCartesian f (hc.map f x.unop) := hc.isStronglyCartesian f x.unop
    letI : P.p.IsStronglyCartesian f (hc.map f y.unop) := hc.isStronglyCartesian f y.unop
    letI : P.p.IsHomLift (𝟙 U) g.unop.1 := g.unop.2
    change
      Functor.IsStronglyCartesian.map P.p f (hc.map f x.unop) (Category.id_comp f).symm
          (hc.map f y.unop ≫ g.unop.1) ≫
            hc.map f x.unop =
        hc.map f y.unop ≫ g.unop.1
    exact Functor.IsStronglyCartesian.fac P.p f (hc.map f x.unop) (Category.id_comp f).symm
      (hc.map f y.unop ≫ g.unop.1)
  dsimp [fiberRestrictionPresheaf, fiberPullbackPrecomp, fiberRestrictionComparisonApp]
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg
    (fun k :
      (((canonicalPullbackChoice P.p).pullbackFunctor f).obj y.unop).1 ⟶ x.unop.1 ↦
      ℱ.map
        (show op x.unop.1 ⟶
            op ((((canonicalPullbackChoice P.p).pullbackFunctor f).obj y.unop).1) from op k))
    hfac.symm

/-- The natural transformation on fiber restrictions induced by the canonical pullback functor over
`f : V ⟶ U`. -/
def fiberRestrictionComparison
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v})
    {U V : C} (f : V ⟶ U) :
    fiberRestrictionPresheaf P ℱ U ⟶
      (fiberPullbackPrecomp P f).obj (fiberRestrictionPresheaf P ℱ V) where
  app x := fiberRestrictionComparisonApp P ℱ f x
  naturality := fun {_ _} g ↦ fiberRestrictionComparison_naturality P ℱ f g

/-- The component of `fiberRestrictionComparison P ℱ f` at a fiber object is the canonical
pullback map on the underlying presheaf `ℱ`. -/
@[simp] theorem fiberRestrictionComparison_app
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v})
    {U V : C} (f : V ⟶ U) (x : (P.p.Fiber U)ᵒᵖ) :
    (fiberRestrictionComparison P ℱ f).app x =
      ℱ.map (op ((canonicalPullbackChoice P.p).map f x.unop)) :=
  rfl

/-- The cocone leg from an object of the fiber over `U` to the colimit over the fiber over `V`
attached to `f : V ⟶ U`. -/
private def fiberwiseColimitRestrictionCoconeApp
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v})
    {U V : C} (f : V ⟶ U) (x : (P.p.Fiber U)ᵒᵖ) :
    (fiberRestrictionPresheaf P ℱ U).obj x ⟶ fiberwiseColimitPresheafObj P ℱ (op V) :=
  fiberRestrictionComparisonApp P ℱ f x ≫
    colimit.ι (fiberRestrictionPresheaf P ℱ V)
      (((canonicalPullbackChoice P.p).pullbackFunctor f).op.obj x)

-- Proof sketch: the cocone legs are the natural-transformation components above followed by the
-- universal cocone morphisms into the colimit over the target fiber.
/-- The comparison maps to the target-fiber colimit are natural in objects of the source fiber. -/
private theorem fiberwiseColimitRestrictionCocone_naturality
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v})
    {U V : C} (f : V ⟶ U) :
    ∀ {x y : (P.p.Fiber U)ᵒᵖ} (g : x ⟶ y),
      (fiberRestrictionPresheaf P ℱ U).map g ≫
          fiberwiseColimitRestrictionCoconeApp P ℱ f y =
        fiberwiseColimitRestrictionCoconeApp P ℱ f x := by
  intro x y g
  calc
    (fiberRestrictionPresheaf P ℱ U).map g ≫
        fiberwiseColimitRestrictionCoconeApp P ℱ f y =
      ((fiberRestrictionPresheaf P ℱ U).map g ≫
          fiberRestrictionComparisonApp P ℱ f y) ≫
        colimit.ι (fiberRestrictionPresheaf P ℱ V)
          (((canonicalPullbackChoice P.p).pullbackFunctor f).op.obj y) := by
        simp [fiberwiseColimitRestrictionCoconeApp, Category.assoc]
    _ =
      (fiberRestrictionComparisonApp P ℱ f x ≫
          ((fiberPullbackPrecomp P f).obj (fiberRestrictionPresheaf P ℱ V)).map g) ≫
        colimit.ι (fiberRestrictionPresheaf P ℱ V)
          (((canonicalPullbackChoice P.p).pullbackFunctor f).op.obj y) := by
        rw [fiberRestrictionComparison_naturality]
    _ =
      fiberRestrictionComparisonApp P ℱ f x ≫
        (((fiberPullbackPrecomp P f).obj (fiberRestrictionPresheaf P ℱ V)).map g ≫
          colimit.ι (fiberRestrictionPresheaf P ℱ V)
            (((canonicalPullbackChoice P.p).pullbackFunctor f).op.obj y)) := by
        simp [Category.assoc]
    _ =
      fiberRestrictionComparisonApp P ℱ f x ≫
        colimit.ι (fiberRestrictionPresheaf P ℱ V)
          (((canonicalPullbackChoice P.p).pullbackFunctor f).op.obj x) := by
        simpa [fiberPullbackPrecomp, Category.assoc] using
          congrArg
            (fun k ↦ fiberRestrictionComparisonApp P ℱ f x ≫ k)
            (colimit.w (fiberRestrictionPresheaf P ℱ V)
              (((canonicalPullbackChoice P.p).pullbackFunctor f).op.map g))
    _ = fiberwiseColimitRestrictionCoconeApp P ℱ f x := by
        simp [fiberwiseColimitRestrictionCoconeApp]

/-- The cocone over the restricted diagram on the fiber over `U` with vertex the colimit over the
fiber over `V`, induced by pullback along `f : V ⟶ U`. -/
private def fiberwiseColimitRestrictionCocone
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v})
    {U V : C} (f : V ⟶ U) :
    Cocone (fiberRestrictionPresheaf P ℱ U) where
  pt := fiberwiseColimitPresheafObj P ℱ (op V)
  ι :=
    { app := fiberwiseColimitRestrictionCoconeApp P ℱ f
      naturality := fun {_ _} g ↦ fiberwiseColimitRestrictionCocone_naturality P ℱ f g }

/-- The restriction map on the fiberwise-colimit presheaf induced by `f : V ⟶ U`. -/
private def fiberwiseColimitPresheafMap
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v})
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    fiberwiseColimitPresheafObj P ℱ U ⟶ fiberwiseColimitPresheafObj P ℱ V :=
  show fiberwiseColimitPresheafObj P ℱ U ⟶ fiberwiseColimitPresheafObj P ℱ V from
    colimit.desc (fiberRestrictionPresheaf P ℱ (unop U))
      (fiberwiseColimitRestrictionCocone P ℱ f.unop)

/-- Helper for Lemma 21.38.8: on a colimit generator, the restriction map for an identity arrow
rewrites back to the same colimit leg through the identity pullback comparison. -/
private theorem fiberwiseColimitPresheaf_map_id_on_ι
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v})
    (U : Cᵒᵖ) (x : (P.p.Fiber (unop U))ᵒᵖ) :
    colimit.ι (fiberRestrictionPresheaf P ℱ (unop U)) x ≫
        fiberwiseColimitPresheafMap P ℱ (𝟙 U) =
      colimit.ι (fiberRestrictionPresheaf P ℱ (unop U)) x := by
  let hc := canonicalPullbackChoice P.p
  have hmap :
      ((hc.pullbackIdIso (unop U)).inv.app x.unop).1 =
        hc.map (𝟙 (unop U)) x.unop := by
    -- Compare the inverse component with the chosen cartesian arrow by composing with the
    -- defining triangle of `pullbackIdIso`.
    have h :=
      congrArg
        (fun k ↦ k ≫ hc.map (𝟙 (unop U)) x.unop)
        (congrArg (fun k ↦ k.1) ((hc.pullbackIdIso (unop U)).inv_hom_id_app x.unop))
    change
      ((hc.pullbackIdIso (unop U)).inv.app x.unop).1 ≫
          ((hc.pullbackIdIso (unop U)).hom.app x.unop).1 ≫
            hc.map (𝟙 (unop U)) x.unop =
        𝟙 _ ≫ hc.map (𝟙 (unop U)) x.unop at h
    simpa [Category.assoc, hc.pullbackIdComponentIso_fac] using h
  calc
    colimit.ι (fiberRestrictionPresheaf P ℱ (unop U)) x ≫
        fiberwiseColimitPresheafMap P ℱ (𝟙 U) =
      ℱ.map (op (((hc.pullbackIdIso (unop U)).inv.app x.unop).1)) ≫
        colimit.ι (fiberRestrictionPresheaf P ℱ (unop U))
          ((hc.pullbackFunctor (𝟙 (unop U))).op.obj x) := by
        -- Read the defining cocone leg of the colimit-desc restriction map.
        simpa [fiberwiseColimitPresheafMap, fiberwiseColimitRestrictionCoconeApp,
          fiberRestrictionComparisonApp, hmap] using
          (colimit.ι_desc (fiberwiseColimitRestrictionCocone P ℱ (𝟙 (unop U))) x)
    _ = colimit.ι (fiberRestrictionPresheaf P ℱ (unop U)) x := by
        -- The inverse component of `pullbackIdIso` is a morphism in the fiber, so the colimit
        -- cocone relation rewrites the target leg back to the original generator.
        simpa [fiberRestrictionPresheaf_map] using
          (colimit.w (fiberRestrictionPresheaf P ℱ (unop U))
            (op ((hc.pullbackIdIso (unop U)).inv.app x.unop)))

/-- Helper for Lemma 21.38.8: on a colimit generator, the restriction map for a composite arrow
agrees with the composite of the restriction maps for the two chosen pullback functors. -/
private theorem fiberwiseColimitPresheaf_map_comp_on_ι
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v})
    {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (x : (P.p.Fiber (unop U))ᵒᵖ) :
    colimit.ι (fiberRestrictionPresheaf P ℱ (unop U)) x ≫
        fiberwiseColimitPresheafMap P ℱ (f ≫ g) =
      colimit.ι (fiberRestrictionPresheaf P ℱ (unop U)) x ≫
        fiberwiseColimitPresheafMap P ℱ f ≫
          fiberwiseColimitPresheafMap P ℱ g := by
  let hc := canonicalPullbackChoice P.p
  have hcomp :
      ((hc.pullbackCompIso f.unop g.unop).inv.app x.unop).1 ≫
          hc.map ((f ≫ g).unop) x.unop =
        hc.map g.unop ((hc.pullbackFunctor f.unop).obj x.unop) ≫
          hc.map f.unop x.unop := by
    -- Compose the inverse-component identity with the chosen composite pullback map to recover
    -- the textbook factorization encoded by `pullbackCompIso`.
    have h :=
      congrArg
        (fun k ↦ k ≫ hc.map ((f ≫ g).unop) x.unop)
        (congrArg (fun k ↦ k.1) ((hc.pullbackCompIso f.unop g.unop).inv_hom_id_app x.unop))
    change
      ((hc.pullbackCompIso f.unop g.unop).inv.app x.unop).1 ≫
          ((hc.pullbackCompIso f.unop g.unop).hom.app x.unop).1 ≫
            hc.map ((f ≫ g).unop) x.unop =
        𝟙 _ ≫ hc.map ((f ≫ g).unop) x.unop at h
    simpa [Category.assoc, hc.pullbackCompComponentIso_fac] using h
  calc
    colimit.ι (fiberRestrictionPresheaf P ℱ (unop U)) x ≫
        fiberwiseColimitPresheafMap P ℱ (f ≫ g) =
      ℱ.map (op (hc.map ((f ≫ g).unop) x.unop)) ≫
        colimit.ι (fiberRestrictionPresheaf P ℱ (unop W))
          ((hc.pullbackFunctor ((f ≫ g).unop)).op.obj x) := by
        -- Evaluate the colimit-desc map on the generator `x`.
        simpa [fiberwiseColimitPresheafMap, fiberwiseColimitRestrictionCoconeApp,
          fiberRestrictionComparisonApp] using
          (colimit.ι_desc (fiberwiseColimitRestrictionCocone P ℱ ((f ≫ g).unop)) x)
    _ =
      ℱ.map (op (hc.map ((f ≫ g).unop) x.unop)) ≫
        ℱ.map (op (((hc.pullbackCompIso f.unop g.unop).inv.app x.unop).1)) ≫
          colimit.ι (fiberRestrictionPresheaf P ℱ (unop W))
            (((hc.pullbackFunctor f.unop ⋙ hc.pullbackFunctor g.unop).op.obj x)) := by
        -- Move from the chosen pullback for `f ≫ g` to the iterated pullback using the inverse
        -- comparison component, then read the resulting cocone leg.
        rw [← Category.assoc]
        simpa [fiberRestrictionPresheaf_map] using
          (colimit.w (fiberRestrictionPresheaf P ℱ (unop W))
            (op ((hc.pullbackCompIso f.unop g.unop).inv.app x.unop)))
    _ =
      ℱ.map (op (hc.map f.unop x.unop)) ≫
        ℱ.map (op (hc.map g.unop ((hc.pullbackFunctor f.unop).obj x.unop))) ≫
          colimit.ι (fiberRestrictionPresheaf P ℱ (unop W))
            (((hc.pullbackFunctor f.unop ⋙ hc.pullbackFunctor g.unop).op.obj x)) := by
        -- Collapse the two consecutive pullback maps to the composite pullback map.
        rw [← Functor.map_comp, congrArg Quiver.Hom.op hcomp, Functor.map_comp]
    _ =
      colimit.ι (fiberRestrictionPresheaf P ℱ (unop U)) x ≫
        fiberwiseColimitPresheafMap P ℱ f ≫
          fiberwiseColimitPresheafMap P ℱ g := by
        -- Expand the two restriction maps on generators and regroup.
        calc
          ℱ.map (op (hc.map f.unop x.unop)) ≫
              ℱ.map (op (hc.map g.unop ((hc.pullbackFunctor f.unop).obj x.unop))) ≫
                colimit.ι (fiberRestrictionPresheaf P ℱ (unop W))
                  (((hc.pullbackFunctor f.unop ⋙ hc.pullbackFunctor g.unop).op.obj x)) =
            (ℱ.map (op (hc.map f.unop x.unop)) ≫
                colimit.ι (fiberRestrictionPresheaf P ℱ (unop V))
                  ((hc.pullbackFunctor f.unop).op.obj x)) ≫
                fiberwiseColimitPresheafMap P ℱ g := by
                  rw [Category.assoc]
                  simpa [fiberwiseColimitPresheafMap, fiberwiseColimitRestrictionCoconeApp,
                    fiberRestrictionComparisonApp, Category.assoc] using
                    congrArg
                      (fun k ↦ ℱ.map (op (hc.map f.unop x.unop)) ≫ k)
                      (colimit.ι_desc (fiberwiseColimitRestrictionCocone P ℱ g.unop)
                        ((hc.pullbackFunctor f.unop).op.obj x))
          _ =
            colimit.ι (fiberRestrictionPresheaf P ℱ (unop U)) x ≫
              fiberwiseColimitPresheafMap P ℱ f ≫
                fiberwiseColimitPresheafMap P ℱ g := by
                  rw [← Category.assoc]
                  simpa [fiberwiseColimitPresheafMap, fiberwiseColimitRestrictionCoconeApp,
                    fiberRestrictionComparisonApp] using
                    (colimit.ι_desc (fiberwiseColimitRestrictionCocone P ℱ f.unop) x).symm

-- Proof sketch: for the identity arrow, the canonical pullback functor on the fiber is naturally
-- isomorphic to the identity, so the induced colimit map is the identity.
/-- The restriction map of the fiberwise-colimit presheaf is the identity on identity arrows. -/
private theorem fiberwiseColimitPresheaf_map_id
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v})
    (U : Cᵒᵖ) :
    fiberwiseColimitPresheafMap P ℱ (𝟙 U) =
      𝟙 (fiberwiseColimitPresheafObj P ℱ U) := by
  apply colimit.hom_ext
  intro x
  simpa using fiberwiseColimitPresheaf_map_id_on_ι P ℱ U x

-- Proof sketch: compose the cocones coming from the chosen pullback functors along `g` and `f`,
-- then use the universal property of the colimit over the source fiber.
/-- The restriction maps of the fiberwise-colimit presheaf respect composition. -/
private theorem fiberwiseColimitPresheaf_map_comp
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v})
    {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    fiberwiseColimitPresheafMap P ℱ (f ≫ g) =
      fiberwiseColimitPresheafMap P ℱ f ≫
        fiberwiseColimitPresheafMap P ℱ g := by
  -- The generator-level comparison already identifies the two morphisms out of the colimit.
  apply colimit.hom_ext
  intro x
  simpa [Category.assoc] using fiberwiseColimitPresheaf_map_comp_on_ι P ℱ f g x

/-- The source-facing presheaf on the base site sending `V` to the colimit of the restriction of
`ℱ` to the fiber over `V`. -/
def fiberwiseColimitPresheaf
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    Cᵒᵖ ⥤ AddCommGrpCat.{max u v} where
  obj := fiberwiseColimitPresheafObj P ℱ
  map := fiberwiseColimitPresheafMap P ℱ
  map_id := fiberwiseColimitPresheaf_map_id P ℱ
  map_comp := fiberwiseColimitPresheaf_map_comp P ℱ

/-- The value of `fiberwiseColimitPresheaf P ℱ` at `V` is the colimit of the restriction of `ℱ`
to the opposite of the fiber over `unop V`. -/
theorem fiberwiseColimitPresheaf_obj
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v})
    (V : Cᵒᵖ) :
    (fiberwiseColimitPresheaf P ℱ).obj V =
      colimit (fiberRestrictionPresheaf P ℱ (unop V)) :=
  rfl

/-- Bridge view: the associated sheaf on the base site attached to the source-facing fiberwise
colimit presheaf of an abelian sheaf on the total site. -/
def fiberwiseColimitSheafOfSheaf
    (ℱ : Sheaf Jₚ AddCommGrpCat.{max u v}) :
    Sheaf J AddCommGrpCat.{max u v} :=
  (presheafToSheaf J AddCommGrpCat.{max u v}).obj
    (fiberwiseColimitPresheaf P ℱ.1)

/-- On a colimit generator, the restriction map of `fiberwiseColimitPresheaf P ℱ` is induced by
the canonical pullback morphism in the corresponding fiber. This is the source-facing bridge from
the colimit presentation to restriction along a morphism in the base site. -/
theorem fiberwiseColimitPresheaf_ι_map
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v})
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : (P.p.Fiber (unop U))ᵒᵖ) :
    colimit.ι (fiberRestrictionPresheaf P ℱ (unop U)) x ≫
        (fiberwiseColimitPresheaf P ℱ).map f =
      ℱ.map (op ((canonicalPullbackChoice P.p).map f.unop x.unop)) ≫
        colimit.ι (fiberRestrictionPresheaf P ℱ (unop V))
          (((canonicalPullbackChoice P.p).pullbackFunctor f.unop).op.obj x) := by
  simpa [fiberwiseColimitPresheaf, fiberwiseColimitPresheafMap,
    fiberwiseColimitRestrictionCoconeApp, fiberRestrictionComparisonApp] using
    (colimit.ι_desc (fiberwiseColimitRestrictionCocone P ℱ f.unop) x)

/-- Helper for Lemma 21.38.8: the underlying presheaf of the continuous pushforward is the
expected precomposition with the projection functor `P.p`. -/
private def pushforwardUnderlyingPresheafIso
    [Functor.IsContinuous P.p Jₚ J]
    (𝒢 : Sheaf J AddCommGrpCat.{max u v}) :
    (((P.p.sheafPushforwardContinuous AddCommGrpCat.{max u v} Jₚ J).obj 𝒢).1) ≅
      P.p.op ⋙ 𝒢.1 :=
  (P.p.sheafPushforwardContinuousCompSheafToPresheafIso AddCommGrpCat.{max u v} Jₚ J).app 𝒢

/-- Helper for Lemma 21.38.8: a morphism into the pushforward sheaf yields the source-proof
compatible family of maps `ℱ(X) → 𝒢(p(X))` on total-site objects. -/
private def pushforwardCompatibleFamilyApp
    [Functor.IsContinuous P.p Jₚ J]
    {ℱ : Sheaf Jₚ AddCommGrpCat.{max u v}}
    {𝒢 : Sheaf J AddCommGrpCat.{max u v}}
    (φ : ℱ ⟶ (P.p.sheafPushforwardContinuous AddCommGrpCat.{max u v} Jₚ J).obj 𝒢)
    (X : P.S) :
    ℱ.1.obj (op X) ⟶ 𝒢.1.obj (op (P.p.obj X)) :=
  φ.1.app (op X) ≫ (pushforwardUnderlyingPresheafIso P J 𝒢).hom.app (op X)

-- Proof sketch: first apply naturality of the sheaf morphism `φ`, then rewrite the pushforward
-- restriction map through the canonical presheaf comparison iso.
/-- Helper for Lemma 21.38.8: the compatible family extracted from a pushforward morphism is
natural under restriction in the total category. -/
private theorem pushforwardCompatibleFamily_naturality
    [Functor.IsContinuous P.p Jₚ J]
    {ℱ : Sheaf Jₚ AddCommGrpCat.{max u v}}
    {𝒢 : Sheaf J AddCommGrpCat.{max u v}}
    (φ : ℱ ⟶ (P.p.sheafPushforwardContinuous AddCommGrpCat.{max u v} Jₚ J).obj 𝒢)
    {X Y : P.S} (α : X ⟶ Y) :
    ℱ.1.map (op α) ≫ pushforwardCompatibleFamilyApp P J φ X =
      pushforwardCompatibleFamilyApp P J φ Y ≫
        𝒢.1.map (op (P.p.map α)) := by
  -- First use naturality of `φ`, then rewrite the pushforward leg through the comparison iso.
  dsimp [pushforwardCompatibleFamilyApp]
  calc
    ℱ.1.map (op α) ≫ φ.1.app (op X) ≫
        (pushforwardUnderlyingPresheafIso P J 𝒢).hom.app (op X) =
      (φ.1.app (op Y) ≫
          (((P.p.sheafPushforwardContinuous AddCommGrpCat.{max u v} Jₚ J).obj 𝒢).1.map
            (op α))) ≫
          (pushforwardUnderlyingPresheafIso P J 𝒢).hom.app (op X) := by
            rw [φ.1.naturality]
    _ =
      φ.1.app (op Y) ≫
        (pushforwardUnderlyingPresheafIso P J 𝒢).hom.app (op Y) ≫
          𝒢.1.map (op (P.p.map α)) := by
            rw [Category.assoc]
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ φ.1.app (op Y) ≫ k)
                ((pushforwardUnderlyingPresheafIso P J 𝒢).hom.naturality (op α))

/-- Helper for Lemma 21.38.8: a compatible family on the total site restricts to a section over a
fixed fiber by transporting once along the equality carried by the fiber object. -/
private def fiber_section_of_compatible_family
    {ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    {𝒢 : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    (σ : ∀ X : P.S, ℱ.obj (op X) ⟶ 𝒢.obj (op (P.p.obj X)))
    (V : C) (x : (P.p.Fiber V)ᵒᵖ) :
    (fiberRestrictionPresheaf P ℱ V).obj x ⟶ 𝒢.obj (op V) :=
  σ x.unop.1 ≫
    (show 𝒢.obj (op (P.p.obj x.unop.1)) ⟶ 𝒢.obj (op V) from
      eqToHom (congrArg (fun Z : C ↦ 𝒢.obj (op Z)) x.unop.2))

/-- Helper for Lemma 21.38.8: mapping the transport from `V` back to a fiber object gives the
forward transport on `𝒢`. -/
private theorem presheaf_map_eqToHom_fiber_eq_symm
    {𝒢 : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    {V : C} {x : (P.p.Fiber V)ᵒᵖ} :
    𝒢.map ((eqToHom x.unop.2.symm).op) =
      eqToHom (congrArg (fun Z : C ↦ 𝒢.obj (op Z)) x.unop.2) := by
  -- Normalize the opposite transport once and let the functorial `eqToHom` computation finish.
  erw [eqToHom_op, eqToHom_map]

/-- Helper for Lemma 21.38.8: mapping the transport from a fiber object down to `V` gives the
inverse transport on `𝒢`. -/
private theorem presheaf_map_eqToHom_fiber_eq
    {𝒢 : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    {V : C} {x : (P.p.Fiber V)ᵒᵖ} :
    𝒢.map ((eqToHom x.unop.2).op) =
      eqToHom (congrArg (fun Z : C ↦ 𝒢.obj (op Z)) x.unop.2.symm) := by
  -- This is the inverse transport normalization to the previous lemma.
  erw [eqToHom_op, eqToHom_map]

-- Proof sketch: express `p.map g.unop.1` using `IsHomLift.fac'` over `𝟙 V`, turn the two
-- equality transports into functorial transports on `𝒢`, and then cancel the inverse pair.
/-- Helper for Lemma 21.38.8: for a morphism inside one fiber, the base-map action on `𝒢`
followed by the target transport equals the source transport. -/
private theorem presheaf_map_hom_lift_id_transport
    {𝒢 : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    {V : C} {x y : (P.p.Fiber V)ᵒᵖ} (g : x ⟶ y) :
    𝒢.map (op (P.p.map g.unop.1)) ≫
      eqToHom (congrArg (fun Z : C ↦ 𝒢.obj (op Z)) y.unop.2) =
    eqToHom (congrArg (fun Z : C ↦ 𝒢.obj (op Z)) x.unop.2) := by
  letI : P.p.IsHomLift (𝟙 V) g.unop.1 := g.unop.2
  -- Rewrite the base map of the fiber morphism by the standard hom-lift formula.
  have hfac :
      P.p.map g.unop.1 =
        eqToHom y.unop.2 ≫ 𝟙 V ≫ eqToHom x.unop.2.symm := by
    simpa using (IsHomLift.fac' P.p (𝟙 V) g.unop.1)
  rw [hfac]
  calc
    𝒢.map (op (eqToHom y.unop.2 ≫ 𝟙 V ≫ eqToHom x.unop.2.symm)) ≫
        eqToHom (congrArg (fun Z : C ↦ 𝒢.obj (op Z)) y.unop.2) =
      𝒢.map ((eqToHom x.unop.2.symm).op) ≫
        𝒢.map (𝟙 (op V)) ≫
          𝒢.map ((eqToHom y.unop.2).op) ≫
            eqToHom (congrArg (fun Z : C ↦ 𝒢.obj (op Z)) y.unop.2) := by
              simp [Functor.map_comp, Category.assoc]
    _ = 𝒢.map ((eqToHom x.unop.2.symm).op) := by
      rw [presheaf_map_eqToHom_fiber_eq (𝒢 := 𝒢) (x := y)]
      simp [eqToHom_trans, Category.assoc]
    _ = eqToHom (congrArg (fun Z : C ↦ 𝒢.obj (op Z)) x.unop.2) := by
      simpa using presheaf_map_eqToHom_fiber_eq_symm (𝒢 := 𝒢) (x := x)

-- Proof sketch: normalize the base map of an arbitrary hom lift by `IsHomLift.fac'`, rewrite the
-- endpoint equality transports via the presheaf `eqToHom` formulas, and cancel the inverse pair.
/-- Helper for Lemma 21.38.8: for a hom lift over `f : V ⟶ U`, the base-map action on `𝒢`
followed by the target transport is the source transport followed by `𝒢.map (op f)`. -/
private theorem presheaf_map_hom_lift_transport
    {𝒢 : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    {U V : C} {X Y : P.S}
    (hX : P.p.obj X = V) (hY : P.p.obj Y = U)
    (f : V ⟶ U) (α : X ⟶ Y) (hα : P.p.IsHomLift f α) :
    𝒢.map (op (P.p.map α)) ≫
      eqToHom (congrArg (fun Z : C ↦ 𝒢.obj (op Z)) hX) =
    eqToHom (congrArg (fun Z : C ↦ 𝒢.obj (op Z)) hY) ≫
      𝒢.map f.op := by
  -- Normalize the base map of the hom lift and cancel the endpoint transports explicitly.
  have hfac :
      P.p.map α =
        eqToHom hX ≫ f ≫ eqToHom hY.symm := by
    simpa using (IsHomLift.fac' P.p f α)
  rw [hfac]
  let xV : (P.p.Fiber V)ᵒᵖ := op (Functor.Fiber.mk hX)
  let yU : (P.p.Fiber U)ᵒᵖ := op (Functor.Fiber.mk hY)
  calc
    𝒢.map (op (eqToHom hX ≫ f ≫ eqToHom hY.symm)) ≫
        eqToHom (congrArg (fun Z : C ↦ 𝒢.obj (op Z)) hX) =
      𝒢.map ((eqToHom hY.symm).op) ≫
        𝒢.map f.op ≫
          𝒢.map ((eqToHom hX).op) ≫
            eqToHom (congrArg (fun Z : C ↦ 𝒢.obj (op Z)) hX) := by
              simp [Functor.map_comp, Category.assoc]
    _ = 𝒢.map ((eqToHom hY.symm).op) ≫ 𝒢.map f.op := by
      rw [presheaf_map_eqToHom_fiber_eq (𝒢 := 𝒢) (x := xV)]
      simp [eqToHom_trans, Category.assoc, xV]
    _ = eqToHom (congrArg (fun Z : C ↦ 𝒢.obj (op Z)) hY) ≫ 𝒢.map f.op := by
      rw [presheaf_map_eqToHom_fiber_eq_symm (𝒢 := 𝒢) (x := yU)]

-- Proof sketch: after rewriting the two fiber objects so that they literally lie over `V`, the
-- naturality statement is the original total-site compatibility specialized to a morphism over
-- `𝟙 V`.
/-- Helper for Lemma 21.38.8: the transported fiber section is natural for morphisms inside a
single fiber. -/
private theorem fiber_section_of_compatible_family_naturality
    {ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    {𝒢 : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    (σ : ∀ X : P.S, ℱ.obj (op X) ⟶ 𝒢.obj (op (P.p.obj X)))
    (hσ : ∀ {X Y : P.S} (α : X ⟶ Y),
      ℱ.map (op α) ≫ σ X = σ Y ≫ 𝒢.map (op (P.p.map α)))
    {V : C} :
    ∀ {x y : (P.p.Fiber V)ᵒᵖ} (g : x ⟶ y),
      (fiberRestrictionPresheaf P ℱ V).map g ≫
          fiber_section_of_compatible_family P σ V y =
        fiber_section_of_compatible_family P σ V x := by
  intro x y g
  -- Expand the fiber sections and reduce to the original compatible-family naturality plus the
  -- normalized transport for a morphism inside one fiber.
  calc
    (fiberRestrictionPresheaf P ℱ V).map g ≫
        fiber_section_of_compatible_family P σ V y =
      ℱ.map (op g.unop.1) ≫ σ y.unop.1 ≫
        eqToHom (congrArg (fun Z : C ↦ 𝒢.obj (op Z)) y.unop.2) := by
          simp [fiberRestrictionPresheaf_map, fiber_section_of_compatible_family, Category.assoc]
    _ =
      σ x.unop.1 ≫ 𝒢.map (op (P.p.map g.unop.1)) ≫
        eqToHom (congrArg (fun Z : C ↦ 𝒢.obj (op Z)) y.unop.2) := by
          rw [hσ g.unop.1]
          simp [Category.assoc]
    _ =
      σ x.unop.1 ≫
        eqToHom (congrArg (fun Z : C ↦ 𝒢.obj (op Z)) x.unop.2) := by
          rw [presheaf_map_hom_lift_id_transport (P := P) (𝒢 := 𝒢) g]
          simp [Category.assoc]
    _ = fiber_section_of_compatible_family P σ V x := by
          simp [fiber_section_of_compatible_family]

-- Proof sketch: first reuse the original total-site compatible-family naturality on the hom lift,
-- then normalize the induced base-map transport by the general transport lemma above.
/-- Helper for Lemma 21.38.8: a compatible family is natural along any morphism whose image in the
base is the chosen arrow `f : V ⟶ U`. -/
private theorem fiber_section_of_compatible_family_hom_lift_naturality
    {ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    {𝒢 : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    (σ : ∀ X : P.S, ℱ.obj (op X) ⟶ 𝒢.obj (op (P.p.obj X)))
    (hσ : ∀ {X Y : P.S} (α : X ⟶ Y),
      ℱ.map (op α) ≫ σ X = σ Y ≫ 𝒢.map (op (P.p.map α)))
    {U V : C} {X Y : P.S}
    (hX : P.p.obj X = V) (hY : P.p.obj Y = U)
    (f : V ⟶ U) (α : X ⟶ Y) (hα : P.p.IsHomLift f α) :
    ℱ.map (op α) ≫
        fiber_section_of_compatible_family P σ V (op (Functor.Fiber.mk hX)) =
      fiber_section_of_compatible_family P σ U (op (Functor.Fiber.mk hY)) ≫
        𝒢.map f.op := by
  -- This is the same compatible-family identity, now followed by the general hom-lift transport
  -- normalization at the chosen endpoints.
  change
    ℱ.map (op α) ≫ σ X ≫
        eqToHom (congrArg (fun Z : C ↦ 𝒢.obj (op Z)) hX) =
      σ Y ≫ eqToHom (congrArg (fun Z : C ↦ 𝒢.obj (op Z)) hY) ≫
        𝒢.map f.op
  rw [Category.assoc, hσ α, Category.assoc,
    presheaf_map_hom_lift_transport (P := P) (𝒢 := 𝒢) hX hY f α hα]

/-- Helper for Lemma 21.38.8: a compatible total-site family produces a cocone on the restricted
diagram over each fiber. -/
private def fiber_cocone_of_compatible_family
    {ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    {𝒢 : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    (σ : ∀ X : P.S, ℱ.obj (op X) ⟶ 𝒢.obj (op (P.p.obj X)))
    (hσ : ∀ {X Y : P.S} (α : X ⟶ Y),
      ℱ.map (op α) ≫ σ X = σ Y ≫ 𝒢.map (op (P.p.map α)))
    (V : C) :
    Cocone (fiberRestrictionPresheaf P ℱ V) where
  pt := 𝒢.obj (op V)
  ι :=
    { app := fiber_section_of_compatible_family P σ V
      naturality := fun {_ _} g ↦
        fiber_section_of_compatible_family_naturality P σ hσ g }

-- Proof sketch: evaluate both descended maps on a universal colimit leg, rewrite each side by
-- `colimit.ι_desc`, and then invoke the hom-lift naturality of the compatible family for the
-- chosen strongly cartesian pullback arrow over `f.unop`.
/-- Helper for Lemma 21.38.8: on a colimit generator, the descended map attached to a pushforward
morphism is natural for base change. -/
private theorem forward_descended_map_naturality_on_ι
    [Functor.IsContinuous P.p Jₚ J]
    {ℱ : Sheaf Jₚ AddCommGrpCat.{max u v}}
    {𝒢 : Sheaf J AddCommGrpCat.{max u v}}
    (φ : ℱ ⟶ (P.p.sheafPushforwardContinuous AddCommGrpCat.{max u v} Jₚ J).obj 𝒢)
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : (P.p.Fiber (unop U))ᵒᵖ) :
    let δφ : ∀ W : C, colimit (fiberRestrictionPresheaf P ℱ.1 W) ⟶ 𝒢.1.obj (op W) :=
      fun W ↦
        colimit.desc (fiberRestrictionPresheaf P ℱ.1 W)
          (fiber_cocone_of_compatible_family P
            (pushforwardCompatibleFamilyApp P J φ)
            (pushforwardCompatibleFamily_naturality P J φ)
            W);
      colimit.ι (fiberRestrictionPresheaf P ℱ.1 (unop U)) x ≫
          fiberwiseColimitPresheafMap P ℱ.1 f ≫ δφ (unop V) =
        colimit.ι (fiberRestrictionPresheaf P ℱ.1 (unop U)) x ≫
          δφ (unop U) ≫ 𝒢.1.map f := by
  let hc := canonicalPullbackChoice P.p
  let δφ : ∀ W : C, colimit (fiberRestrictionPresheaf P ℱ.1 W) ⟶ 𝒢.1.obj (op W) :=
    fun W ↦
      colimit.desc (fiberRestrictionPresheaf P ℱ.1 W)
        (fiber_cocone_of_compatible_family P
          (pushforwardCompatibleFamilyApp P J φ)
          (pushforwardCompatibleFamily_naturality P J φ)
          W)
  let α : ((hc.pullbackFunctor f.unop).obj x.unop).1 ⟶ x.unop.1 := hc.map f.unop x.unop
  letI : P.p.IsHomLift f.unop α := hc.isStronglyCartesian f.unop x.unop
  -- Read both descended maps on the relevant colimit generators and reduce to the previously
  -- normalized hom-lift naturality for the compatible family coming from `φ`.
  calc
    colimit.ι (fiberRestrictionPresheaf P ℱ.1 (unop U)) x ≫
        fiberwiseColimitPresheafMap P ℱ.1 f ≫ δφ (unop V) =
      ℱ.1.map (op α) ≫
        fiber_section_of_compatible_family P
          (pushforwardCompatibleFamilyApp P J φ)
          (unop V) (((hc.pullbackFunctor f.unop).op.obj x)) := by
            dsimp [δφ, α]
            rw [Category.assoc]
            simpa [fiberwiseColimitPresheafMap, fiberwiseColimitRestrictionCoconeApp,
              fiberRestrictionComparisonApp, fiber_cocone_of_compatible_family] using
              congrArg
                (fun k ↦ k ≫
                  colimit.desc (fiberRestrictionPresheaf P ℱ.1 (unop V))
                    (fiber_cocone_of_compatible_family P
                      (pushforwardCompatibleFamilyApp P J φ)
                      (pushforwardCompatibleFamily_naturality P J φ)
                      (unop V)))
                (colimit.ι_desc (fiberwiseColimitRestrictionCocone P ℱ.1 f.unop) x)
    _ =
      fiber_section_of_compatible_family P
          (pushforwardCompatibleFamilyApp P J φ)
          (unop U) x ≫
        𝒢.1.map f := by
            simpa [α] using
              (fiber_section_of_compatible_family_hom_lift_naturality
                (P := P) (𝒢 := 𝒢.1)
                (σ := pushforwardCompatibleFamilyApp P J φ)
                (hσ := pushforwardCompatibleFamily_naturality P J φ)
                x.unop.2 (((hc.pullbackFunctor f.unop).obj x.unop).2)
                f.unop α inferInstance)
    _ =
      colimit.ι (fiberRestrictionPresheaf P ℱ.1 (unop U)) x ≫
        δφ (unop U) ≫ 𝒢.1.map f := by
            dsimp [δφ]
            rw [Category.assoc]
            rfl

-- Proof sketch: once the descended maps agree on the universal colimit generators, `colimit.hom_ext`
-- upgrades the equality to the full naturality equation for the forward map.
/-- Helper for Lemma 21.38.8: the descended map from a pushforward morphism is a presheaf
morphism out of the fiberwise-colimit presheaf. -/
private theorem forward_descended_map_naturality
    [Functor.IsContinuous P.p Jₚ J]
    {ℱ : Sheaf Jₚ AddCommGrpCat.{max u v}}
    {𝒢 : Sheaf J AddCommGrpCat.{max u v}}
    (φ : ℱ ⟶ (P.p.sheafPushforwardContinuous AddCommGrpCat.{max u v} Jₚ J).obj 𝒢)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    let δφ : ∀ W : C, colimit (fiberRestrictionPresheaf P ℱ.1 W) ⟶ 𝒢.1.obj (op W) :=
      fun W ↦
        colimit.desc (fiberRestrictionPresheaf P ℱ.1 W)
          (fiber_cocone_of_compatible_family P
            (pushforwardCompatibleFamilyApp P J φ)
            (pushforwardCompatibleFamily_naturality P J φ)
            W);
      fiberwiseColimitPresheafMap P ℱ.1 f ≫ δφ (unop V) =
        δφ (unop U) ≫ 𝒢.1.map f := by
  -- The generator-level descent naturality already determines the global morphism equality.
  apply colimit.hom_ext
  intro x
  simpa [Category.assoc] using
    (forward_descended_map_naturality_on_ι (P := P) (J := J) (φ := φ) f x)

/-- Helper for Lemma 21.38.8: the canonical object of the fiber over `P.p.obj X`
represented by `X` itself. -/
private def backward_family_fiber_obj (X : P.S) :
    P.p.Fiber (P.p.obj X) :=
  Functor.Fiber.mk rfl

/-- Helper for Lemma 21.38.8: every total-site morphism is a hom lift over its own image in the
base. -/
private theorem backward_family_self_hom_lift
    {X Y : P.S} (α : X ⟶ Y) :
    P.p.IsHomLift (P.p.map α) α := by
  -- A morphism is tautologically a lift of its own image in the base.
  simpa using (show P.p.IsHomLift (P.p.map α) α from inferInstance)

/-- Helper for Lemma 21.38.8: the canonical morphism from `X` into the chosen pullback of `Y`
along `P.p.map α`, viewed inside the fiber over `P.p.obj X`. -/
private noncomputable def backward_family_pullback_hom
    {X Y : P.S} (α : X ⟶ Y) :
    backward_family_fiber_obj P X ⟶
      ((canonicalPullbackChoice P.p).pullbackFunctor (P.p.map α)).obj
        (backward_family_fiber_obj P Y) := by
  let hc := canonicalPullbackChoice P.p
  let y := backward_family_fiber_obj P Y
  let φ : (hc.obj (P.p.map α) y).1 ⟶ y.1 := hc.map (P.p.map α) y
  let hsc : P.p.IsStronglyCartesian (P.p.map α) φ := hc.isStronglyCartesian (P.p.map α) y
  let hα : P.p.IsHomLift ((𝟙 (P.p.obj X)) ≫ P.p.map α) α := by
    simpa using (backward_family_self_hom_lift P α : P.p.IsHomLift (P.p.map α) α)
  exact Functor.Fiber.homMk P.p (P.p.obj X)
    (@Functor.IsStronglyCartesian.map _ _ _ _ P.p _ _ _ _
      (P.p.map α) φ hsc _ _ (𝟙 (P.p.obj X))
      ((𝟙 (P.p.obj X)) ≫ P.p.map α) rfl α hα)

/-- Helper for Lemma 21.38.8: the canonical backward pullback morphism factors the chosen
strongly cartesian arrow through `α`. -/
private theorem backward_family_pullback_hom_fac
    {X Y : P.S} (α : X ⟶ Y) :
    (backward_family_pullback_hom P α).1 ≫
        (canonicalPullbackChoice P.p).map
          (P.p.map α) (backward_family_fiber_obj P Y) =
      α := by
  let hc := canonicalPullbackChoice P.p
  let y := backward_family_fiber_obj P Y
  let φ : (hc.obj (P.p.map α) y).1 ⟶ y.1 := hc.map (P.p.map α) y
  let hsc : P.p.IsStronglyCartesian (P.p.map α) φ := hc.isStronglyCartesian (P.p.map α) y
  let hα : P.p.IsHomLift ((𝟙 (P.p.obj X)) ≫ P.p.map α) α := by
    simpa using (backward_family_self_hom_lift P α : P.p.IsHomLift (P.p.map α) α)
  -- Unfold the chosen comparison morphism so that the strong-cartesianness factorization applies
  -- directly to the underlying arrow.
  change
    (@Functor.IsStronglyCartesian.map _ _ _ _ P.p _ _ _ _
        (P.p.map α) φ hsc _ _ (𝟙 (P.p.obj X))
        ((𝟙 (P.p.obj X)) ≫ P.p.map α) rfl α hα) ≫
      hc.map (P.p.map α) y =
        α
  simpa [φ, y] using
    (Functor.IsStronglyCartesian.fac P.p (P.p.map α) φ rfl α)

/-- Helper for Lemma 21.38.8: the restriction map on the fiberwise-colimit presheaf sends the
canonical generator of `Y` to the image of the canonical generator of `X` under `ℱ.map (op α)`. -/
private theorem backward_family_generator_map
    {ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    {X Y : P.S} (α : X ⟶ Y) :
    colimit.ι (fiberRestrictionPresheaf P ℱ (P.p.obj Y))
        (op (backward_family_fiber_obj P Y)) ≫
      fiberwiseColimitPresheafMap P ℱ (op (P.p.map α)) =
    ℱ.map (op α) ≫
      colimit.ι (fiberRestrictionPresheaf P ℱ (P.p.obj X))
        (op (backward_family_fiber_obj P X)) := by
  let hc := canonicalPullbackChoice P.p
  calc
    colimit.ι (fiberRestrictionPresheaf P ℱ (P.p.obj Y))
        (op (backward_family_fiber_obj P Y)) ≫
        fiberwiseColimitPresheafMap P ℱ (op (P.p.map α)) =
      ℱ.map (op (hc.map (P.p.map α) (backward_family_fiber_obj P Y))) ≫
        colimit.ι (fiberRestrictionPresheaf P ℱ (P.p.obj X))
          (((hc.pullbackFunctor (P.p.map α)).op.obj
            (op (backward_family_fiber_obj P Y)))) := by
            -- Evaluate the restriction map on the canonical generator of `Y`.
            simpa [backward_family_fiber_obj] using
              (fiberwiseColimitPresheaf_ι_map (P := P) (ℱ := ℱ)
                (f := op (P.p.map α)) (x := op (backward_family_fiber_obj P Y)))
    _ =
      ℱ.map (op (hc.map (P.p.map α) (backward_family_fiber_obj P Y))) ≫
        ℱ.map (op ((backward_family_pullback_hom P α).1)) ≫
          colimit.ι (fiberRestrictionPresheaf P ℱ (P.p.obj X))
            (op (backward_family_fiber_obj P X)) := by
              -- Move from the chosen pullback object to the canonical fiber object `X`.
              rw [← Category.assoc]
              simpa [backward_family_fiber_obj, fiberRestrictionPresheaf_map, Category.assoc] using
                congrArg
                  (fun k ↦ ℱ.map (op (hc.map (P.p.map α) (backward_family_fiber_obj P Y))) ≫ k)
                  (colimit.w (fiberRestrictionPresheaf P ℱ (P.p.obj X))
                    (op (backward_family_pullback_hom P α))).symm
    _ =
      ℱ.map (op α) ≫
        colimit.ι (fiberRestrictionPresheaf P ℱ (P.p.obj X))
          (op (backward_family_fiber_obj P X)) := by
            -- The two pullback arrows compose to `α`, so the corresponding restriction maps do too.
            rw [← Category.assoc, ← Functor.map_comp]
            simpa [backward_family_fiber_obj] using
              congrArg
                (fun k ↦
                  ℱ.map (op k) ≫
                    colimit.ι (fiberRestrictionPresheaf P ℱ (P.p.obj X))
                      (op (backward_family_fiber_obj P X)))
                (backward_family_pullback_hom_fac P α)

/-- Helper for Lemma 21.38.8: evaluate a map out of the fiberwise-colimit presheaf on the
canonical generator `Functor.Fiber.mk rfl` to recover the source-proof compatible family. -/
private def backward_family_of_descended_map
    {ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    {𝒢 : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    (η : fiberwiseColimitPresheaf P ℱ ⟶ 𝒢)
    (X : P.S) :
    ℱ.obj (op X) ⟶ 𝒢.obj (op (P.p.obj X)) :=
  colimit.ι (fiberRestrictionPresheaf P ℱ (P.p.obj X))
      (op (backward_family_fiber_obj P X)) ≫
    η.app (op (P.p.obj X))

/-- Helper for Lemma 21.38.8: the family recovered from a descended map is natural under
restriction in the total category, by factoring through the chosen strongly cartesian pullback. -/
private theorem backward_family_naturality_via_strongly_cartesian_factorization
    {ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    {𝒢 : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    (η : fiberwiseColimitPresheaf P ℱ ⟶ 𝒢)
    {X Y : P.S} (α : X ⟶ Y) :
    ℱ.map (op α) ≫ backward_family_of_descended_map P η X =
      backward_family_of_descended_map P η Y ≫
        𝒢.map (op (P.p.map α)) := by
  -- Rewrite the canonical generator of `Y` through the chosen strongly cartesian factorization,
  -- then apply naturality of the descended map `η`.
  dsimp [backward_family_of_descended_map]
  calc
    ℱ.map (op α) ≫
        colimit.ι (fiberRestrictionPresheaf P ℱ (P.p.obj X))
          (op (backward_family_fiber_obj P X)) ≫
          η.app (op (P.p.obj X)) =
      colimit.ι (fiberRestrictionPresheaf P ℱ (P.p.obj Y))
          (op (backward_family_fiber_obj P Y)) ≫
          fiberwiseColimitPresheafMap P ℱ (op (P.p.map α)) ≫
            η.app (op (P.p.obj X)) := by
              rw [backward_family_generator_map (P := P) (ℱ := ℱ) α]
    _ =
      colimit.ι (fiberRestrictionPresheaf P ℱ (P.p.obj Y))
          (op (backward_family_fiber_obj P Y)) ≫
          η.app (op (P.p.obj Y)) ≫
            𝒢.map (op (P.p.map α)) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦
                    colimit.ι (fiberRestrictionPresheaf P ℱ (P.p.obj Y))
                      (op (backward_family_fiber_obj P Y)) ≫ k)
                  (η.naturality (op (P.p.map α)))

/-- Helper for Lemma 21.38.8: package the descended cocone maps of a pushforward morphism into a
presheaf morphism from the fiberwise-colimit presheaf. -/
private noncomputable def forwardDescendedMap
    [Functor.IsContinuous P.p Jₚ J]
    {ℱ : Sheaf Jₚ AddCommGrpCat.{max u v}}
    {𝒢 : Sheaf J AddCommGrpCat.{max u v}}
    (φ : ℱ ⟶ (P.p.sheafPushforwardContinuous AddCommGrpCat.{max u v} Jₚ J).obj 𝒢) :
    fiberwiseColimitPresheaf P ℱ.1 ⟶ 𝒢.1 where
  app U :=
    colimit.desc (fiberRestrictionPresheaf P ℱ.1 (unop U))
      (fiber_cocone_of_compatible_family P
        (pushforwardCompatibleFamilyApp P J φ)
        (pushforwardCompatibleFamily_naturality P J φ)
        (unop U))
  naturality := by
    intro U V f
    -- The generator-level descent compatibility has already been upgraded to presheaf naturality.
    simpa using forward_descended_map_naturality (P := P) (J := J) (φ := φ) f

/-- Helper for Lemma 21.38.8: postcomposing a descended map with a sheaf morphism postcomposes the
recovered compatible family on total-site objects. -/
private theorem backward_family_of_descended_map_comp
    {ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    {𝒢 𝒢' : Sheaf J AddCommGrpCat.{max u v}}
    (η : fiberwiseColimitPresheaf P ℱ ⟶ 𝒢.1) (α : 𝒢 ⟶ 𝒢')
    (X : P.S) :
    backward_family_of_descended_map P (η ≫ α.1) X =
      backward_family_of_descended_map P η X ≫ α.1.app (op (P.p.obj X)) := by
  -- Expand the recovered family and regroup the postcomposition with `α`.
  simp [backward_family_of_descended_map, Category.assoc]

/-- Helper for Lemma 21.38.8: the fiber section attached to the recovered compatible family is
exactly the original value of the descended map on that fiber generator. -/
private theorem backward_family_fiber_section
    {ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    {𝒢 : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    (η : fiberwiseColimitPresheaf P ℱ ⟶ 𝒢)
    {V : C} (x : (P.p.Fiber V)ᵒᵖ) :
    fiber_section_of_compatible_family P (backward_family_of_descended_map P η) V x =
      colimit.ι (fiberRestrictionPresheaf P ℱ V) x ≫ η.app (op V) := by
  -- Route correction: after unpacking the opposite fiber object and its base equality, this is
  -- literally the defining canonical generator followed by `η`.
  cases x using Opposite.rec
  rename_i x
  cases x with
  | mk X hX =>
      cases hX
      rfl

/-- Helper for Lemma 21.38.8: the recovered compatible family defines a morphism into the
continuous pushforward sheaf. -/
private theorem backwardPushforwardMap_naturality
    [Functor.IsContinuous P.p Jₚ J]
    {ℱ : Sheaf Jₚ AddCommGrpCat.{max u v}}
    {𝒢 : Sheaf J AddCommGrpCat.{max u v}}
    (η : fiberwiseColimitPresheaf P ℱ.1 ⟶ 𝒢.1)
    {X Y : P.Sᵒᵖ} (α : X ⟶ Y) :
    ℱ.1.map α ≫
        (backward_family_of_descended_map P η Y.unop ≫
          (pushforwardUnderlyingPresheafIso P J 𝒢).inv.app Y) =
      (backward_family_of_descended_map P η X.unop ≫
          (pushforwardUnderlyingPresheafIso P J 𝒢).inv.app X) ≫
        (((P.p.sheafPushforwardContinuous AddCommGrpCat.{max u v} Jₚ J).obj 𝒢).1.map α) := by
  -- First use the recovered compatible-family naturality, then rewrite the pushforward transport
  -- through the canonical comparison isomorphism on underlying presheaves.
  calc
    ℱ.1.map α ≫
        (backward_family_of_descended_map P η Y.unop ≫
          (pushforwardUnderlyingPresheafIso P J 𝒢).inv.app Y) =
      (ℱ.1.map α ≫ backward_family_of_descended_map P η Y.unop) ≫
        (pushforwardUnderlyingPresheafIso P J 𝒢).inv.app Y := by
          simp [Category.assoc]
    _ =
      (backward_family_of_descended_map P η X.unop ≫
          𝒢.1.map (op (P.p.map α.unop))) ≫
        (pushforwardUnderlyingPresheafIso P J 𝒢).inv.app Y := by
          rw [backward_family_naturality_via_strongly_cartesian_factorization
            (P := P) (η := η) α.unop]
    _ =
      backward_family_of_descended_map P η X.unop ≫
        (𝒢.1.map (op (P.p.map α.unop)) ≫
          (pushforwardUnderlyingPresheafIso P J 𝒢).inv.app Y) := by
          simp [Category.assoc]
    _ =
      backward_family_of_descended_map P η X.unop ≫
        ((pushforwardUnderlyingPresheafIso P J 𝒢).inv.app X ≫
          (((P.p.sheafPushforwardContinuous AddCommGrpCat.{max u v} Jₚ J).obj 𝒢).1.map α)) := by
          simpa [pushforwardUnderlyingPresheafIso, Category.assoc] using
            congrArg
              (fun k ↦ backward_family_of_descended_map P η X.unop ≫ k)
              ((pushforwardUnderlyingPresheafIso P J 𝒢).inv.naturality α)
    _ =
      (backward_family_of_descended_map P η X.unop ≫
          (pushforwardUnderlyingPresheafIso P J 𝒢).inv.app X) ≫
        (((P.p.sheafPushforwardContinuous AddCommGrpCat.{max u v} Jₚ J).obj 𝒢).1.map α) := by
          simp [Category.assoc]

/-- Helper for Lemma 21.38.8: the recovered compatible family yields a sheaf morphism into the
continuous pushforward sheaf. -/
private noncomputable def backwardPushforwardMap
    [Functor.IsContinuous P.p Jₚ J]
    {ℱ : Sheaf Jₚ AddCommGrpCat.{max u v}}
    {𝒢 : Sheaf J AddCommGrpCat.{max u v}}
    (η : fiberwiseColimitPresheaf P ℱ.1 ⟶ 𝒢.1) :
    ℱ ⟶ (P.p.sheafPushforwardContinuous AddCommGrpCat.{max u v} Jₚ J).obj 𝒢 :=
  ObjectProperty.homMk <|
    { app := fun X ↦
        backward_family_of_descended_map P η X.unop ≫
          (pushforwardUnderlyingPresheafIso P J 𝒢).inv.app X
      naturality := fun {_ _} α ↦ backwardPushforwardMap_naturality (P := P) (J := J) η α }

/-- Helper for Lemma 21.38.8: the compatible family extracted from `backwardPushforwardMap`
recovers the original descended-family values. -/
private theorem pushforwardCompatibleFamily_backwardPushforwardMap
    [Functor.IsContinuous P.p Jₚ J]
    {ℱ : Sheaf Jₚ AddCommGrpCat.{max u v}}
    {𝒢 : Sheaf J AddCommGrpCat.{max u v}}
    (η : fiberwiseColimitPresheaf P ℱ.1 ⟶ 𝒢.1)
    (X : P.S) :
    pushforwardCompatibleFamilyApp P J (backwardPushforwardMap (P := P) (J := J) η) X =
      backward_family_of_descended_map P η X := by
  -- The comparison isomorphism cancels the inverse component used in the sheaf-level lift.
  simp [pushforwardCompatibleFamilyApp, backwardPushforwardMap, Category.assoc]

/-- Helper for Lemma 21.38.8: evaluating the forward descended map on the canonical fiber object
recovers the original compatible family from the pushforward morphism. -/
private theorem backward_family_of_forwardDescendedMap
    [Functor.IsContinuous P.p Jₚ J]
    {ℱ : Sheaf Jₚ AddCommGrpCat.{max u v}}
    {𝒢 : Sheaf J AddCommGrpCat.{max u v}}
    (φ : ℱ ⟶ (P.p.sheafPushforwardContinuous AddCommGrpCat.{max u v} Jₚ J).obj 𝒢)
    (X : P.S) :
    backward_family_of_descended_map P (forwardDescendedMap (P := P) (J := J) φ) X =
      pushforwardCompatibleFamilyApp P J φ X := by
  -- Evaluate the colimit descent map on the canonical generator `Functor.Fiber.mk rfl`.
  dsimp [backward_family_of_descended_map, forwardDescendedMap, backward_family_fiber_obj]
  simpa [fiber_cocone_of_compatible_family, fiber_section_of_compatible_family] using
    (colimit.ι_desc
      (fiber_cocone_of_compatible_family P
        (pushforwardCompatibleFamilyApp P J φ)
        (pushforwardCompatibleFamily_naturality P J φ)
        (P.p.obj X))
      (op (backward_family_fiber_obj P X)))

/-- Helper for Lemma 21.38.8: descending the compatible family recovered from a presheaf morphism
returns the original presheaf morphism. -/
private theorem forwardDescendedMap_of_backwardPushforwardMap
    [Functor.IsContinuous P.p Jₚ J]
    {ℱ : Sheaf Jₚ AddCommGrpCat.{max u v}}
    {𝒢 : Sheaf J AddCommGrpCat.{max u v}}
    (η : fiberwiseColimitPresheaf P ℱ.1 ⟶ 𝒢.1) :
    forwardDescendedMap (P := P) (J := J)
        (backwardPushforwardMap (P := P) (J := J) η) =
      η := by
  -- Compare both presheaf morphisms on the universal colimit generators over each fiber.
  ext V
  apply colimit.hom_ext
  intro x
  calc
    colimit.ι (fiberRestrictionPresheaf P ℱ.1 (unop V)) x ≫
        (forwardDescendedMap (P := P) (J := J)
          (backwardPushforwardMap (P := P) (J := J) η)).app V =
      fiber_section_of_compatible_family P
          (pushforwardCompatibleFamilyApp P J
            (backwardPushforwardMap (P := P) (J := J) η))
          (unop V) x := by
            simpa [forwardDescendedMap, fiber_cocone_of_compatible_family] using
              (colimit.ι_desc
                (fiber_cocone_of_compatible_family P
                  (pushforwardCompatibleFamilyApp P J
                    (backwardPushforwardMap (P := P) (J := J) η))
                  (pushforwardCompatibleFamily_naturality P J
                    (backwardPushforwardMap (P := P) (J := J) η))
                  (unop V))
                x)
    _ =
      fiber_section_of_compatible_family P
        (backward_family_of_descended_map P η) (unop V) x := by
          rw [pushforwardCompatibleFamily_backwardPushforwardMap
            (P := P) (J := J) (η := η) x.unop.1]
    _ =
      colimit.ι (fiberRestrictionPresheaf P ℱ.1 (unop V)) x ≫ η.app V := by
          simpa using backward_family_fiber_section (P := P) (η := η) x

/-- Helper for Lemma 21.38.8: recovering the compatible family from the forward descended map
returns the original sheaf morphism into the pushforward. -/
private theorem backwardPushforwardMap_of_forwardDescendedMap
    [Functor.IsContinuous P.p Jₚ J]
    {ℱ : Sheaf Jₚ AddCommGrpCat.{max u v}}
    {𝒢 : Sheaf J AddCommGrpCat.{max u v}}
    (φ : ℱ ⟶ (P.p.sheafPushforwardContinuous AddCommGrpCat.{max u v} Jₚ J).obj 𝒢) :
    backwardPushforwardMap (P := P) (J := J)
        (forwardDescendedMap (P := P) (J := J) φ) =
      φ := by
  -- Postcompose with the comparison isomorphism on underlying presheaves to reduce to the
  -- canonical-family equality on total-site objects.
  ext X
  apply (cancel_mono ((pushforwardUnderlyingPresheafIso P J 𝒢).hom.app X)).1
  calc
    (backwardPushforwardMap (P := P) (J := J)
        (forwardDescendedMap (P := P) (J := J) φ)).1.app X ≫
          (pushforwardUnderlyingPresheafIso P J 𝒢).hom.app X =
      backward_family_of_descended_map P
        (forwardDescendedMap (P := P) (J := J) φ) X.unop := by
          simpa [pushforwardCompatibleFamilyApp, Category.assoc] using
            pushforwardCompatibleFamily_backwardPushforwardMap
              (P := P) (J := J)
              (η := forwardDescendedMap (P := P) (J := J) φ) X.unop
    _ =
      pushforwardCompatibleFamilyApp P J φ X.unop := by
          simpa using backward_family_of_forwardDescendedMap
            (P := P) (J := J) (φ := φ) X.unop
    _ = φ.1.app X ≫ (pushforwardUnderlyingPresheafIso P J 𝒢).hom.app X := by
          rfl

/-- Helper for Lemma 21.38.8: the presheaf-level Hom-equivalence from the source proof. -/
private noncomputable def fiberwiseColimitPresheafHomEquiv
    [Functor.IsContinuous P.p Jₚ J]
    (ℱ : Sheaf Jₚ AddCommGrpCat.{max u v})
    (𝒢 : Sheaf J AddCommGrpCat.{max u v}) :
    (fiberwiseColimitPresheaf P ℱ.1 ⟶ 𝒢.1) ≃
      (ℱ ⟶ (P.p.sheafPushforwardContinuous AddCommGrpCat.{max u v} Jₚ J).obj 𝒢) where
  toFun := backwardPushforwardMap (P := P) (J := J)
  invFun := forwardDescendedMap (P := P) (J := J)
  left_inv := forwardDescendedMap_of_backwardPushforwardMap (P := P) (J := J)
  right_inv := backwardPushforwardMap_of_forwardDescendedMap (P := P) (J := J)

/-- Helper for Lemma 21.38.8: postcomposition on the target sheaf matches postcomposition under
the presheaf-level Hom-equivalence. -/
private theorem fiberwiseColimitPresheafHomEquiv_naturality_right
    [Functor.IsContinuous P.p Jₚ J]
    {ℱ : Sheaf Jₚ AddCommGrpCat.{max u v}}
    {𝒢 𝒢' : Sheaf J AddCommGrpCat.{max u v}}
    (η : fiberwiseColimitPresheaf P ℱ.1 ⟶ 𝒢.1) (α : 𝒢 ⟶ 𝒢') :
    fiberwiseColimitPresheafHomEquiv (P := P) (J := J) ℱ 𝒢' (η ≫ α.1) =
      fiberwiseColimitPresheafHomEquiv (P := P) (J := J) ℱ 𝒢 η ≫
        (P.p.sheafPushforwardContinuous AddCommGrpCat.{max u v} Jₚ J).map α := by
  -- Compare the two sheaf morphisms after extracting their compatible families on total-site
  -- objects.
  ext X
  apply (cancel_mono ((pushforwardUnderlyingPresheafIso P J 𝒢').hom.app X)).1
  calc
    (fiberwiseColimitPresheafHomEquiv (P := P) (J := J) ℱ 𝒢' (η ≫ α.1)).1.app X ≫
        (pushforwardUnderlyingPresheafIso P J 𝒢').hom.app X =
      backward_family_of_descended_map P (η ≫ α.1) X.unop := by
          simpa [fiberwiseColimitPresheafHomEquiv, pushforwardCompatibleFamilyApp, Category.assoc]
            using
              pushforwardCompatibleFamily_backwardPushforwardMap
                (P := P) (J := J) (η := η ≫ α.1) X.unop
    _ =
      backward_family_of_descended_map P η X.unop ≫
        α.1.app (op (P.p.obj X.unop)) := by
          simpa using backward_family_of_descended_map_comp
            (P := P) (η := η) α X.unop
    _ =
      pushforwardCompatibleFamilyApp P J
          (fiberwiseColimitPresheafHomEquiv (P := P) (J := J) ℱ 𝒢 η)
          X.unop ≫ α.1.app (op (P.p.obj X.unop)) := by
            rw [pushforwardCompatibleFamily_backwardPushforwardMap
              (P := P) (J := J) (η := η) X.unop]
    _ =
      ((fiberwiseColimitPresheafHomEquiv (P := P) (J := J) ℱ 𝒢 η ≫
          (P.p.sheafPushforwardContinuous AddCommGrpCat.{max u v} Jₚ J).map α).1.app X) ≫
        (pushforwardUnderlyingPresheafIso P J 𝒢').hom.app X := by
          -- Rewrite the postcomposition on pushforwards through the comparison isomorphism.
          dsimp [pushforwardCompatibleFamilyApp]
          rw [Category.assoc]
          simpa [pushforwardUnderlyingPresheafIso, Category.assoc] using
            congrArg
              (fun k ↦
                (fiberwiseColimitPresheafHomEquiv (P := P) (J := J) ℱ 𝒢 η).1.app X ≫ k)
              (((P.p.sheafPushforwardContinuousCompSheafToPresheafIso
                  AddCommGrpCat.{max u v} Jₚ J).hom.naturality α).app X)

/-- Helper for Lemma 21.38.8: the sheafification of the fiberwise-colimit presheaf represents the
same Hom functor into continuous pushforward sheaves. -/
private noncomputable def fiberwiseColimitSheafHomEquiv
    [Functor.IsContinuous P.p Jₚ J]
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    (ℱ : Sheaf Jₚ AddCommGrpCat.{max u v})
    (𝒢 : Sheaf J AddCommGrpCat.{max u v}) :
    (fiberwiseColimitSheafOfSheaf P J ℱ ⟶ 𝒢) ≃
      (ℱ ⟶ (P.p.sheafPushforwardContinuous AddCommGrpCat.{max u v} Jₚ J).obj 𝒢) :=
  ((sheafificationAdjunction J AddCommGrpCat.{max u v}).homEquiv
      (fiberwiseColimitPresheaf P ℱ.1) 𝒢).trans
    (fiberwiseColimitPresheafHomEquiv (P := P) (J := J) ℱ 𝒢)

/-- Helper for Lemma 21.38.8: postcomposition on target sheaves matches postcomposition under the
sheafified Hom-equivalence used in the final Yoneda comparison. -/
private theorem fiberwiseColimitSheafHomEquiv_naturality_right
    [Functor.IsContinuous P.p Jₚ J]
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    {ℱ : Sheaf Jₚ AddCommGrpCat.{max u v}}
    {𝒢 𝒢' : Sheaf J AddCommGrpCat.{max u v}}
    (β : fiberwiseColimitSheafOfSheaf P J ℱ ⟶ 𝒢) (α : 𝒢 ⟶ 𝒢') :
    fiberwiseColimitSheafHomEquiv (P := P) (J := J) ℱ 𝒢' (β ≫ α) =
      fiberwiseColimitSheafHomEquiv (P := P) (J := J) ℱ 𝒢 β ≫
        (P.p.sheafPushforwardContinuous AddCommGrpCat.{max u v} Jₚ J).map α := by
  -- Combine sheafification naturality on the right with the presheaf-level Hom-equivalence
  -- naturality already established above.
  dsimp [fiberwiseColimitSheafHomEquiv]
  rw [Equiv.trans_apply, Equiv.trans_apply]
  rw [(sheafificationAdjunction J AddCommGrpCat.{max u v}).homEquiv_naturality_right β α]
  simpa using
    fiberwiseColimitPresheafHomEquiv_naturality_right
      (P := P) (J := J)
      ((sheafificationAdjunction J AddCommGrpCat.{max u v}).homEquiv
        (fiberwiseColimitPresheaf P ℱ.1) 𝒢 β) α

/-- Helper for Lemma 21.38.8: compare the sheafified fiberwise-colimit Hom functor with the
canonical lower-shriek Hom functor through the two right-adjoint descriptions. -/
private noncomputable def lowerShriekComparisonHomEquiv
    [Functor.IsContinuous P.p Jₚ J]
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [((P.p.sheafPushforwardContinuous AddCommGrpCat.{max u v} Jₚ J).IsRightAdjoint)]
    (ℱ : Sheaf Jₚ AddCommGrpCat.{max u v})
    (𝒢 : Sheaf J AddCommGrpCat.{max u v}) :
    (fiberwiseColimitSheafOfSheaf P J ℱ ⟶ 𝒢) ≃
      (((P.p.sheafPullback AddCommGrpCat.{max u v} Jₚ J).obj ℱ) ⟶ 𝒢) :=
  (fiberwiseColimitSheafHomEquiv (P := P) (J := J) ℱ 𝒢).trans
    (((P.p.sheafAdjunctionContinuous AddCommGrpCat.{max u v} Jₚ J).homEquiv ℱ 𝒢).symm)

/-- Helper for Lemma 21.38.8: the final comparison Hom-equivalence is natural in the target
sheaf, which is the only Yoneda-style compatibility needed for the objectwise isomorphism. -/
private theorem lowerShriekComparisonHomEquiv_naturality_right
    [Functor.IsContinuous P.p Jₚ J]
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [((P.p.sheafPushforwardContinuous AddCommGrpCat.{max u v} Jₚ J).IsRightAdjoint)]
    {ℱ : Sheaf Jₚ AddCommGrpCat.{max u v}}
    {𝒢 𝒢' : Sheaf J AddCommGrpCat.{max u v}}
    (β : fiberwiseColimitSheafOfSheaf P J ℱ ⟶ 𝒢) (α : 𝒢 ⟶ 𝒢') :
    lowerShriekComparisonHomEquiv (P := P) (J := J) ℱ 𝒢' (β ≫ α) =
      lowerShriekComparisonHomEquiv (P := P) (J := J) ℱ 𝒢 β ≫ α := by
  -- Apply right naturality first on the sheafified Hom-equivalence and then on the canonical
  -- pullback/pushforward adjunction.
  dsimp [lowerShriekComparisonHomEquiv]
  rw [Equiv.trans_apply, Equiv.trans_apply]
  rw [fiberwiseColimitSheafHomEquiv_naturality_right (P := P) (J := J)]
  simpa using
    (P.p.sheafAdjunctionContinuous AddCommGrpCat.{max u v} Jₚ J).homEquiv_naturality_right_symm
      ((fiberwiseColimitSheafHomEquiv (P := P) (J := J) ℱ 𝒢) β) α

-- Proof sketch: compare morphisms from the sheafification of the fiberwise-colimit presheaf into
-- any abelian sheaf on `J` with compatible families of morphisms from `ℱ` on the fibers, and then
-- identify those with morphisms from `ℱ` into the inverse image along `π`.
/-- Lemma 21.38.8: for an abelian sheaf `ℱ` on the total site of a fibred category `P` over the
base site `J`, the lower shriek `π_! ℱ` is the sheaf associated to the presheaf sending an
object `V` of the base to the colimit of the restriction of `ℱ` over the opposite of the fiber
category `P.p.Fiber V`. -/
@[stacks 08PE]
theorem lowerShriek_is_sheafification_of_fiberwiseColimitPresheaf
    [Functor.IsContinuous P.p Jₚ J]
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [((P.p.sheafPushforwardContinuous AddCommGrpCat.{max u v} Jₚ J).IsRightAdjoint)]
    (ℱ : Sheaf Jₚ AddCommGrpCat.{max u v}) :
    IsIsomorphic
      ((P.p.sheafPullback AddCommGrpCat.{max u v} Jₚ J).obj ℱ)
      (fiberwiseColimitSheafOfSheaf P J ℱ) := by
  let A : Sheaf J AddCommGrpCat.{max u v} := fiberwiseColimitSheafOfSheaf P J ℱ
  let B : Sheaf J AddCommGrpCat.{max u v} :=
    (P.p.sheafPullback AddCommGrpCat.{max u v} Jₚ J).obj ℱ
  let e :
      ∀ 𝒢 : Sheaf J AddCommGrpCat.{max u v}, (A ⟶ 𝒢) ≃ (B ⟶ 𝒢) :=
    lowerShriekComparisonHomEquiv (P := P) (J := J) ℱ
  let g : B ⟶ A := (e A) (𝟙 A)
  let f : A ⟶ B := (e B).symm (𝟙 B)
  have hgf : g ≫ f = 𝟙 B := by
    -- Evaluate right naturality at `𝟙 A` and the comparison map `f`.
    simpa [A, B, e, g, f] using
      (lowerShriekComparisonHomEquiv_naturality_right
        (P := P) (J := J) (ℱ := ℱ) (β := 𝟙 A) (α := f)).symm
  have hfg : f ≫ g = 𝟙 A := by
    -- Compare both arrows under the representing equivalence at `A`.
    apply (e A).injective
    calc
      (e A) (f ≫ g) = (e B) f ≫ g := by
        simpa [A, B, e] using
          (lowerShriekComparisonHomEquiv_naturality_right
            (P := P) (J := J) (ℱ := ℱ) (β := f) (α := g))
      _ = 𝟙 B ≫ g := by simp [f]
      _ = g := by simp
      _ = (e A) (𝟙 A) := by simp [g]
  -- The representing-object comparison maps are inverse, so `B` and `A` are isomorphic.
  exact ⟨{ hom := g, inv := f, hom_inv_id := hgf, inv_hom_id := hfg }⟩

end

end

end FibredCategoryOver
end CategoryTheory
