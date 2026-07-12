import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Order.Directed

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry

/- Semantic recall for this item:
`lean_leansearch` surfaced the canonical sheaf owners `Scheme.zariskiTopology` and
`Presheaf.IsSheaf`, while local Chapter 34 precedent represents full subcategories of `Sch/S`
by `ObjectProperty.FullSubcategory` on `Over S`. Local Chapter 32 precedent represents directed
limits of affine schemes over a base by diagrams `OrderDual I ⥤ Over S` with explicit limit cones.
The source tag evidence is consistent with Stacks tag `0EUW`.
-/

/-- A full subcategory of `Sch/S` contains affine opens of its objects up to isomorphism. -/
def overSubcategoryContainsAffineOpens {S : Scheme.{u}} (C : ObjectProperty (Over S)) : Prop :=
  ∀ (X : C.FullSubcategory) (U : Scheme.Opens (X.obj : Over S).left), IsAffineOpen U →
    ∃ Y : C.FullSubcategory, Nonempty (Over.mk (U.ι ≫ X.obj.hom) ≅ Y.obj)

/-- Unfolding the affine-open closure condition for a full subcategory of `Sch/S`. -/
theorem overSubcategoryContainsAffineOpens_iff {S : Scheme.{u}}
    (C : ObjectProperty (Over S)) :
    overSubcategoryContainsAffineOpens C ↔
      ∀ (X : C.FullSubcategory) (U : Scheme.Opens (X.obj : Over S).left), IsAffineOpen U →
        ∃ Y : C.FullSubcategory, Nonempty (Over.mk (U.ι ≫ X.obj.hom) ≅ Y.obj) := sorry

/-- A full subcategory of `Sch/S` contains affine schemes of finite presentation over affine
opens of `S`, up to isomorphism over `S`. -/
def overSubcategoryContainsFinitelyPresentedAffinesOverAffineBase {S : Scheme.{u}}
    (C : ObjectProperty (Over S)) : Prop :=
  ∀ (U : S.Opens), IsAffineOpen U →
    ∀ (V : Scheme.{u}) [IsAffine V] (g : V ⟶ (U : Scheme.{u})),
      LocallyOfFinitePresentation g →
        ∃ Y : C.FullSubcategory, Nonempty (Over.mk (g ≫ U.ι) ≅ Y.obj)

/-- Unfolding the finite-presentation affine-over-affine-base closure condition. -/
theorem overSubcategoryContainsFinitelyPresentedAffinesOverAffineBase_iff {S : Scheme.{u}}
    (C : ObjectProperty (Over S)) :
    overSubcategoryContainsFinitelyPresentedAffinesOverAffineBase C ↔
      ∀ (U : S.Opens), IsAffineOpen U →
        ∀ (V : Scheme.{u}) [IsAffine V] (g : V ⟶ (U : Scheme.{u})),
          LocallyOfFinitePresentation g →
            ∃ Y : C.FullSubcategory, Nonempty (Over.mk (g ≫ U.ι) ≅ Y.obj) := sorry

/-- A presheaf on a full subcategory of `Sch/S` satisfies the Zariski sheaf condition for every
Zariski covering family whose source and target objects lie in the subcategory. -/
def satisfiesZariskiSheafConditionOnSubcategory {S : Scheme.{u}}
    (C : ObjectProperty (Over S)) (F : C.FullSubcategoryᵒᵖ ⥤ Type v) : Prop :=
  ∀ {ι : Type w} {X : C.FullSubcategory} (U : ι → C.FullSubcategory)
    (f : ∀ i, U i ⟶ X),
      Presieve.ofArrows (fun i ↦ (U i).obj) (fun i ↦ (f i).hom) ∈
        (Scheme.zariskiTopology.over S).toPrecoverage X.obj →
      Presieve.IsSheafFor F (Presieve.ofArrows U f)

/-- Unfolding the Zariski sheaf condition on a full subcategory of `Sch/S`. -/
theorem satisfiesZariskiSheafConditionOnSubcategory_iff {S : Scheme.{u}}
    (C : ObjectProperty (Over S)) (F : C.FullSubcategoryᵒᵖ ⥤ Type v) :
    satisfiesZariskiSheafConditionOnSubcategory C F ↔
      ∀ {ι : Type w} {X : C.FullSubcategory} (U : ι → C.FullSubcategory)
        (f : ∀ i, U i ⟶ X),
          Presieve.ofArrows (fun i ↦ (U i).obj) (fun i ↦ (f i).hom) ∈
            (Scheme.zariskiTopology.over S).toPrecoverage X.obj →
          Presieve.IsSheafFor F (Presieve.ofArrows U f) := sorry

/-- A presheaf on a full subcategory of `Sch/S` commutes with directed limits of affine schemes
whose stages and limit all lie in the subcategory. -/
def preservesDirectedAffineLimitsOnSubcategory {S : Scheme.{u}}
    (C : ObjectProperty (Over S)) (F : C.FullSubcategoryᵒᵖ ⥤ Type v) : Prop :=
  ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ C.FullSubcategory) (c : Cone D),
      IsLimit ((C.ι).mapCone c) →
      (∀ i : I, IsAffine ((D.obj i).obj : Over S).left) →
      IsAffine (c.pt.obj : Over S).left →
      Nonempty (IsColimit (F.mapCocone c.op))

/-- Unfolding preservation of directed affine limits on a full subcategory of `Sch/S`. -/
theorem preservesDirectedAffineLimitsOnSubcategory_iff {S : Scheme.{u}}
    (C : ObjectProperty (Over S)) (F : C.FullSubcategoryᵒᵖ ⥤ Type v) :
    preservesDirectedAffineLimitsOnSubcategory C F ↔
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ C.FullSubcategory) (c : Cone D),
          IsLimit ((C.ι).mapCone c) →
          (∀ i : I, IsAffine ((D.obj i).obj : Over S).left) →
          IsAffine (c.pt.obj : Over S).left →
          Nonempty (IsColimit (F.mapCocone c.op)) := sorry

/-- A presheaf on `Sch/S` commutes with directed limits of affine schemes over `S`. -/
def preservesDirectedAffineLimitsOver (S : Scheme.{u})
    (F : (Over S)ᵒᵖ ⥤ Type v) : Prop :=
  ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D),
      IsLimit c →
      (∀ i : I, IsAffine (D.obj i).left) →
      IsAffine c.pt.left →
      Nonempty (IsColimit (F.mapCocone c.op))

/-- Unfolding preservation of directed affine limits on `Sch/S`. -/
theorem preservesDirectedAffineLimitsOver_iff (S : Scheme.{u})
    (F : (Over S)ᵒᵖ ⥤ Type v) :
    preservesDirectedAffineLimitsOver S F ↔
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ Over S) (c : Cone D),
          IsLimit c →
          (∀ i : I, IsAffine (D.obj i).left) →
          IsAffine c.pt.left →
          Nonempty (IsColimit (F.mapCocone c.op)) := sorry

/-- Lemma 34.13.1: a set-valued functor on a full subcategory of `Sch/S` satisfying the stated
affine-open closure, finite-presentation affine closure, Zariski sheaf condition, and directed
affine-limit condition admits a unique extension to `Sch/S` satisfying the corresponding Zariski
sheaf and directed affine-limit conditions. -/
@[stacks 0EUW]
theorem exists_unique_extension_of_zariskiSheaf_preservesDirectedAffineLimits
    {S : Scheme.{u}} (C : ObjectProperty (Over S))
    (F : C.FullSubcategoryᵒᵖ ⥤ Type v)
    (hC_open : overSubcategoryContainsAffineOpens C)
    (hC_fp : overSubcategoryContainsFinitelyPresentedAffinesOverAffineBase C)
    (hF_zariski : satisfiesZariskiSheafConditionOnSubcategory C F)
    (hF_limits : preservesDirectedAffineLimitsOnSubcategory C F) :
    ∃ (F' : (Over S)ᵒᵖ ⥤ Type v), ∃ (eF' : C.ι.op ⋙ F' ≅ F),
      ∃ (_ : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F'),
      ∃ (_ : preservesDirectedAffineLimitsOver S F'),
        ∀ (G : (Over S)ᵒᵖ ⥤ Type v) (eG : C.ι.op ⋙ G ≅ F),
          Presheaf.IsSheaf (Scheme.zariskiTopology.over S) G →
          preservesDirectedAffineLimitsOver S G →
          ∃! α : F' ≅ G, Functor.isoWhiskerLeft C.ι.op α ≪≫ eG = eF' := sorry

end AlgebraicGeometry
