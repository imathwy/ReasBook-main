import Mathlib
import StacksProject_2024.Chap04.Definition_4_32_1
import StacksProject_2024.Chap04.Definition_4_33_9
import StacksProject_2024.Chap04.Lemma_4_32_3
import StacksProject_2024.Chap04.Lemma_4_35_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryOver
open BasedFunctor
open scoped Bicategory

universe u₁ u₂ u₃ v

namespace CategoryTheory

variable {C : Type u₁} [Category.{v} C]
variable {S : Type u₂} [Category.{v} S]
variable {S' : Type u₃} [Category.{v} S']

/- Domain-style sampling for Lemma 4.34.1:
- primary domain: relative inertia over a fixed base and its comparison with the chapter owner
  `explicitTwoFibreProduct` in `Cat/C`;
- sampled owner-level declarations:
  `CategoryOver.explicitTwoFibreProduct`,
  `CategoryOver.relativeInertiaOver`,
  `BasedFunctor.IsEquivalenceOverBase`,
  `Functor.Fiber`;
- best owner abstraction: the intrinsic source-level data are the relative inertia objects
  `RelativeInertiaObject F`, while the public over-base diagonal and comparison maps should live on
  the bundled morphism owner `X ⥤ᵇ Y` in `Cat/C`, not on a bare functor plus a separate
  commutativity proof;
- primitive data: an object `x : S` together with an automorphism `α : x ≅ x` whose image under
  `F` is the identity;
- derived API: the category structure, projection and structure functors, induced functoriality on
  inertia, and the over-`C` bridge from relative inertia to the diagonal self-`2`-fibre product.

Source/core/bridge triage:
- `source-facing`: `RelativeInertiaObject`, `relativeInertiaProjection`, and the bundled
  over-base theorem `BasedFunctor.relativeInertiaEquivalenceOverBase`;
- `core/canonical`: `CategoryOver.relativeInertiaOver`,
  `CategoryOver.explicitTwoFibreProduct`, and `BasedFunctor.IsEquivalenceOverBase`;
- `bridge/view`: the internal bare-functor constructions used to build the bundled `Cat/C`
  morphisms. -/

/-- An object of the relative inertia of a functor `F : S ⥤ S'` is an object `x` of `S`
together with an automorphism of `x` whose image under `F` is the identity. -/
structure RelativeInertiaObject (F : S ⥤ S') where
  /-- The underlying object of the total category. -/
  x : S
  /-- The automorphism of `x`. -/
  α : x ≅ x
  /-- The automorphism becomes the identity after applying `F`. -/
  map_hom_eq_id : F.map α.hom = 𝟙 (F.obj x)

/-- A morphism in the relative inertia category intertwines the chosen automorphisms. -/
structure RelativeInertiaHom (F : S ⥤ S')
    (X Y : RelativeInertiaObject F) where
  /-- The underlying morphism in `S`. -/
  φ : X.x ⟶ Y.x
  /-- The underlying morphism commutes with the chosen automorphisms. -/
  comm : X.α.hom ≫ φ = φ ≫ Y.α.hom

/-- Relative-inertia morphisms are determined by their underlying morphisms in `S`. -/
@[ext] theorem RelativeInertiaHom.ext {F : S ⥤ S'} {X Y : RelativeInertiaObject F}
    (f g : RelativeInertiaHom F X Y) (h : f.φ = g.φ) :
    f = g := by
  cases f
  cases g
  cases h
  rfl

variable (F : S ⥤ S')

-- Proof sketch: both sides are the same composite with an identity morphism on `X.x`.
/-- The identity morphism of an inertia object commutes with its chosen automorphism. -/
private theorem relativeInertiaHom_id_comm
    (X : RelativeInertiaObject F) :
    X.α.hom ≫ 𝟙 X.x = 𝟙 X.x ≫ X.α.hom := sorry

/-- The identity morphism in the relative inertia category. -/
private def relativeInertiaHomId
    (X : RelativeInertiaObject F) :
    RelativeInertiaHom F X X :=
  { φ := 𝟙 X.x
    comm := relativeInertiaHom_id_comm F X }

-- Proof sketch: paste the two intertwining squares for `f` and `g` and reassociate.
/-- The composite of two inertia morphisms again commutes with the chosen automorphisms. -/
private theorem relativeInertiaHom_comp_comm
    {X Y Z : RelativeInertiaObject F}
    (f : RelativeInertiaHom F X Y)
    (g : RelativeInertiaHom F Y Z) :
    X.α.hom ≫ (f.φ ≫ g.φ) = (f.φ ≫ g.φ) ≫ Z.α.hom := sorry

/-- Composition in the relative inertia category. -/
private def relativeInertiaHomComp
    {X Y Z : RelativeInertiaObject F}
    (f : RelativeInertiaHom F X Y)
    (g : RelativeInertiaHom F Y Z) :
    RelativeInertiaHom F X Z :=
  { φ := f.φ ≫ g.φ
    comm := relativeInertiaHom_comp_comm F f g }

-- Proof sketch: both morphisms have the same underlying component `f.φ`.
/-- Left identity for the composition law on relative inertia morphisms. -/
private theorem relativeInertiaHom_id_comp
    {X Y : RelativeInertiaObject F}
    (f : RelativeInertiaHom F X Y) :
    relativeInertiaHomComp F (relativeInertiaHomId F X) f = f := sorry

-- Proof sketch: both morphisms have the same underlying component `f.φ`.
/-- Right identity for the composition law on relative inertia morphisms. -/
private theorem relativeInertiaHom_comp_id
    {X Y : RelativeInertiaObject F}
    (f : RelativeInertiaHom F X Y) :
    relativeInertiaHomComp F f (relativeInertiaHomId F Y) = f := sorry

-- Proof sketch: all three composites have the same underlying morphism
-- `f.φ ≫ g.φ ≫ h.φ`, and the compatibility proofs are propositions.
/-- Associativity of composition in the relative inertia category. -/
private theorem relativeInertiaHom_assoc
    {W X Y Z : RelativeInertiaObject F}
    (f : RelativeInertiaHom F W X)
    (g : RelativeInertiaHom F X Y)
    (h : RelativeInertiaHom F Y Z) :
    relativeInertiaHomComp F (relativeInertiaHomComp F f g) h =
      relativeInertiaHomComp F f (relativeInertiaHomComp F g h) := sorry

/-- The relative inertia objects and intertwining morphisms form a category. -/
instance relativeInertiaCategory :
    Category (RelativeInertiaObject F) where
  Hom X Y := RelativeInertiaHom F X Y
  id := relativeInertiaHomId F
  comp f g := relativeInertiaHomComp F f g
  id_comp := relativeInertiaHom_id_comp F
  comp_id := relativeInertiaHom_comp_id F
  assoc f g h := relativeInertiaHom_assoc F f g h

namespace RelativeInertiaHom

variable {F} {X Y : RelativeInertiaObject F}

/-- A morphism in a relative inertia category is an isomorphism as soon as its underlying
morphism in the source category is an isomorphism. -/
theorem isIso_of_isIso (f : X ⟶ Y) [IsIso f.φ] : IsIso f := by
  let g : RelativeInertiaHom F Y X :=
    { φ := inv f.φ
      comm := by
        apply (cancel_mono f.φ).1
        simp [Category.assoc, f.comm] }
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply RelativeInertiaHom.ext
    change f.φ ≫ inv f.φ = 𝟙 X.x
    simp
  · apply RelativeInertiaHom.ext
    change inv f.φ ≫ f.φ = 𝟙 Y.x
    simp

end RelativeInertiaHom

/-- The projection from the relative inertia category to the base category `C`. -/
def relativeInertiaProjection
    (p : S ⥤ C) :
    RelativeInertiaObject F ⥤ C where
  obj X := p.obj X.x
  map f := p.map f.φ
  map_id X := p.map_id X.x
  map_comp f g := p.map_comp f.φ g.φ

/-- The canonical forgetful functor from the relative inertia of `F` to the source category
`S`. -/
def relativeInertiaStructureFunctor :
    RelativeInertiaObject F ⥤ S where
  obj X := X.x
  map f := f.φ
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The canonical structure functor from the relative inertia of `F` lies over the base category
`C`. -/
theorem relativeInertiaStructureFunctor_comm
    (p : S ⥤ C) :
    relativeInertiaStructureFunctor F ⋙ p = relativeInertiaProjection F p :=
  rfl

/-- The identity morphisms define the neutral section from the source category to its relative
inertia. -/
def relativeInertiaIdentitySection :
    S ⥤ RelativeInertiaObject F where
  obj X :=
    { x := X
      α := Iso.refl X
      map_hom_eq_id := F.map_id X }
  map f :=
    { φ := f
      comm := by simp }
  map_id X := RelativeInertiaHom.ext _ _ rfl
  map_comp f g := RelativeInertiaHom.ext _ _ rfl

/-- The neutral section is a right inverse to the relative-inertia structure functor. -/
@[simp] theorem relativeInertiaIdentitySection_comp_structureFunctor :
    relativeInertiaIdentitySection F ⋙ relativeInertiaStructureFunctor F = 𝟭 S :=
  rfl

/-- The neutral section picks out the identity automorphism on each source object. -/
@[simp] theorem relativeInertiaIdentitySection_obj_α (X : S) :
    ((relativeInertiaIdentitySection F).obj X).α = Iso.refl X :=
  rfl

private theorem relativeInertiaMapObj_map_hom_eq_id
    {S₁ S₁' S₂ S₂' : Type*}
    [Category.{v} S₁] [Category.{v} S₁'] [Category.{v} S₂] [Category.{v} S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'}
    (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂)
    (X : RelativeInertiaObject F₁) :
    F₂.map (G.map X.α.hom) = 𝟙 (F₂.obj (G.obj X.x)) := sorry

private def relativeInertiaMapObj
    {S₁ S₁' S₂ S₂' : Type*}
    [Category.{v} S₁] [Category.{v} S₁'] [Category.{v} S₂] [Category.{v} S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'}
    (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂)
    (X : RelativeInertiaObject F₁) :
    RelativeInertiaObject F₂ :=
  { x := G.obj X.x
    α := G.mapIso X.α
    map_hom_eq_id := relativeInertiaMapObj_map_hom_eq_id G G' τ X }

private theorem relativeInertiaMapHom_comm
    {S₁ S₁' S₂ : Type*}
    [Category.{v} S₁] [Category.{v} S₁'] [Category.{v} S₂]
    {F : S₁ ⥤ S₁'} (G : S₁ ⥤ S₂)
    {X Y : RelativeInertiaObject F} (f : X ⟶ Y) :
    G.map X.α.hom ≫ G.map f.φ = G.map f.φ ≫ G.map Y.α.hom := sorry

private def relativeInertiaMapHom
    {S₁ S₁' S₂ S₂' : Type*}
    [Category.{v} S₁] [Category.{v} S₁'] [Category.{v} S₂] [Category.{v} S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'}
    (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂)
    {X Y : RelativeInertiaObject F₁} (f : X ⟶ Y) :
    relativeInertiaMapObj G G' τ X ⟶ relativeInertiaMapObj G G' τ Y :=
  { φ := G.map f.φ
    comm := relativeInertiaMapHom_comm G f }

private theorem relativeInertiaMap_map_id
    {S₁ S₁' S₂ S₂' : Type*}
    [Category.{v} S₁] [Category.{v} S₁'] [Category.{v} S₂] [Category.{v} S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'}
    (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂)
    (X : RelativeInertiaObject F₁) :
    relativeInertiaMapHom G G' τ (𝟙 X) = 𝟙 (relativeInertiaMapObj G G' τ X) := sorry

private theorem relativeInertiaMap_map_comp
    {S₁ S₁' S₂ S₂' : Type*}
    [Category.{v} S₁] [Category.{v} S₁'] [Category.{v} S₂] [Category.{v} S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'}
    (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂)
    {X Y Z : RelativeInertiaObject F₁} (f : X ⟶ Y) (g : Y ⟶ Z) :
    relativeInertiaMapHom G G' τ (f ≫ g) =
      relativeInertiaMapHom G G' τ f ≫ relativeInertiaMapHom G G' τ g := sorry

/-- An invertible comparison square `F₁ ⋙ G' ≅ G ⋙ F₂` induces the canonical functor on relative
inertia categories, sending `(x, α)` to `(G.obj x, G.mapIso α)` and intertwining morphisms by
`G.map`. -/
def relativeInertiaMap
    {S₁ S₁' S₂ S₂' : Type*}
    [Category.{v} S₁] [Category.{v} S₁'] [Category.{v} S₂] [Category.{v} S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'}
    (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂) :
    RelativeInertiaObject F₁ ⥤ RelativeInertiaObject F₂ where
  obj := relativeInertiaMapObj G G' τ
  map := relativeInertiaMapHom G G' τ
  map_id := relativeInertiaMap_map_id G G' τ
  map_comp := relativeInertiaMap_map_comp G G' τ

/-- The canonical functor on relative inertia sends the underlying object `x` to `G.obj x`. -/
@[simp] theorem relativeInertiaMap_obj_x
    {S₁ S₁' S₂ S₂' : Type*}
    [Category.{v} S₁] [Category.{v} S₁'] [Category.{v} S₂] [Category.{v} S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'}
    (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂)
    (X : RelativeInertiaObject F₁) :
    ((relativeInertiaMap G G' τ).obj X).x = G.obj X.x :=
  rfl

/-- The canonical functor on relative inertia sends the chosen automorphism `α` to `G.mapIso α`.
-/
@[simp] theorem relativeInertiaMap_obj_α
    {S₁ S₁' S₂ S₂' : Type*}
    [Category.{v} S₁] [Category.{v} S₁'] [Category.{v} S₂] [Category.{v} S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'}
    (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂)
    (X : RelativeInertiaObject F₁) :
    ((relativeInertiaMap G G' τ).obj X).α = G.mapIso X.α :=
  rfl

/-- The canonical functor on relative inertia sends the underlying arrow `φ` to `G.map φ`. -/
@[simp] theorem relativeInertiaMap_map_hom
    {S₁ S₁' S₂ S₂' : Type*}
    [Category.{v} S₁] [Category.{v} S₁'] [Category.{v} S₂] [Category.{v} S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'}
    (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂)
    {X Y : RelativeInertiaObject F₁} (f : X ⟶ Y) :
    ((relativeInertiaMap G G' τ).map f).φ = G.map f.φ :=
  rfl

variable (p : S ⥤ C)

variable {p}
variable (p' : S' ⥤ C)

-- Proof sketch: apply `p'` to the equality `F.map X.α.hom = 𝟙`, then rewrite both sides using
-- the strict commutativity `F ⋙ p' = p`.
/-- The automorphism in an inertia object is vertical over `C`. -/
theorem relativeInertiaObject_base_eq_id
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    p.map X.α.hom = 𝟙 (p.obj X.x) := sorry

private abbrev overFunctor
    (comm : F ⋙ p' = p) :
    BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p' :=
  { toFunctor := F
    w := comm }

private theorem relativeDiagonalObjIso_hom_isLift
    (comm : F ⋙ p' = p)
    (X : S) :
    p'.IsHomLift (𝟙 (p.obj X)) (𝟙 (F.obj X)) := by
  cases comm
  simp

private theorem relativeDiagonalObjIso_hom_inv_id
    (X : S) :
    𝟙 (F.obj X) ≫ 𝟙 (F.obj X) = 𝟙 (F.obj X) := by
  simp

private def relativeDiagonalObjIso
    (comm : F ⋙ p' = p)
    (X : S) :
    ((overFunctor F p' comm).fiberFunctor (p.obj X)).obj (Functor.Fiber.mk rfl) ≅
      ((overFunctor F p' comm).fiberFunctor (p.obj X)).obj (Functor.Fiber.mk rfl) where
  hom := ⟨𝟙 (F.obj X), relativeDiagonalObjIso_hom_isLift F p' comm X⟩
  inv := ⟨𝟙 (F.obj X), relativeDiagonalObjIso_hom_isLift F p' comm X⟩
  hom_inv_id := by
    apply Functor.Fiber.hom_ext
    exact relativeDiagonalObjIso_hom_inv_id F X
  inv_hom_id := by
    apply Functor.Fiber.hom_ext
    exact relativeDiagonalObjIso_hom_inv_id F X

private theorem relativeDiagonalFunctor_map_comm
    (comm : F ⋙ p' = p)
    {X Y : S}
    (f : X ⟶ Y) :
    CommSq
      (F.map f)
      (relativeDiagonalObjIso F p' comm X).hom.1
      (relativeDiagonalObjIso F p' comm Y).hom.1
      (F.map f) := by
  sorry

private def relativeDiagonalObject
    (comm : F ⋙ p' = p)
    (X : S) :
    ExplicitTwoFibreProductObject (overFunctor F p' comm) (overFunctor F p' comm) :=
  { U := p.obj X
    obj :=
      { fst := Functor.Fiber.mk rfl
        snd := Functor.Fiber.mk rfl
        iso := relativeDiagonalObjIso F p' comm X } }

private def relativeDiagonalFunctorMap
    (comm : F ⋙ p' = p)
    {X Y : S}
    (f : X ⟶ Y) :
    relativeDiagonalObject F p' comm X ⟶ relativeDiagonalObject F p' comm Y :=
  { base := p.map f
    a := f
    a_over := by
      exact IsHomLift.of_fac p (p.map f) f rfl rfl (by simp)
    b := f
    b_over := by
      exact IsHomLift.of_fac p (p.map f) f rfl rfl (by simp)
    comm := relativeDiagonalFunctor_map_comm F p' comm f }

private theorem relativeDiagonalFunctor_map_id
    (comm : F ⋙ p' = p)
    (X : S) :
    relativeDiagonalFunctorMap F p' comm (𝟙 X) =
      𝟙 (relativeDiagonalObject F p' comm X) := by
  apply ExplicitTwoFibreProductHom.ext
  · rfl
  · rfl

private theorem relativeDiagonalFunctor_map_comp
    (comm : F ⋙ p' = p)
    {X Y Z : S}
    (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    relativeDiagonalFunctorMap F p' comm (f ≫ g) =
      relativeDiagonalFunctorMap F p' comm f ≫
        relativeDiagonalFunctorMap F p' comm g := by
  apply ExplicitTwoFibreProductHom.ext
  · rfl
  · rfl

private def relativeDiagonalFunctor
    (comm : F ⋙ p' = p) :
    S ⥤ (explicitTwoFibreProduct (overFunctor F p' comm) (overFunctor F p' comm)).obj where
  obj := relativeDiagonalObject F p' comm
  map := relativeDiagonalFunctorMap F p' comm
  map_id := relativeDiagonalFunctor_map_id F p' comm
  map_comp := relativeDiagonalFunctor_map_comp F p' comm

private theorem relativeDiagonalFunctor_comm
    (comm : F ⋙ p' = p) :
    relativeDiagonalFunctor F p' comm ⋙
        (explicitTwoFibreProduct (overFunctor F p' comm) (overFunctor F p' comm)).p =
      p := by
  sorry

/-- Internal bare-functor model for the canonical diagonal morphism in `Cat/C`. The bundled
public owner is `BasedFunctor.relativeDiagonalOver`. -/
private def relativeDiagonalOverRaw
    (comm : F ⋙ p' = p) :
    BasedCategory.ofFunctor p ⥤ᵇ
      explicitTwoFibreProduct (overFunctor F p' comm) (overFunctor F p' comm) :=
  { toFunctor := relativeDiagonalFunctor F p' comm
    w := relativeDiagonalFunctor_comm F p' comm }

private theorem relativeInertiaObject_map_inv_eq_id
    (X : RelativeInertiaObject F) :
    F.map X.α.inv = 𝟙 (F.obj X.x) := by
  have h : F.map X.α.inv ≫ F.map X.α.hom = 𝟙 (F.obj X.x) := by
    simp
  simpa [X.map_hom_eq_id] using h

private theorem relativeInertiaObject_base_inv_eq_id
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    p.map X.α.inv = 𝟙 (p.obj X.x) := by
  have h : p.map X.α.inv ≫ p.map X.α.hom = 𝟙 (p.obj X.x) := by
    simp
  simpa [relativeInertiaObject_base_eq_id F p' comm X] using h

private def relativeInertiaComparisonHom
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    ExplicitTwoFibreProductHom
      (overFunctor F p' comm)
      (overFunctor F p' comm)
      ((relativeDiagonalOverRaw F p' comm).obj X.x)
      ((relativeDiagonalOverRaw F p' comm).obj X.x) where
  base := 𝟙 (p.obj X.x)
  a := X.α.hom
  a_over := by
    change p.IsHomLift (𝟙 (p.obj X.x)) X.α.hom
    simpa [relativeInertiaObject_base_eq_id F p' comm X] using
      (inferInstance : p.IsHomLift (p.map X.α.hom) X.α.hom)
  b := 𝟙 X.x
  b_over := by
    change p.IsHomLift (𝟙 (p.obj X.x)) (𝟙 X.x)
    refine IsHomLift.of_fac p (𝟙 (p.obj X.x)) (𝟙 X.x) rfl rfl ?_
    simp
  comm := by
    sorry

private theorem relativeInertiaComparisonHom_isHomLift
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    let Y := (relativeDiagonalOverRaw F p' comm).obj X.x
    ((explicitTwoFibreProduct (overFunctor F p' comm) (overFunctor F p' comm)).p).IsHomLift
      (𝟙 (p.obj X.x))
      (relativeInertiaComparisonHom F p' comm X) := by
  sorry

private def relativeInertiaComparisonInvHom
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    ExplicitTwoFibreProductHom
      (overFunctor F p' comm)
      (overFunctor F p' comm)
      ((relativeDiagonalOverRaw F p' comm).obj X.x)
      ((relativeDiagonalOverRaw F p' comm).obj X.x) where
  base := 𝟙 (p.obj X.x)
  a := X.α.inv
  a_over := by
    change p.IsHomLift (𝟙 (p.obj X.x)) X.α.inv
    simpa [relativeInertiaObject_base_inv_eq_id F p' comm X] using
      (inferInstance : p.IsHomLift (p.map X.α.inv) X.α.inv)
  b := 𝟙 X.x
  b_over := by
    change p.IsHomLift (𝟙 (p.obj X.x)) (𝟙 X.x)
    refine IsHomLift.of_fac p (𝟙 (p.obj X.x)) (𝟙 X.x) rfl rfl ?_
    simp
  comm := by
    sorry

private theorem relativeInertiaComparisonInvHom_isHomLift
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    let Y := (relativeDiagonalOverRaw F p' comm).obj X.x
    ((explicitTwoFibreProduct (overFunctor F p' comm) (overFunctor F p' comm)).p).IsHomLift
      (𝟙 (p.obj X.x))
      (relativeInertiaComparisonInvHom F p' comm X) := by
  sorry

private theorem relativeInertiaComparisonIso_hom_inv_id
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    relativeInertiaComparisonHom F p' comm X ≫
        relativeInertiaComparisonInvHom F p' comm X =
      𝟙 ((relativeDiagonalOverRaw F p' comm).obj X.x) := by
  sorry

private theorem relativeInertiaComparisonIso_inv_hom_id
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    relativeInertiaComparisonInvHom F p' comm X ≫
        relativeInertiaComparisonHom F p' comm X =
      𝟙 ((relativeDiagonalOverRaw F p' comm).obj X.x) := by
  sorry

private def relativeInertiaComparisonIso
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    ((relativeDiagonalOverRaw F p' comm).fiberFunctor (p.obj X.x)).obj (Functor.Fiber.mk rfl) ≅
      ((relativeDiagonalOverRaw F p' comm).fiberFunctor (p.obj X.x)).obj (Functor.Fiber.mk rfl) where
  hom := ⟨relativeInertiaComparisonHom F p' comm X,
    relativeInertiaComparisonHom_isHomLift F p' comm X⟩
  inv := ⟨relativeInertiaComparisonInvHom F p' comm X,
    relativeInertiaComparisonInvHom_isHomLift F p' comm X⟩
  hom_inv_id := by
    apply Functor.Fiber.hom_ext
    exact relativeInertiaComparisonIso_hom_inv_id F p' comm X
  inv_hom_id := by
    apply Functor.Fiber.hom_ext
    exact relativeInertiaComparisonIso_inv_hom_id F p' comm X

private def relativeInertiaToDiagonalPullbackObj
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    ExplicitTwoFibreProductObject
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm) :=
  { U := p.obj X.x
    obj :=
      { fst := Functor.Fiber.mk rfl
        snd := Functor.Fiber.mk rfl
        iso := relativeInertiaComparisonIso F p' comm X } }

private theorem relativeInertiaToDiagonalPullback_map_comm
    (comm : F ⋙ p' = p)
    {X Y : RelativeInertiaObject F}
    (f : RelativeInertiaHom F X Y) :
    CommSq
      ((relativeDiagonalOverRaw F p' comm).map f.φ)
      (relativeInertiaToDiagonalPullbackObj F p' comm X).obj.iso.hom.1
      (relativeInertiaToDiagonalPullbackObj F p' comm Y).obj.iso.hom.1
      ((relativeDiagonalOverRaw F p' comm).map f.φ) := by
  sorry

private def relativeInertiaToDiagonalPullbackMap
    (comm : F ⋙ p' = p)
    {X Y : RelativeInertiaObject F}
    (f : RelativeInertiaHom F X Y) :
    ExplicitTwoFibreProductHom
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)
      (relativeInertiaToDiagonalPullbackObj F p' comm X)
      (relativeInertiaToDiagonalPullbackObj F p' comm Y) :=
  { base := p.map f.φ
    a := f.φ
    a_over := by
      exact IsHomLift.of_fac p (p.map f.φ) f.φ rfl rfl (by simp)
    b := f.φ
    b_over := by
      exact IsHomLift.of_fac p (p.map f.φ) f.φ rfl rfl (by simp)
    comm := relativeInertiaToDiagonalPullback_map_comm F p' comm f }

private theorem relativeInertiaToDiagonalPullback_map_id
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    relativeInertiaToDiagonalPullbackMap F p' comm (𝟙 X) =
      𝟙 (relativeInertiaToDiagonalPullbackObj F p' comm X) := by
  apply ExplicitTwoFibreProductHom.ext
  · rfl
  · rfl

private def relativeInertiaToDiagonalPullbackFunctor
    (comm : F ⋙ p' = p) :
    RelativeInertiaObject F ⥤
      (explicitTwoFibreProduct
        (relativeDiagonalOverRaw F p' comm)
        (relativeDiagonalOverRaw F p' comm)).obj where
  obj := relativeInertiaToDiagonalPullbackObj F p' comm
  map := relativeInertiaToDiagonalPullbackMap F p' comm
  map_id := relativeInertiaToDiagonalPullback_map_id F p' comm
  map_comp := by
    intro X Y Z f g
    apply ExplicitTwoFibreProductHom.ext
    · rfl
    · rfl

private theorem relativeInertiaToDiagonalPullbackFunctor_comm
    (comm : F ⋙ p' = p) :
    relativeInertiaToDiagonalPullbackFunctor F p' comm ⋙
        (explicitTwoFibreProduct
          (relativeDiagonalOverRaw F p' comm)
          (relativeDiagonalOverRaw F p' comm)).p =
      relativeInertiaProjection F p := by
  sorry

/-- Internal bare-functor comparison morphism from relative inertia to the self-pullback of the
raw diagonal. The bundled public owner is `BasedFunctor.relativeInertiaToDiagonalPullback`. -/
private def relativeInertiaToDiagonalPullbackRaw
    (comm : F ⋙ p' = p) :
    BasedCategory.ofFunctor (relativeInertiaProjection F p) ⥤ᵇ
      explicitTwoFibreProduct (relativeDiagonalOverRaw F p' comm) (relativeDiagonalOverRaw F p' comm)
    where
  toFunctor := relativeInertiaToDiagonalPullbackFunctor F p' comm
  w := relativeInertiaToDiagonalPullbackFunctor_comm F p' comm

-- Proof sketch: this is the Stacks comparison `(x, α) ↦ (x, x, α, id_x)` into the self-pullback
-- of the relative diagonal `S ⟶ S ×_{S'} S`. A quasi-inverse sends the explicit pullback datum
-- `(x, x, (ι, κ))` to `(x, κ⁻¹ ≫ ι)`, exactly as in the source argument using the canonical
-- explicit `2`-fibre-product model from Lemma `4.33.10`.
/-- Internal bare-functor form of Lemma 4.34.1. The public over-base statement is the bundled
owner theorem `BasedFunctor.relativeInertiaEquivalenceOverBase`. -/
private theorem relativeInertiaEquivalenceOverBaseRaw
    (comm : F ⋙ p' = p) :
    (relativeInertiaToDiagonalPullbackRaw F p' comm).IsEquivalenceOverBase := sorry

namespace BasedFunctor

variable {X Y : CategoryOver C}

/-- The canonical diagonal morphism in `Cat/C` attached to a bundled morphism over `C`. Its target
is the explicit self-`2`-fibre product `X ×_Y X`. -/
def relativeDiagonalOver (F : X ⥤ᵇ Y) :
    X ⥤ᵇ explicitTwoFibreProduct F F :=
  relativeDiagonalOverRaw F.toFunctor Y.p F.w

/-- The canonical comparison morphism in `Cat/C` from the relative inertia over `C` of a bundled
morphism `F` to the explicit self-`2`-fibre product of its diagonal. -/
def relativeInertiaToDiagonalPullback (F : X ⥤ᵇ Y) :
    BasedCategory.ofFunctor (relativeInertiaProjection F.toFunctor X.p) ⥤ᵇ
      explicitTwoFibreProduct (relativeDiagonalOver F) (relativeDiagonalOver F) :=
  relativeInertiaToDiagonalPullbackRaw F.toFunctor Y.p F.w

-- Proof sketch: this is the bundled over-`C` restatement of the internal bare-functor comparison
-- theorem above, with the commutativity proof supplied canonically by `F.w`.
/-- Lemma 4.34.1: for a morphism `F : X ⟶ Y` in `Cat/C`, the relative inertia of `F` over `C` is
equivalent over `C` to the explicit self-`2`-fibre product of the canonical diagonal
`X ⟶ X ×_Y X`. -/
theorem relativeInertiaEquivalenceOverBase (F : X ⥤ᵇ Y) :
    (relativeInertiaToDiagonalPullback F).IsEquivalenceOverBase :=
  relativeInertiaEquivalenceOverBaseRaw F.toFunctor Y.p F.w

end BasedFunctor

namespace FibredInGroupoidsMor

section

variable {C : Type (max u₁ v)} [Category.{v} C]
variable {X Y : FibredInGroupoidsOver.{v, max u₁ v, max u₁ v, v} C}

/-- The canonical self-`2`-fibre-product target of the diagonal of a morphism of categories
fibred in groupoids over `C`, obtained by rebundling the explicit pullback model in `Cat/C`. -/
theorem diagonalTargetProjection_isFibredInGroupoids
    (F : X ⟶ Y) :
    IsFibredInGroupoids
      (explicitTwoFibreProduct
        (FibredInGroupoidsMor.toBasedFunctor F)
        (FibredInGroupoidsMor.toBasedFunctor F)).p := by
  sorry

/-- The canonical target of the diagonal of a morphism of categories fibred in groupoids over
`C`, obtained by rebundling the explicit self-`2`-fibre product in `Cat/C`. -/
abbrev diagonalTarget (F : X ⟶ Y) : FibredInGroupoidsOver C :=
  letI := diagonalTargetProjection_isFibredInGroupoids F
  FibredInGroupoidsOver.ofFunctor <|
    (explicitTwoFibreProduct
      (FibredInGroupoidsMor.toBasedFunctor F)
      (FibredInGroupoidsMor.toBasedFunctor F)).p

/-- The canonical diagonal morphism attached to a morphism of categories fibred in groupoids over
`C`. -/
abbrev diagonalMor (F : X ⟶ Y) : X ⟶ diagonalTarget F :=
  letI := diagonalTargetProjection_isFibredInGroupoids F
  FibredInGroupoidsMor.ofBasedFunctor <|
    BasedFunctor.relativeDiagonalOver (FibredInGroupoidsMor.toBasedFunctor F)

end

end FibredInGroupoidsMor

namespace FibredInGroupoidsOver

section

variable {C : Type (max u₁ v)} [Category.{v} C]
variable (X : FibredInGroupoidsOver.{v, max u₁ v, max u₁ v, v} C)

/-- The canonical diagonal of the base projection of a bundled category fibred in groupoids over
`C`. This is the object-prefix bridge to the owner morphism `X.baseProjection.diagonalMor`. -/
abbrev baseProjectionDiagonalMor :=
  FibredInGroupoidsMor.diagonalMor X.baseProjection

end

end FibredInGroupoidsOver

-- Proof sketch: use the over-`C` equivalence from Lemma `4.34.1` to replace the relative
-- inertia projection by the explicit self-`2`-fibre-product of the diagonal
-- `S ⟶ S ×_{S'} S`, then apply Lemma `4.33.10` to the canonical explicit `2`-fibre-product
-- construction.
/-- The projection from the relative inertia of a morphism of fibred categories over `C` is
fibred. -/
theorem relativeInertiaProjection_isFibered
    {X Y : FibredCategoryOver C} (F : X ⟶ Y) :
    (relativeInertiaProjection (FibredCategoryMor.toFunctor F) X.p).IsFibered := sorry

instance
    {X Y : FibredCategoryOver C} (F : X ⟶ Y) :
    (relativeInertiaProjection (FibredCategoryMor.toFunctor F) X.p).IsFibered :=
  relativeInertiaProjection_isFibered F

end CategoryTheory
