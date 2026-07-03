import Mathlib
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_4_32_4 (from Chap04) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryOver
open scoped CategoricalPullback

namespace CategoryTheory

/-
Domain-style sampling for Example 4.32.4:
- primary domain: comparison between the categorical pullback of functors and the canonical
  `2`-fibre product in `Cat/C`;
- owner abstractions:
  `CategoricalPullback` for the pullback of plain categories,
  `CategoryOver` for categories over a fixed base,
  `BasedCategory.toBase` for the canonical morphism from an object of `Cat/C` to the base object,
  `CategoryOver.explicitTwoFibreProduct` for the canonical pullback object in `Cat/C`;
- primitive data: the unique functor from the one-point category to the one-object two-arrow
  groupoid, and the corresponding object of `Cat/exampleTwoArrowGroupoid`;
- derived API: the concrete discrete-category descriptions of the two pullback constructions,
  together with the resulting inequivalence companion.

Source/core/bridge triage:
- `source-facing`: the concrete descriptions of the two pullback constructions in the example;
- `core/canonical`: `CategoricalPullback` and `explicitTwoFibreProduct`;
- `bridge/view`: the inequivalence comparison theorem deduced from those concrete descriptions. -/

/-- The two-element group used to realize the one-object groupoid with two arrows. -/
abbrev exampleTwoArrowGroup := Multiplicative (ZMod 2)

/-- The groupoid with one object and two arrows from Example 4.32.4. -/
abbrev exampleTwoArrowGroupoid : Type := SingleObj exampleTwoArrowGroup

/-- The unique object of the one-object two-arrow groupoid. -/
private abbrev exampleBaseObject : exampleTwoArrowGroupoid :=
  SingleObj.star exampleTwoArrowGroup

/-- The discrete category with one object from Example 4.32.4. -/
abbrev exampleOnePointCategory : Type := Discrete PUnit

/-- The unique functor from the one-point discrete category to the two-arrow groupoid. -/
abbrev exampleOnePointToTwoArrowGroupoid :
    exampleOnePointCategory ⥤ exampleTwoArrowGroupoid :=
  Functor.fromPUnit exampleBaseObject

/-- The categorical pullback of the example cospan, viewed only as a cospan of categories. -/
private abbrev exampleCategoricalPullback :=
  exampleOnePointToTwoArrowGroupoid ⊡ exampleOnePointToTwoArrowGroupoid

/-- The one-point category viewed as an object of `Cat/exampleTwoArrowGroupoid`. -/
abbrev exampleOnePointOverGroupoid : CategoryOver exampleTwoArrowGroupoid :=
  BasedCategory.ofFunctor exampleOnePointToTwoArrowGroupoid

/-- The underlying category of the canonical `2`-fibre product in
`Cat/exampleTwoArrowGroupoid` for Example 4.32.4. -/
private abbrev exampleCategoryOverPullback :=
  (explicitTwoFibreProduct exampleOnePointOverGroupoid.toBase exampleOnePointOverGroupoid.toBase).obj

/-- The unique object of the one-point discrete category. -/
private abbrev exampleOnePointObject : exampleOnePointCategory :=
  Discrete.mk PUnit.unit

/-- The unique object of the fibre of the one-point functor over the unique base object. -/
private abbrev exampleOnePointLift :
    Functor.Fiber exampleOnePointOverGroupoid.p exampleBaseObject :=
  Functor.Fiber.mk (show exampleOnePointOverGroupoid.p.obj exampleOnePointObject = exampleBaseObject from rfl)

/-- The unique object of the fibre of the identity functor over the unique base object. -/
private abbrev exampleIdentityLift :
    Functor.Fiber (𝟭 exampleTwoArrowGroupoid) exampleBaseObject :=
  Functor.Fiber.mk (show (𝟭 exampleTwoArrowGroupoid).obj exampleBaseObject = exampleBaseObject from rfl)

/-- The canonical object of the `2`-fibre product in `Cat/exampleTwoArrowGroupoid`. -/
private abbrev exampleCategoryOverPullbackPoint : exampleCategoryOverPullback :=
  { U := exampleBaseObject
    obj :=
      { fst := exampleOnePointLift
        snd := exampleOnePointLift
        iso := Iso.refl exampleIdentityLift } }

/-- The object of the categorical pullback determined by a chosen automorphism of the unique
object of the two-arrow groupoid. -/
private noncomputable def exampleCategoricalPullbackFromArrow
    (g : exampleTwoArrowGroup) : exampleCategoricalPullback :=
  { fst := exampleOnePointObject
    snd := exampleOnePointObject
    iso := asIso g }

-- Proof sketch: the structural isomorphism of `exampleCategoricalPullbackFromArrow g` was chosen
-- to have `g` as its underlying morphism.
/-- Reading off the comparison isomorphism of the object built from `g` recovers `g`. -/
private theorem exampleCategoricalPullbackFromArrow_hom
    (g : exampleTwoArrowGroup) :
    (exampleCategoricalPullbackFromArrow g).iso.hom = g := by
  -- The object was defined with comparison isomorphism `asIso g`, so its stored morphism is `g`.
  simp [exampleCategoricalPullbackFromArrow, asIso_hom]

-- Proof sketch: an object of the categorical pullback over the constant point functor has only
-- the unique left and right objects available, so it is determined entirely by its comparison
-- isomorphism.
/-- Every object of the categorical pullback is recovered from its comparison automorphism. -/
private theorem exampleCategoricalPullback_from_hom
    (P : exampleCategoricalPullback) :
    exampleCategoricalPullbackFromArrow P.iso.hom = P := by
  -- The left and right components are forced to be the unique point object, so rebuilding from
  -- the stored comparison morphism only replaces `P.iso` by `asIso P.iso.hom`.
  cases P with
  | mk fst snd iso =>
      cases fst
      cases snd
      have hiso : asIso iso.hom = iso := by
        ext
        simp [asIso_hom]
      simpa [exampleCategoricalPullbackFromArrow, hiso]

/-- The objects of the categorical pullback are in bijection with the two automorphisms of the
unique object of the two-arrow groupoid. -/
private noncomputable def exampleCategoricalPullbackEquivGroup :
    exampleCategoricalPullback ≃ exampleTwoArrowGroup :=
  { toFun := fun P ↦ P.iso.hom
    invFun := exampleCategoricalPullbackFromArrow
    left_inv := exampleCategoricalPullback_from_hom
    right_inv := exampleCategoricalPullbackFromArrow_hom }

-- Proof sketch: the object-reconstruction equivalence identifies the object type of the
-- categorical pullback with the two automorphisms of the unique object of the base groupoid.
/-- The categorical pullback in Example 4.32.4 has finitely many objects. -/
private noncomputable instance :
    Fintype exampleCategoricalPullback :=
  Fintype.ofEquiv exampleTwoArrowGroup exampleCategoricalPullbackEquivGroup.symm

-- Proof sketch: an object of the categorical pullback is determined by the unique left and right
-- objects together with an automorphism of the unique object of the base groupoid, and there are
-- exactly two such automorphisms.
/-- The categorical pullback construction in Example 4.32.4 has exactly two objects. -/
private theorem exampleCategoricalPullback_card_eq_two :
    Fintype.card exampleCategoricalPullback = 2 := by
  -- The reconstruction equivalence identifies pullback objects with the two elements of `ZMod 2`.
  simpa [exampleTwoArrowGroup] using
    (Fintype.card_congr exampleCategoricalPullbackEquivGroup)

/-- Helper for Example 4.32.4: every morphism in the one-point discrete category is the unique
identity morphism. -/
private theorem exampleOnePointCategory_hom_subsingleton
    {X Y : exampleOnePointCategory} (f g : X ⟶ Y) :
    f = g := by
  -- The discrete one-point category has no nontrivial morphism choices.
  exact Subsingleton.elim f g

-- Proof sketch: any morphism in the categorical pullback has identity first and second
-- components, so the compatibility condition forces equality of the comparison isomorphisms;
-- the object-reconstruction theorem then identifies the endpoints.
/-- A morphism in the categorical pullback forces its source and target objects to coincide. -/
private theorem exampleCategoricalPullback_eq_of_hom
    {P Q : exampleCategoricalPullback} (f : P ⟶ Q) :
    P = Q := by
  have hf_fst : exampleOnePointToTwoArrowGroupoid.map f.fst = 𝟙 _ :=
    by simp [exampleOnePointToTwoArrowGroupoid]
  have hf_snd : exampleOnePointToTwoArrowGroupoid.map f.snd = 𝟙 _ :=
    by simp [exampleOnePointToTwoArrowGroupoid]
  have hhom :
      P.iso.hom = Q.iso.hom := by
    simpa [hf_fst, hf_snd] using f.w.symm
  calc
    P = exampleCategoricalPullbackFromArrow P.iso.hom := by
      symm
      exact exampleCategoricalPullback_from_hom P
    _ = exampleCategoricalPullbackFromArrow Q.iso.hom := by
      simp [hhom]
    _ = Q := exampleCategoricalPullback_from_hom Q

private instance : IsDiscrete exampleCategoricalPullback where
  subsingleton _ _ := by
    -- Morphisms are determined by their two components, and each component lives in a one-point
    -- discrete category.
    refine ⟨fun f g ↦ ?_⟩
    apply CategoricalPullback.hom_ext
    · exact Subsingleton.elim _ _
    · exact Subsingleton.elim _ _
  eq_of_hom := exampleCategoricalPullback_eq_of_hom

/-- Example 4.32.4 (1): the categorical pullback of the cospan
`exampleOnePointToTwoArrowGroupoid, exampleOnePointToTwoArrowGroupoid` is discrete. -/
instance example_categorical_pullback_isDiscrete :
    IsDiscrete (exampleOnePointToTwoArrowGroupoid ⊡ exampleOnePointToTwoArrowGroupoid) := by
  change IsDiscrete exampleCategoricalPullback
  infer_instance

/-- Example 4.32.4 (2): viewed as an ordinary categorical pullback, the pullback of the one-point
category with itself over the one-object two-arrow groupoid has exactly two objects. -/
theorem example_categorical_pullback_card_eq_two :
    Fintype.card (exampleOnePointToTwoArrowGroupoid ⊡ exampleOnePointToTwoArrowGroupoid) = 2 := by
  simpa using exampleCategoricalPullback_card_eq_two

-- Proof sketch: in the `2`-fibre product over `exampleTwoArrowGroupoid`, the comparison
-- isomorphism lives in the fibre of the identity functor over the unique base object, so it must
-- be the identity; hence the resulting category has a unique object.
/-- Helper for Example 4.32.4: every object of the explicit pullback over the one-object
two-arrow groupoid is the canonical point. -/
private theorem exampleCategoryOverPullback_eq_point
    (P : exampleCategoryOverPullback) :
    P = exampleCategoryOverPullbackPoint := by
  -- Collapse the base object and the two fibre objects to the unique choices available in the
  -- one-point categories.
  cases P with
  | mk U obj =>
      cases obj with
      | mk fst snd iso =>
          cases fst with
          | mk x hx =>
              cases snd with
              | mk y hy =>
                  have hxobj : x = exampleOnePointObject := by
                    cases x
                    rfl
                  have hyobj : y = exampleOnePointObject := by
                    cases y
                    rfl
                  cases hxobj
                  cases hyobj
                  cases hx
                  cases hy
                  -- The remaining comparison isomorphism lies in the fibre of the identity functor,
                  -- so its underlying arrow is forced to be the identity.
                  have hhom_val : iso.hom.1 = 𝟙 _ := by
                    let h :=
                      @CategoryTheory.IsHomLift.eq_of_isHomLift
                        _ _ _ _ (𝟭 exampleTwoArrowGroupoid) _ _
                        (𝟙 exampleBaseObject) iso.hom.1 iso.hom.2
                    simpa using
                      h.symm
                  have hhom : iso.hom = 𝟙 _ := by
                    apply Functor.Fiber.hom_ext
                    exact hhom_val
                  have hiso : iso = Iso.refl _ := by
                    ext
                    simpa using congrArg Subtype.val hhom
                  cases hiso
                  rfl

private instance : Subsingleton exampleCategoryOverPullback := by
  refine ⟨fun P Q ↦ ?_⟩
  -- Every object identifies with the canonical point, so the whole object type is a subsingleton.
  exact (exampleCategoryOverPullback_eq_point P).trans (exampleCategoryOverPullback_eq_point Q).symm

/-- The `2`-fibre product in `Cat/exampleTwoArrowGroupoid` has a unique object. -/
private noncomputable instance : Unique exampleCategoryOverPullback :=
  uniqueOfSubsingleton exampleCategoryOverPullbackPoint

/-- The `2`-fibre product in `Cat/exampleTwoArrowGroupoid` has finitely many objects. -/
private noncomputable instance :
    Fintype exampleCategoryOverPullback :=
  inferInstance

/-- Example 4.32.4 (3): in `Cat/exampleTwoArrowGroupoid`, the canonical `2`-fibre product of the
one-point category with itself has a unique object. -/
noncomputable instance example_category_over_pullback_unique :
    Unique
      ((explicitTwoFibreProduct
        exampleOnePointOverGroupoid.toBase
        exampleOnePointOverGroupoid.toBase).obj) := by
  change Unique exampleCategoryOverPullback
  infer_instance

-- Proof sketch: in the pullback over the base groupoid, the comparison isomorphism must lie over
-- the identity of the unique base object, so the only possible comparison arrow is the identity;
-- hence there is only one object.
/-- The pullback construction in `Cat/exampleTwoArrowGroupoid` for Example 4.32.4 has exactly one
object. -/
private theorem exampleCategoryOverPullback_card_eq_one :
    Fintype.card exampleCategoryOverPullback = 1 := by
  -- Once the pullback category has a unique object, its object cardinality is immediately `1`.
  simp

/-- Example 4.32.4 (4): viewed as the canonical `2`-fibre product in `Cat/exampleTwoArrowGroupoid`,
the pullback of the one-point category with itself has exactly one object. -/
theorem example_category_over_pullback_card_eq_one :
    Fintype.card
      ((explicitTwoFibreProduct
        exampleOnePointOverGroupoid.toBase
        exampleOnePointOverGroupoid.toBase).obj) = 1 := by
  simpa only [exampleCategoryOverPullback] using exampleCategoryOverPullback_card_eq_one

-- Proof sketch: the point category is discrete and the only admissible base morphism is the
-- identity, so every morphism in the pullback over the base is forced to be the identity.
private instance : IsDiscrete exampleCategoryOverPullback where
  subsingleton P Q := by
    -- After collapsing both endpoints to the canonical point, morphisms are determined by their
    -- left and right components in the one-point discrete category.
    refine ⟨fun f g ↦ ?_⟩
    have hP : P = exampleCategoryOverPullbackPoint := exampleCategoryOverPullback_eq_point P
    have hQ : Q = exampleCategoryOverPullbackPoint := exampleCategoryOverPullback_eq_point Q
    subst hP
    subst hQ
    change
      CategoryOver.ExplicitTwoFibreProductHom
        exampleOnePointOverGroupoid.toBase
        exampleOnePointOverGroupoid.toBase
        exampleCategoryOverPullbackPoint
        exampleCategoryOverPullbackPoint at f g
    cases f
    cases g
    apply ExplicitTwoFibreProductHom.ext
    · exact exampleOnePointCategory_hom_subsingleton _ _
    · exact exampleOnePointCategory_hom_subsingleton _ _
  eq_of_hom := fun {_ _} _ ↦ Subsingleton.elim _ _

/-- Helper for Example 4.32.4: an equivalence between finite discrete categories preserves the
number of objects. -/
private theorem card_eq_of_discrete_equivalence
    {C D : Type*} [Category C] [Category D] [Fintype C] [Fintype D]
    [IsDiscrete C] [IsDiscrete D] (e : C ≌ D) :
    Fintype.card C = Fintype.card D := by
  -- In a discrete category, the unit and counit isomorphisms identify the inverse object maps as
  -- actual inverse functions.
  let h : C ≃ D :=
    { toFun := e.functor.obj
      invFun := e.inverse.obj
      left_inv := fun X ↦ (IsDiscrete.eq_of_hom (e.unitIso.app X).hom).symm
      right_inv := fun Y ↦ IsDiscrete.eq_of_hom (e.counitIso.app Y).hom }
  exact Fintype.card_congr h

/-- Example 4.32.4 (5): in `Cat/exampleTwoArrowGroupoid`, the canonical `2`-fibre product of the
one-point category with itself is discrete. -/
instance example_category_over_pullback_isDiscrete :
    IsDiscrete
      ((explicitTwoFibreProduct
        exampleOnePointOverGroupoid.toBase
        exampleOnePointOverGroupoid.toBase).obj) := by
  change IsDiscrete exampleCategoryOverPullback
  infer_instance

-- Proof sketch: equivalences preserve the cardinality of the object type. The categorical
-- pullback has two objects by `exampleCategoricalPullback_card_eq_two`, while the pullback in
-- `Cat/exampleTwoArrowGroupoid` has one object by `exampleCategoryOverPullback_card_eq_one`.
/-- Example 4.32.4 (6): the `2`-fibre product of the one-point discrete category with itself over the
one-object two-arrow groupoid depends on whether we form it as a pullback of categories or as a
pullback in `Cat/exampleTwoArrowGroupoid`; the two resulting categories are not equivalent. -/
theorem example_two_fibre_product_constructions_not_equivalent :
    ¬ Nonempty
        (exampleOnePointToTwoArrowGroupoid ⊡ exampleOnePointToTwoArrowGroupoid ≌
          (explicitTwoFibreProduct
            exampleOnePointOverGroupoid.toBase
            exampleOnePointOverGroupoid.toBase).obj) := by
  rintro ⟨e⟩
  -- An equivalence of these discrete categories would force their object types to have the same
  -- finite cardinality, contradicting the computations `2` and `1` above.
  have hcard :
      Fintype.card (exampleOnePointToTwoArrowGroupoid ⊡ exampleOnePointToTwoArrowGroupoid) =
        Fintype.card
          ((explicitTwoFibreProduct
            exampleOnePointOverGroupoid.toBase
            exampleOnePointOverGroupoid.toBase).obj) :=
    card_eq_of_discrete_equivalence e
  rw [example_categorical_pullback_card_eq_two, example_category_over_pullback_card_eq_one] at hcard
  omega

end CategoryTheory

/-! ### Lemma_4_32_5 (from Chap04) -/
open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open BasedNatIso
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback

universe u v uX uY uS

namespace CategoryTheory
namespace CategoryOver

/- Domain-style sampling for Lemma 4.32.5:
- primary domain: categories over a fixed base, standard fibres, and the source-facing `2`-fibre
  product over `C`;
- sampled owner-level declarations:
  `BasedCategory`,
  `BasedFunctor.fiberFunctor`,
  `Functor.Fiber`,
  `CategoricalPullback`,
  `CategoricalPullback.CatCommSqOver`;
- best owner abstraction: the source-facing over-`C` pullback is the explicit category whose
  objects are base points `U : C` together with fibrewise pullback objects
  `CategoricalPullback (F.fiberFunctor U) (G.fiberFunctor U)`;
- primitive data: the based functors `F : X ⥤ᵇ S` and `G : Y ⥤ᵇ S`;
- derived API: the bundled category over `C`, its two projection functors, its comparison
  isomorphism over `S`, and the fibrewise equivalence over a fixed `U`.

Source/core/bridge triage:
- `source-facing`: `ExplicitTwoFibreProductObject`, `ExplicitTwoFibreProductHom`, and
  `explicitTwoFibreProduct`;
- `core/canonical`: `Functor.Fiber`, `BasedFunctor.fiberFunctor`, and `CategoricalPullback`;
- `bridge/view`: `explicitTwoFibreProductSquareOver` and
  `fibreOfPullback_equiv_pullbackOfFibres`. -/

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{v, uX} C}
variable {Y : BasedCategory.{v, uY} C}
variable {S : BasedCategory.{v, uS} C}
variable (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)

/-- An object of the explicit `2`-fibre product over `C` is a base object `U : C` together with
an object of the fibrewise categorical pullback `X_U ×_{S_U} Y_U`. -/
structure ExplicitTwoFibreProductObject where
  /-- The chosen base object `U` of `C`. -/
  U : C
  /-- The canonical pullback object `(x, y, f)` in the fibre categories over `U`. -/
  obj : CategoricalPullback (F.fiberFunctor U) (G.fiberFunctor U)

namespace ExplicitTwoFibreProductObject

/-- The canonical comparison morphism in `S` carried by an object of the explicit `2`-fibre
product. -/
abbrev comparison
    (P : ExplicitTwoFibreProductObject F G) :
    F.obj P.obj.fst.1 ⟶ G.obj P.obj.snd.1 :=
  match P with
  | ⟨_, ⟨_, _, i⟩⟩ => i.hom.1

/-- The canonical comparison morphism of an explicit `2`-fibre-product object lies over the
identity of the chosen base object. -/
theorem comparison_over
    (P : ExplicitTwoFibreProductObject F G) :
    S.p.IsHomLift (𝟙 P.U) P.comparison :=
  match P with
  | ⟨_, ⟨_, _, i⟩⟩ => i.hom.2

end ExplicitTwoFibreProductObject

/-- A morphism in the explicit `2`-fibre product is a pair of morphisms in `X` and `Y`
lying over a common base morphism in `C` and compatible with the comparison isomorphisms in `S`. -/
structure ExplicitTwoFibreProductHom
    (P Q : ExplicitTwoFibreProductObject F G) where
  /-- The common base morphism in `C`. -/
  base : P.U ⟶ Q.U
  /-- The morphism on the `X`-component. -/
  a : P.obj.fst.1 ⟶ Q.obj.fst.1
  /-- The `X`-component lies over the common base morphism. -/
  a_over : X.p.IsHomLift base a
  /-- The morphism on the `Y`-component. -/
  b : P.obj.snd.1 ⟶ Q.obj.snd.1
  /-- The `Y`-component lies over the same common base morphism. -/
  b_over : Y.p.IsHomLift base b
  /-- The square relating `F(a)` and `G(b)` commutes. -/
  comm : CommSq (F.toFunctor.map a) P.comparison Q.comparison (G.toFunctor.map b)

attribute [instance] ExplicitTwoFibreProductHom.a_over ExplicitTwoFibreProductHom.b_over

namespace ExplicitTwoFibreProductHom

/-- Morphisms in the explicit `2`-fibre product are determined by their two fibrewise
components. The common base arrow is forced by either lift condition. -/
@[ext] theorem ext
    {P Q : ExplicitTwoFibreProductObject F G}
    (φ ψ : ExplicitTwoFibreProductHom F G P Q)
    (ha : φ.a = ψ.a) (hb : φ.b = ψ.b) :
    φ = ψ := by
  have hbase : φ.base = ψ.base := by
    calc
      φ.base =
          eqToHom P.obj.fst.2.symm ≫ X.p.map φ.a ≫ eqToHom Q.obj.fst.2 :=
        IsHomLift.fac X.p φ.base φ.a
      _ = eqToHom P.obj.fst.2.symm ≫ X.p.map ψ.a ≫ eqToHom Q.obj.fst.2 := by
          simp [ha]
      _ = ψ.base := by simpa using (IsHomLift.fac X.p ψ.base ψ.a).symm
  cases φ
  cases ψ
  cases hbase
  cases ha
  cases hb
  rfl

end ExplicitTwoFibreProductHom

/-- The defining square for the identity morphism in the explicit `2`-fibre product commutes. -/
private theorem explicitTwoFibreProductHom_id_comm
    (P : ExplicitTwoFibreProductObject F G) :
    CommSq
      (F.toFunctor.map (𝟙 P.obj.fst.1))
      P.comparison
      P.comparison
      (G.toFunctor.map (𝟙 P.obj.snd.1)) := by
  refine ⟨?_⟩
  simp [ExplicitTwoFibreProductObject.comparison]

/-- The identity morphism in the explicit `2`-fibre product. -/
private def explicitTwoFibreProductHom_id
    (P : ExplicitTwoFibreProductObject F G) :
    ExplicitTwoFibreProductHom F G P P :=
  { base := 𝟙 P.U
    a := 𝟙 P.obj.fst.1
    a_over := IsHomLift.id P.obj.fst.2
    b := 𝟙 P.obj.snd.1
    b_over := IsHomLift.id P.obj.snd.2
    comm := explicitTwoFibreProductHom_id_comm F G P }

/-- The defining square remains commutative after composing two morphisms in the explicit
`2`-fibre product. -/
private theorem explicitTwoFibreProductHom_comp_comm
    {P Q R : ExplicitTwoFibreProductObject F G}
    (φ : ExplicitTwoFibreProductHom F G P Q)
    (ψ : ExplicitTwoFibreProductHom F G Q R) :
    CommSq (F.toFunctor.map (φ.a ≫ ψ.a)) P.comparison R.comparison
      (G.toFunctor.map (φ.b ≫ ψ.b)) := by
  simpa [Functor.map_comp] using CommSq.horiz_comp φ.comm ψ.comm

/-- Composition in the explicit `2`-fibre product. -/
private def explicitTwoFibreProductHom_comp
    {P Q R : ExplicitTwoFibreProductObject F G}
    (φ : ExplicitTwoFibreProductHom F G P Q)
    (ψ : ExplicitTwoFibreProductHom F G Q R) :
    ExplicitTwoFibreProductHom F G P R :=
  { base := φ.base ≫ ψ.base
    a := φ.a ≫ ψ.a
    a_over := by infer_instance
    b := φ.b ≫ ψ.b
    b_over := by infer_instance
    comm := explicitTwoFibreProductHom_comp_comm F G φ ψ }

/-- Left identity for the explicit `2`-fibre-product composition law. -/
private theorem explicitTwoFibreProductHom_id_comp
    {P Q : ExplicitTwoFibreProductObject F G}
    (φ : ExplicitTwoFibreProductHom F G P Q) :
    explicitTwoFibreProductHom_comp F G (explicitTwoFibreProductHom_id F G P) φ = φ := by
  apply ExplicitTwoFibreProductHom.ext
  · simp [explicitTwoFibreProductHom_comp, explicitTwoFibreProductHom_id]
  · simp [explicitTwoFibreProductHom_comp, explicitTwoFibreProductHom_id]

/-- Right identity for the explicit `2`-fibre-product composition law. -/
private theorem explicitTwoFibreProductHom_comp_id
    {P Q : ExplicitTwoFibreProductObject F G}
    (φ : ExplicitTwoFibreProductHom F G P Q) :
    explicitTwoFibreProductHom_comp F G φ (explicitTwoFibreProductHom_id F G Q) = φ := by
  apply ExplicitTwoFibreProductHom.ext
  · simp [explicitTwoFibreProductHom_comp, explicitTwoFibreProductHom_id]
  · simp [explicitTwoFibreProductHom_comp, explicitTwoFibreProductHom_id]

/-- Associativity for the explicit `2`-fibre-product composition law. -/
private theorem explicitTwoFibreProductHom_assoc
    {P Q R T : ExplicitTwoFibreProductObject F G}
    (φ : ExplicitTwoFibreProductHom F G P Q)
    (ψ : ExplicitTwoFibreProductHom F G Q R)
    (χ : ExplicitTwoFibreProductHom F G R T) :
    explicitTwoFibreProductHom_comp F G (explicitTwoFibreProductHom_comp F G φ ψ) χ =
      explicitTwoFibreProductHom_comp F G φ (explicitTwoFibreProductHom_comp F G ψ χ) := by
  apply ExplicitTwoFibreProductHom.ext
  · simp [explicitTwoFibreProductHom_comp]
  · simp [explicitTwoFibreProductHom_comp]

/-- The objects and morphisms described in Lemma 4.32.5 form a category. -/
instance explicitTwoFibreProductCategory :
    Category (ExplicitTwoFibreProductObject F G) where
  Hom P Q := ExplicitTwoFibreProductHom F G P Q
  id := explicitTwoFibreProductHom_id F G
  comp φ ψ := explicitTwoFibreProductHom_comp F G φ ψ
  id_comp := explicitTwoFibreProductHom_id_comp F G
  comp_id := explicitTwoFibreProductHom_comp_id F G
  assoc φ ψ χ := explicitTwoFibreProductHom_assoc F G φ ψ χ

/-- The projection from the explicit `2`-fibre product to the base category `C`. -/
private abbrev explicitTwoFibreProductBaseFunctor :
    ExplicitTwoFibreProductObject F G ⥤ C :=
  { obj := fun P ↦ P.U
    map := fun φ ↦ φ.base
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }

/-- The projection from the explicit `2`-fibre product to the left total category. -/
private abbrev explicitTwoFibreProductLeftFunctor :
    ExplicitTwoFibreProductObject F G ⥤ X.obj :=
  { obj := fun P ↦ P.obj.fst.1
    map := fun φ ↦ φ.a
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }

/-- The projection from the explicit `2`-fibre product to the right total category. -/
private abbrev explicitTwoFibreProductRightFunctor :
    ExplicitTwoFibreProductObject F G ⥤ Y.obj :=
  { obj := fun P ↦ P.obj.snd.1
    map := fun φ ↦ φ.b
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }

/-- The left projection composed with the structure map to `C` recovers the base projection of
the explicit `2`-fibre product. -/
private theorem explicitTwoFibreProductLeftFunctor_comm :
    explicitTwoFibreProductLeftFunctor F G ⋙ X.p =
      explicitTwoFibreProductBaseFunctor F G := by
  exact Functor.ext (fun P ↦ P.obj.fst.2) (fun P Q φ ↦ by
    simpa using (IsHomLift.fac' X.p φ.base φ.a))

/-- The right projection composed with the structure map to `C` recovers the base projection of
the explicit `2`-fibre product. -/
private theorem explicitTwoFibreProductRightFunctor_comm :
    explicitTwoFibreProductRightFunctor F G ⋙ Y.p =
      explicitTwoFibreProductBaseFunctor F G := by
  exact Functor.ext (fun P ↦ P.obj.snd.2) (fun P Q φ ↦ by
    simpa using (IsHomLift.fac' Y.p φ.base φ.b))

/-- The canonical comparison isomorphism `F ∘ p ≅ G ∘ q` on the explicit `2`-fibre product. -/
private def explicitTwoFibreProductComparisonNatIso :
    explicitTwoFibreProductLeftFunctor F G ⋙ F.toFunctor ≅
      explicitTwoFibreProductRightFunctor F G ⋙ G.toFunctor :=
  NatIso.ofComponents
    (fun P ↦
      (fiberInclusion : Functor.Fiber S.p P.U ⥤ S.obj).mapIso P.obj.iso)
    (fun {_ _} φ ↦ φ.comm.w)

/-- The explicit `2`-fibre product over `C`, with objects given by a base point `U` and an object
of the pullback of the fibre categories over `U`. -/
abbrev explicitTwoFibreProduct
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :=
  BasedCategory.ofFunctor (explicitTwoFibreProductBaseFunctor F G)

/-- The left projection from the explicit `2`-fibre product in `Cat/C`. -/
abbrev explicitTwoFibreProductLeftProjection
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    explicitTwoFibreProduct F G ⥤ᵇ X :=
  { toFunctor := explicitTwoFibreProductLeftFunctor F G
    w := explicitTwoFibreProductLeftFunctor_comm F G }

/-- The right projection from the explicit `2`-fibre product in `Cat/C`. -/
abbrev explicitTwoFibreProductRightProjection
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    explicitTwoFibreProduct F G ⥤ᵇ Y :=
  { toFunctor := explicitTwoFibreProductRightFunctor F G
    w := explicitTwoFibreProductRightFunctor_comm F G }

noncomputable section

/-- The canonical comparison isomorphism over `C` on the explicit `2`-fibre product. -/
def explicitTwoFibreProductComparisonIsoOver :
    explicitTwoFibreProductLeftProjection F G ⋙ F ≅
      explicitTwoFibreProductRightProjection F G ⋙ G :=
  BasedNatIso.mkNatIso
    (explicitTwoFibreProductComparisonNatIso F G)
    (fun P ↦ by
      simpa [explicitTwoFibreProduct] using P.comparison_over)

/-- The ordinary categorical square underlying the explicit `2`-fibre product over `C`. This is
the canonical bridge from the source-facing based pullback owner to the chapter's categorical
pullback-square owner `CategoricalPullback.CatCommSqOver`. -/
abbrev explicitTwoFibreProductSquareOver :
    CategoricalPullback.CatCommSqOver F.toFunctor G.toFunctor (explicitTwoFibreProduct F G).obj
    where
  fst := (explicitTwoFibreProductLeftProjection F G).toFunctor
  snd := (explicitTwoFibreProductRightProjection F G).toFunctor
  iso := (BasedNatTrans.forgetful _ _).mapIso (explicitTwoFibreProductComparisonIsoOver F G)

/-- The compatibility square in `S` induced by a morphism in the pullback of fibres. -/
private theorem pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct_comm
    {U : C} {P Q : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)}
    (φ : P ⟶ Q) :
    CommSq (F.toFunctor.map φ.fst.1) P.iso.hom.1 Q.iso.hom.1 (G.toFunctor.map φ.snd.1) := by
  refine ⟨?_⟩
  convert congrArg Subtype.val φ.w using 1

/-- The pullback of the fibres over `U`, viewed in the total explicit `2`-fibre product over
`C`. -/
private def pullbackOfFibres_to_explicitTwoFibreProduct
    (U : C) :
    (F.fiberFunctor U) ⊡ (G.fiberFunctor U) ⥤ (explicitTwoFibreProduct F G).obj where
  obj P := { U := U, obj := P }
  map φ :=
    { base := 𝟙 U
      a := φ.fst.1
      a_over := φ.fst.2
      b := φ.snd.1
      b_over := φ.snd.2
      comm := pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct_comm F G φ }
  map_id P := by
    apply ExplicitTwoFibreProductHom.ext
    · rfl
    · rfl
  map_comp φ ψ := by
    apply ExplicitTwoFibreProductHom.ext
    · rfl
    · rfl

/-- The canonical comparison functor from the pullback of the fibres over `U` to the fibre over
`U` of the explicit `2`-fibre product over `C`. -/
private abbrev pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct
    (U : C) :
    (F.fiberFunctor U) ⊡ (G.fiberFunctor U) ⥤
      Functor.Fiber (explicitTwoFibreProduct F G).p U :=
  let H := pullbackOfFibres_to_explicitTwoFibreProduct F G U
  have hH :
      H ⋙ (explicitTwoFibreProduct F G).p =
        (Functor.const ((F.fiberFunctor U) ⊡ (G.fiberFunctor U))).obj U := rfl
  Functor.Fiber.inducedFunctor hH

/-- Helper for Lemma 4.32.5: an object of the fibre of the explicit pullback over `U` already
stores an object of the pullback of the fibre categories over `U`. -/
private def fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_obj
    (U : C) :
    Functor.Fiber (explicitTwoFibreProduct F G).p U →
      ((F.fiberFunctor U) ⊡ (G.fiberFunctor U))
  | ⟨⟨_, P⟩, rfl⟩ => P

/-- Helper for Lemma 4.32.5: the left component of a fibre morphism in the explicit pullback lies
over the identity of `U`. -/
private theorem fibreOfExplicitTwoFibreProduct_left_over_id
    {U : C} {P Q : Functor.Fiber (explicitTwoFibreProduct F G).p U}
    (φ : P ⟶ Q) :
    X.p.IsHomLift (𝟙 U) φ.1.a := by
  -- After normalizing the objects of the outer fibre, the lift over `𝟙 U` becomes definitional.
  cases P with
  | mk P hP =>
      cases Q with
      | mk Q hQ =>
          cases P with
          | mk UP Pobj =>
              cases Q with
              | mk UQ Qobj =>
                  cases hP
                  cases hQ
                  letI : (explicitTwoFibreProduct F G).p.IsHomLift (𝟙 UP) φ.1 := φ.2
                  have hbase : φ.1.base = 𝟙 UP := by
                    simpa [explicitTwoFibreProduct] using
                      (IsHomLift.fac' ((explicitTwoFibreProduct F G).p) (𝟙 UP) φ.1)
                  simpa [hbase, explicitTwoFibreProduct] using φ.1.a_over

/-- Helper for Lemma 4.32.5: the right component of a fibre morphism in the explicit pullback
lies over the identity of `U`. -/
private theorem fibreOfExplicitTwoFibreProduct_right_over_id
    {U : C} {P Q : Functor.Fiber (explicitTwoFibreProduct F G).p U}
    (φ : P ⟶ Q) :
    Y.p.IsHomLift (𝟙 U) φ.1.b := by
  -- The right component is handled by the same outer-fibre normalization.
  cases P with
  | mk P hP =>
      cases Q with
      | mk Q hQ =>
          cases P with
          | mk UP Pobj =>
              cases Q with
              | mk UQ Qobj =>
                  cases hP
                  cases hQ
                  letI : (explicitTwoFibreProduct F G).p.IsHomLift (𝟙 UP) φ.1 := φ.2
                  have hbase : φ.1.base = 𝟙 UP := by
                    simpa [explicitTwoFibreProduct] using
                      (IsHomLift.fac' ((explicitTwoFibreProduct F G).p) (𝟙 UP) φ.1)
                  simpa [hbase, explicitTwoFibreProduct] using φ.1.b_over

/-- Helper for Lemma 4.32.5: the left component of a fibre morphism gives the left morphism in
the pullback of fibres. -/
private def fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_fst
    {U : C} {P Q : Functor.Fiber (explicitTwoFibreProduct F G).p U}
    (φ : P ⟶ Q) :
    (fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_obj F G U P).fst ⟶
      (fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_obj F G U Q).fst :=
  match P, Q, φ with
  | ⟨⟨_, P⟩, rfl⟩, ⟨⟨_, Q⟩, rfl⟩, φ =>
      ⟨φ.1.a, fibreOfExplicitTwoFibreProduct_left_over_id F G φ⟩

/-- Helper for Lemma 4.32.5: the right component of a fibre morphism gives the right morphism in
the pullback of fibres. -/
private def fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_snd
    {U : C} {P Q : Functor.Fiber (explicitTwoFibreProduct F G).p U}
    (φ : P ⟶ Q) :
    (fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_obj F G U P).snd ⟶
      (fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_obj F G U Q).snd :=
  match P, Q, φ with
  | ⟨⟨_, P⟩, rfl⟩, ⟨⟨_, Q⟩, rfl⟩, φ =>
      ⟨φ.1.b, fibreOfExplicitTwoFibreProduct_right_over_id F G φ⟩

/-- Helper for Lemma 4.32.5: the two induced fibre morphisms still satisfy the pullback
compatibility equation. -/
private theorem fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_map_w
    {U : C} {P Q : Functor.Fiber (explicitTwoFibreProduct F G).p U}
    (φ : P ⟶ Q) :
    (F.fiberFunctor U).map (fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_fst F G φ) ≫
        (fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_obj F G U Q).iso.hom =
      (fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_obj F G U P).iso.hom ≫
        (G.fiberFunctor U).map (fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_snd F G φ) := by
  -- After normalizing the outer fibre equalities, this is exactly the compatibility square of
  -- the explicit pullback morphism.
  cases P with
  | mk P hP =>
      cases Q with
      | mk Q hQ =>
          cases P with
          | mk UP Pobj =>
              cases Q with
              | mk UQ Qobj =>
                  cases hP
                  cases hQ
                  apply Functor.Fiber.hom_ext
                  simpa using φ.1.comm.w

/-- Helper for Lemma 4.32.5: a fibre morphism in the explicit pullback induces a morphism in the
pullback of the fibre categories over `U`. -/
private def fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_map
    {U : C} {P Q : Functor.Fiber (explicitTwoFibreProduct F G).p U}
    (φ : P ⟶ Q) :
    fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_obj F G U P ⟶
      fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_obj F G U Q :=
  match P, Q, φ with
  | ⟨⟨_, P⟩, rfl⟩, ⟨⟨_, Q⟩, rfl⟩, φ =>
      { fst := fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_fst F G φ
        snd := fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_snd F G φ
        w := fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_map_w F G φ }

/-- Helper for Lemma 4.32.5: the inverse functor on fibres preserves identities. -/
private theorem fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_map_id
    {U : C} (P : Functor.Fiber (explicitTwoFibreProduct F G).p U) :
    fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_map F G (𝟙 P) =
      𝟙 (fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_obj F G U P) := by
  -- After normalizing the outer fibre equality, the induced morphism is definitionally the
  -- identity on each fibre component.
  cases P with
  | mk P hP =>
      cases P with
      | mk UP Pobj =>
          cases hP
          apply CategoricalPullback.hom_ext
          · apply Functor.Fiber.hom_ext
            rfl
          · apply Functor.Fiber.hom_ext
            rfl

/-- Helper for Lemma 4.32.5: the inverse functor on fibres preserves composition. -/
private theorem fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_map_comp
    {U : C}
    {P Q R : Functor.Fiber (explicitTwoFibreProduct F G).p U}
    (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_map F G (φ ≫ ψ) =
      fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_map F G φ ≫
        fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_map F G ψ := by
  -- After reducing the outer fibre equalities, composition is componentwise in the pullback.
  cases P with
  | mk P hP =>
      cases Q with
      | mk Q hQ =>
          cases R with
          | mk R hR =>
              cases P with
              | mk UP Pobj =>
                  cases Q with
                  | mk UQ Qobj =>
                      cases R with
                      | mk UR Robj =>
                          cases hP
                          cases hQ
                          cases hR
                          apply CategoricalPullback.hom_ext
                          · apply Functor.Fiber.hom_ext
                            rfl
                          · apply Functor.Fiber.hom_ext
                            rfl

/-- Helper for Lemma 4.32.5: forgetting the redundant outer fibre equality gives the concrete
quasi-inverse from the fibre of the explicit pullback to the pullback of fibres. -/
private def fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres
    (U : C) :
    Functor.Fiber (explicitTwoFibreProduct F G).p U ⥤
      ((F.fiberFunctor U) ⊡ (G.fiberFunctor U)) where
  obj := fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_obj F G U
  map := fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_map F G
  map_id := fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_map_id F G
  map_comp := fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_map_comp F G

/-- Helper for Lemma 4.32.5: the canonical functor from the pullback of fibres and the concrete
quasi-inverse compose to the identity on the pullback of fibres. -/
private theorem pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct_comp_inverse
    (U : C) :
    pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct F G U ⋙
        fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres F G U =
      𝟭 ((F.fiberFunctor U) ⊡ (G.fiberFunctor U)) := by
  -- Route correction: use heterogeneous functor extensionality to avoid all `eqToHom`
  -- transports in the morphism clause.
  refine Functor.hext (fun P ↦ rfl) ?_
  intro P Q φ
  cases P
  cases Q
  rfl

/-- Helper for Lemma 4.32.5: the concrete quasi-inverse followed by the canonical functor back to
the outer fibre is the identity on that fibre. -/
private theorem fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_comp_forward
    (U : C) :
    fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres F G U ⋙
        pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct F G U =
      𝟭 (Functor.Fiber (explicitTwoFibreProduct F G).p U) := by
  refine Functor.hext
    (fun P ↦ by
      cases P with
      | mk P hP =>
          cases P with
          | mk UP Pobj =>
              cases hP
              rfl)
    ?_
  intro P Q φ
  cases P with
  | mk P hP =>
      cases Q with
      | mk Q hQ =>
          cases P with
          | mk UP Pobj =>
              cases Q with
              | mk UQ Qobj =>
                  cases hP
                  cases hQ
                  cases Pobj with
                  | mk Pfst Psnd Piso =>
                      cases Qobj with
                      | mk Qfst Qsnd Qiso =>
                          cases Pfst with
                          | mk PX hPX =>
                              cases Psnd with
                              | mk PY hPY =>
                                  cases Qfst with
                                  | mk QX hQX =>
                                      cases Qsnd with
                                      | mk QY hQY =>
                                          have hmap :
                                              (fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres F G
                                                      ((explicitTwoFibreProduct F G).p.obj
                                                        { U := UP
                                                          obj := { fst := ⟨PX, hPX⟩
                                                                   snd := ⟨PY, hPY⟩
                                                                   iso := Piso } }) ⋙
                                                    pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct F G
                                                      ((explicitTwoFibreProduct F G).p.obj
                                                        { U := UP
                                                          obj := { fst := ⟨PX, hPX⟩
                                                                   snd := ⟨PY, hPY⟩
                                                                   iso := Piso } })).map φ =
                                                (𝟭
                                                      ((explicitTwoFibreProduct F G).p.Fiber
                                                        ((explicitTwoFibreProduct F G).p.obj
                                                          { U := UP
                                                            obj := { fst := ⟨PX, hPX⟩
                                                                     snd := ⟨PY, hPY⟩
                                                                     iso := Piso } }))).map φ := by
                                            apply Functor.Fiber.hom_ext
                                            apply ExplicitTwoFibreProductHom.ext
                                            · rfl
                                            · rfl
                                          exact hmap ▸ HEq.rfl

private theorem pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct_isEquivalence
    (U : C) :
    (pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct F G U).IsEquivalence := by
  -- The concrete quasi-inverse is obtained by deleting the redundant outer fibre equality.
  let H := fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres F G U
  have hη :
      pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct F G U ⋙ H =
        𝟭 ((F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :=
    pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct_comp_inverse F G U
  have hε :
      H ⋙ pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct F G U =
        𝟭 (Functor.Fiber (explicitTwoFibreProduct F G).p U) :=
    fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_comp_forward F G U
  exact
    Functor.IsEquivalence.mk'
      H
      (eqToIso hη.symm)
      (eqToIso hε)

/-- Lemma 4.32.5: for morphisms of categories over `C`, the fibre over `U` of the explicit
`2`-fibre product category over `C` is canonically equivalent to the pullback of the fibre
categories `X_U ×_{S_U} Y_U`. -/
noncomputable def fibreOfPullback_equiv_pullbackOfFibres
    (U : C) :
    Functor.Fiber (explicitTwoFibreProduct F G).p U ≌
      ((F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :=
  Equivalence.mk
    (fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres F G U)
    (pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct F G U)
    (eqToIso (fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_comp_forward F G U).symm)
    (eqToIso (pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct_comp_inverse F G U))

/-- Helper for Lemma 4.32.5: the forward functor of the packaged equivalence is the concrete
quasi-inverse obtained by forgetting the redundant outer fibre equality. -/
private theorem fibreOfPullback_equiv_pullbackOfFibres_functor
    (U : C) :
    (fibreOfPullback_equiv_pullbackOfFibres F G U).functor =
      fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres F G U := by
  -- Unfolding the packaged equivalence exposes the chosen quasi-inverse as its forward functor.
  rfl

-- Proof sketch: the equivalence is the quasi-inverse of the canonical functor from the pullback
-- of fibres into the fibre of the explicit pullback. Its forward functor therefore recovers the
-- left pullback projection on the nose, which matches the fibre functor induced by the left
-- projection `explicitTwoFibreProductLeftProjection F G`.
/-- The forward functor of `fibreOfPullback_equiv_pullbackOfFibres` composed with the left
projection `π₁` is the fibre functor induced by the left projection of the explicit
`2`-fibre product. -/
theorem fibreOfPullback_equiv_pullbackOfFibres_functor_comp_pi₁
    (U : C) :
    (fibreOfPullback_equiv_pullbackOfFibres F G U).functor ⋙
        π₁ (F.fiberFunctor U) (G.fiberFunctor U) =
      (explicitTwoFibreProductLeftProjection F G).fiberFunctor U := by
  -- The forward functor is the concrete quasi-inverse defined above.
  rw [fibreOfPullback_equiv_pullbackOfFibres_functor F G U]
  refine Functor.hext
    (fun P ↦ by
      cases P with
      | mk P hP =>
          cases P with
          | mk UP Pobj =>
              cases hP
              rfl)
    ?_
  intro P Q φ
  cases P with
  | mk P hP =>
      cases Q with
      | mk Q hQ =>
          cases P with
          | mk UP Pobj =>
              cases Q with
              | mk UQ Qobj =>
                  cases hP
                  cases hQ
                  rfl

-- Proof sketch: this is the right-hand analogue of
-- `fibreOfPullback_equiv_pullbackOfFibres_functor_comp_pi₁`. The forward functor of the
-- equivalence forgets to the `Y`-component exactly as the fibre functor induced by the right
-- projection `explicitTwoFibreProductRightProjection F G`.
/-- The forward functor of `fibreOfPullback_equiv_pullbackOfFibres` composed with the right
projection `π₂` is the fibre functor induced by the right projection of the explicit
`2`-fibre product. -/
theorem fibreOfPullback_equiv_pullbackOfFibres_functor_comp_pi₂
    (U : C) :
    (fibreOfPullback_equiv_pullbackOfFibres F G U).functor ⋙
        π₂ (F.fiberFunctor U) (G.fiberFunctor U) =
      (explicitTwoFibreProductRightProjection F G).fiberFunctor U := by
  -- The same concrete quasi-inverse forgets to the right fibre component.
  rw [fibreOfPullback_equiv_pullbackOfFibres_functor F G U]
  refine Functor.hext
    (fun P ↦ by
      cases P with
      | mk P hP =>
          cases P with
          | mk UP Pobj =>
              cases hP
              rfl)
    ?_
  intro P Q φ
  cases P with
  | mk P hP =>
      cases Q with
      | mk Q hQ =>
          cases P with
          | mk UP Pobj =>
              cases Q with
              | mk UQ Qobj =>
                  cases hP
                  cases hQ
                  rfl

end

end CategoryOver
end CategoryTheory
