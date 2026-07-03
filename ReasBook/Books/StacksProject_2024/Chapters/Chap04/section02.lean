import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Groupoid.Discrete
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.ObjectProperty.Small
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Widesubcategory
import Mathlib.Logic.Small.Basic
import Mathlib.Tactic.Recall
import Mathlib.Topology.Sheaves.Sheaf

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_2_1 (from Chap04) -/
universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {X Y Z : C}

/- Domain-style sampling for Definition 4.2.1:
- primary domain: the primitive data and axioms of a category.
- inspected owner declarations: `Quiver.Hom`, `CategoryStruct.id`, `CategoryStruct.comp`,
  and `Category`.
- best owner abstraction: `Category`; its inherited owner stack already carries the textbook data,
  so this file should recall that owner instead of introducing a parallel wrapper.

Primitive-vs-derived split:
- primitive data inherited by the owner stack: hom-types from `Quiver.Hom`, identity morphisms
  from `CategoryStruct.id`, composition from `CategoryStruct.comp`, and the axioms from
  `Category`.
- derived API used on the source-facing surface: the standard notation `X ⟶ Y`, `𝟙 X`, `f ≫ g`,
  together with `Category.id_comp`, `Category.comp_id`, and `Category.assoc`.

Source/core/bridge triage:
- `source-facing`: the textbook hom-set, identity, composition, and three category axioms.
- `core/canonical`: `Category`.
- `bridge/view`: the inherited notation and axiom names exposing the source wording on top of the
  canonical owner stack. -/

/- Definition 4.2.1: a category on the ambient type of objects `C` is the canonical mathlib class
`Category`. The source hom-types, identities, and composition are already the inherited data
`Quiver.Hom`, `CategoryStruct.id`, and `CategoryStruct.comp`, so no parallel local definition is
needed. The left/right identity axioms and associativity are the fields of `Category` itself. -/
recall Category

/- Definition 4.2.1, source hom-set notation: for objects `X Y : C`, the morphisms from `X` to
`Y` form the canonical hom-type `X ⟶ Y`, i.e. the notation for `Quiver.Hom X Y`. -/
#check (X ⟶ Y)

/- Definition 4.2.1, source identity morphism: the identity of an object `X` is the canonical
morphism `𝟙 X`, i.e. the notation for `CategoryStruct.id X`. -/
#check (𝟙 X)

/- Definition 4.2.1, source composition operation: composition of composable morphisms is the
canonical infix operation `≫`, i.e. the notation for `CategoryStruct.comp`. -/
#check fun (f : X ⟶ Y) (g : Y ⟶ Z) ↦ f ≫ g

/- Definition 4.2.1 (1): left identity for composition is the canonical axiom
`Category.id_comp`. -/
recall Category.id_comp

/- Definition 4.2.1 (2): right identity for composition is the canonical axiom
`Category.comp_id`. -/
recall Category.comp_id

/- Definition 4.2.1 (3): associativity of composition is the canonical axiom
`Category.assoc`. -/
recall Category.assoc

end CategoryTheory

/-! ### Remark_4_2_2 (from Chap04) -/
universe u

namespace CategoryTheory

/- Domain-style sampling for Remark 4.2.2:
- primary domain: the source-facing whitelist of ambient large categories used throughout the
  chapter, each expressed through its canonical owner declaration
- sampled canonical declarations:
  `LargeCategory`,
  `Action`,
  `ModuleCat`,
  `TopCat.Sheaf`
- best owner abstraction: this remark is not owned by a single new abstraction; its mathematical
  content is the chapter's explicit roster of allowed large categories, so each listed family
  should be presented directly through its existing canonical owner rather than collapsed to the
  generic size abbreviation alone
- primitive data: the owner categories themselves, together with the local mathematical inputs
  they actually depend on, such as a group `G`, a ring `R`, a small category `C`, a topology `J`,
  or a topological space `X`
- derived API: the inherited `LargeCategory` instances on those owner categories

Source/core/bridge triage for Remark 4.2.2:
- source-facing: the whitelist of ambient large categories explicitly allowed in the text
- core/canonical: the owner declarations for those categories, such as `Action`, `ModuleCat`,
  `Presheaf`, `Sheaf`, `TopCat.Presheaf`, `TopCat.Sheaf`, `TopCat`, and
  `AlgebraicGeometry.Scheme`
- bridge/view: the size-interface checks `LargeCategory (...)` showing that each owner category
  fits the ambient convention
-/

/- Remark 4.2.2 fixes the ambient size convention through the canonical abbreviation
`LargeCategory`, but its source-facing mathematical content is the explicit list of large
categories the chapter allows one to work with. The refined file therefore keeps the generic size
recall only as background and records the listed examples directly through their canonical owner
categories. -/
recall LargeCategory

/- Companion recall: when the source mentions functor, presheaf, and sheaf categories indexed by a
category `C`, the relevant input hypothesis is that `C` is small. -/
recall SmallCategory

/- The basic ambient examples named in the remark are already large through their canonical owner
category instances: sets, abelian groups, groups, rings, topological spaces, and schemes. -/
#check (inferInstance : LargeCategory (Type u))
#check (inferInstance : LargeCategory AddCommGrpCat)
#check (inferInstance : LargeCategory GrpCat)
#check (inferInstance : LargeCategory RingCat)
#check (inferInstance : LargeCategory TopCat)
#check (inferInstance : LargeCategory AlgebraicGeometry.Scheme)

section AlgebraicExamples

variable (G : Type u) [Group G]
variable (R : Type u) [Ring R]
variable (k : Type u) [Field k]

/- The algebraic families listed in the remark use their standard owners: `Action (Type u) G` for
`G`-sets, `ModuleCat R` for `R`-modules, `ModuleCat k` for vector spaces over `k`, and the
project's bundled owner `DividedPowerRing` for divided power rings. -/
#check Action
#check (inferInstance : LargeCategory (Action (Type u) G))
#check ModuleCat
#check (inferInstance : LargeCategory (ModuleCat.{u} R))
#check (inferInstance : LargeCategory (ModuleCat.{u} k))
#check DividedPowerRing
#check (inferInstance : LargeCategory DividedPowerRing)

end AlgebraicExamples

section PresheafAndFunctorExamples

variable (C : Type u) [SmallCategory C]
variable (X : TopCat.{u})

/- The remark also allows the standard large categories built from a small category `C` or a
topological space `X`: set-valued functors on `C`, presheaves of sets on `C`, and presheaves of
sets or abelian groups on `X`. -/
#check (inferInstance : LargeCategory (C ⥤ Type u))
#check Presheaf
#check (inferInstance : LargeCategory (Presheaf.{u, u, u} C))
#check TopCat.Presheaf
#check (inferInstance : LargeCategory (X.Presheaf (Type u)))
#check (inferInstance : LargeCategory (X.Presheaf AddCommGrpCat.{u}))

end PresheafAndFunctorExamples

section SheafExamples

variable (C : Type u) [SmallCategory C]
variable (J : GrothendieckTopology C)
variable (X : TopCat.{u})

/- Finally, the sheaf examples from the remark use the canonical site-level and topological-space
owners for sheaves of sets and of abelian groups. -/
#check Sheaf
#check TopCat.Sheaf
#check (inferInstance : LargeCategory (Sheaf J (Type u)))
#check (inferInstance : LargeCategory (X.Sheaf (Type u)))
#check (inferInstance : LargeCategory (X.Sheaf AddCommGrpCat.{u}))

end SheafExamples

end CategoryTheory

/-! ### Remark_4_2_3 (from Chap04) -/
universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {X : C}

/- Domain-style sampling for Remark 4.2.3:
- primary domain: identity morphisms in an arbitrary category and their uniqueness
- sampled canonical declarations:
  `Category.id_comp`,
  `Category.comp_id`,
  `CategoryTheory.id_of_comp_left_id`,
  `CategoryTheory.id_of_comp_right_id`
- best owner abstraction: the canonical identity morphism `𝟙 X`, with uniqueness expressed by the
  owner lemmas `id_of_comp_left_id` and `id_of_comp_right_id`
- primitive data: the ambient category structure and the canonical identity morphism on `X`
- derived API: the source-facing uniqueness bridge for a left identity and a right identity on `X`

Source/core/bridge triage for Remark 4.2.3:
- source-facing: the Stacks remark that identity morphisms are unique
- core/canonical: `𝟙 X`, `id_of_comp_left_id`, `id_of_comp_right_id`
- bridge/view: `identity_morphism_unique`, which packages the source wording as the canonical
  consequence of those owner lemmas
-/

/- Companion recall: a morphism out of `X` acting as a left identity on all maps with source `X`
is the canonical identity `𝟙 X`; this is the owner lemma `id_of_comp_left_id`. -/
recall id_of_comp_left_id

/- Companion recall: a morphism into `X` acting as a right identity on all maps with target `X`
is the canonical identity `𝟙 X`; this is the owner lemma `id_of_comp_right_id`. -/
recall id_of_comp_right_id

/-- Remark 4.2.3: any two identity morphisms of an object `X` are equal. Concretely, if `e` acts
as a left identity on all morphisms out of `X` and `e'` acts as a right identity on all morphisms
into `X`, then `e = e'`; hence one may speak of the identity morphism `𝟙 X`. -/
-- Proof sketch: apply `id_of_comp_left_id` to identify `e` with `𝟙 X`, apply
-- `id_of_comp_right_id` to identify `e'` with `𝟙 X`, and compare the two equalities.
theorem identity_morphism_unique {e e' : X ⟶ X}
    (hleft : ∀ {Y : C} (f : X ⟶ Y), e ≫ f = f)
    (hright : ∀ {Y : C} (f : Y ⟶ X), f ≫ e' = f) :
    e = e' := by
  -- First identify the left-identity candidate with the canonical identity morphism.
  have he : e = 𝟙 X := id_of_comp_left_id e hleft
  -- Then identify the right-identity candidate with the same canonical identity morphism.
  have he' : e' = 𝟙 X := id_of_comp_right_id e' hright
  -- Comparing both morphisms through `𝟙 X` gives the desired uniqueness.
  calc
    e = 𝟙 X := he
    _ = e' := he'.symm

end CategoryTheory

/-! ### Definition_4_2_4 (from Chap04) -/
universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X Y : C}

/- Domain-style sampling for Definition 4.2.4 (isomorphisms in a category):
- primary domain: invertible morphisms in an arbitrary category;
- sampled owner declarations: `IsIso`, `IsIso.out`, `IsIso.mk`, `asIso`;
- primitive data: the existence of a two-sided inverse for a morphism;
- derived API: the chosen inverse `inv`, the bundled isomorphism `asIso`, and the inverse
  identities;
- layer triage:
  - `source-facing`: the textbook inverse criterion for a morphism;
  - `core/canonical`: `IsIso`;
  - `bridge/view`: the constructor/field pair `IsIso.mk` and `IsIso.out`, which expose the
    source inverse criterion without introducing a parallel owner. -/

/- Definition 4.2.4: a morphism in a category is an isomorphism precisely when it admits a
two-sided inverse. This source notion is the canonical mathlib predicate `IsIso`. -/
recall IsIso

/- Source-facing inverse criterion, forward direction: from `IsIso f`, the field `IsIso.out`
extracts a morphism `g : Y ⟶ X` with `f ≫ g = 𝟙 X` and `g ≫ f = 𝟙 Y`. -/
recall IsIso.out

/- Source-facing inverse criterion, converse direction: a two-sided inverse for `f` yields the
canonical instance `IsIso f` via `IsIso.mk`. -/
recall IsIso.mk

end CategoryTheory

/-! ### Definition_4_2_5 (from Chap04) -/
universe v u

namespace CategoryTheory

/- Domain-style sampling for Definition 4.2.5:
- primary domain: categorical groupoids;
- sampled owner-level declarations:
  `CategoryTheory.Groupoid`,
  `CategoryTheory.IsGroupoid`,
  `CategoryTheory.Groupoid.ofIsGroupoid`;
- best owner abstraction: the source notion is already owned canonically by `Groupoid` for bundled
  data and `IsGroupoid` for the Prop-valued condition on an existing category;
- primitive owner data: `Groupoid.inv` in the bundled owner and `IsGroupoid.all_isIso` in the
  Prop-valued owner;
- derived API: `Groupoid.ofIsGroupoid` promotes the Prop-valued owner back to bundled data when a
  downstream construction needs bundled inverses.

Source/core/bridge triage:
- `source-facing`: the textbook wording that a groupoid is a category in which every morphism is an
  isomorphism;
- `core/canonical`: `Groupoid` and `IsGroupoid`;
- `bridge/view`: `Groupoid.ofIsGroupoid`, used when a downstream construction needs bundled
  inverses from the Prop-valued owner. -/

/- Definition 4.2.5: a groupoid is a category in which every morphism is an isomorphism; this is
the defining content bundled by the canonical mathlib class `Groupoid`. -/
recall Groupoid

/- Companion recall: for an already given category structure, the condition that every morphism is
an isomorphism is the canonical Prop-valued class `IsGroupoid C`. -/
recall IsGroupoid

end CategoryTheory

/-! ### Example_4_2_6 (from Chap04) -/
namespace CategoryTheory

/- Domain-style sampling for Example 4.2.6:
- primary domain: one-object categories/groupoids attached to algebraic structures;
- sampled owner-level declarations:
  `CategoryTheory.SingleObj`,
  `CategoryTheory.SingleObj.groupoid`,
  `CategoryTheory.SingleObj.functor`,
  `CategoryTheory.Functor.Faithful`,
  `CategoryTheory.Functor.Full`,
  `CategoryTheory.Functor.essSurj_of_surj`,
  `CategoryTheory.Functor.asEquivalence`;
- best owner abstraction: the source example is already owned canonically by the instance
  `SingleObj.groupoid`; the converse is expressed by the owner-level functor
  `SingleObj.functor (MonoidHom.id (End c)) : SingleObj (End c) ⥤ C` together with the canonical
  functor-owner predicates `Faithful`, `Full`, `EssSurj`, and `asEquivalence`;
- primitive data: the group structure on `G`, or equivalently the endomorphism group `End c` of
  the chosen object `c` of a groupoid `C` with subsingleton object type, whose endomorphism group
  is `End c`;
- derived API: the induced groupoid structure on `SingleObj G` and, for a unique-object groupoid,
  the realization equivalence from `SingleObj (End c)` to `C`.

Source/core/bridge triage:
- `source-facing`: a group determines a one-object groupoid, and conversely every one-object
  groupoid comes from the endomorphism group of its unique object;
- `core/canonical`: `SingleObj.groupoid`;
- `bridge/view`: `SingleObj.functor` realizes `SingleObj (End c)` inside a one-object groupoid,
  while `SingleObj.toEnd` identifies the endomorphisms of the model object with the original
  group. -/

/- Example 4.2.6: a group `G` determines the one-object groupoid `SingleObj G` via the canonical
instance `CategoryTheory.SingleObj.groupoid`. -/
recall SingleObj.groupoid

/-- Example 4.2.6 (converse): if a groupoid `C` has subsingleton object type and `c : C` is the
chosen object, then `C` is equivalent to the single-object groupoid attached to `End c`. -/
noncomputable def oneObjectGroupoidEquivSingleObjEnd
    {C : Type*} [Groupoid C] [Subsingleton C] (c : C) : C ≌ SingleObj (End c) :=
  let F := SingleObj.functor (MonoidHom.id (End c))
  letI : F.Faithful :=
    { map_injective := by
        intro X Y f g h
        cases X
        cases Y
        exact h }
  letI : F.Full :=
    { map_surjective := by
        intro X Y f
        cases X
        cases Y
        exact ⟨f, rfl⟩ }
  letI : F.IsEquivalence :=
    { faithful := inferInstance
      full := inferInstance
      essSurj := Functor.essSurj_of_surj fun X ↦
        ⟨SingleObj.star (End c), Subsingleton.elim c X⟩ }
  F.asEquivalence.symm

end CategoryTheory

/-! ### Example_4_2_7 (from Chap04) -/
universe u

namespace CategoryTheory

/- Example 4.2.7: a set `C` gives the discrete groupoid `Discrete C` via the canonical instance
`instGroupoidDiscrete`. Distinct objects have no morphisms between them, and every endomorphism is
the identity. -/
recall instGroupoidDiscrete

/- Domain-style sampling for Example 4.2.7:
- primary domain: discrete categories and groupoids;
- sampled owner-level declarations: `instGroupoidDiscrete`, `Discrete.isDiscrete`,
  `obj_ext_of_isDiscrete`, `Discrete.instSubsingletonDiscreteHom`;
- best owner abstraction: `IsDiscrete (Discrete C)`;
- primitive owner data: `IsDiscrete.eq_of_hom` and the induced subsingleton hom-spaces;
- derived consequences in the source text: distinct objects admit no morphisms, and every
  endomorphism is the identity. These are better used directly from the owner API than via local
  duplicate theorem names.

Source/core/bridge triage:
- `source-facing`: the example-level recall that `Discrete C` is a groupoid with discrete homs;
- `core/canonical`: `instGroupoidDiscrete`, `Discrete.isDiscrete`, `obj_ext_of_isDiscrete`,
  `Discrete.instSubsingletonDiscreteHom`;
- `bridge/view`: none. -/
recall Discrete.isDiscrete

/- Any morphism in `Discrete C` forces equality of its source and target via the owner bridge
`obj_ext_of_isDiscrete`, specialized by `Discrete.isDiscrete`. -/
recall obj_ext_of_isDiscrete

/- Every hom-space in `Discrete C` is a subsingleton, so in particular every endomorphism is the
identity. -/
recall Discrete.instSubsingletonDiscreteHom

end CategoryTheory

/-! ### Definition_4_2_8 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/- Domain-style sampling for Definition 4.2.8:
- primary domain: basic category theory, specifically the owner object for functors between
  categories;
- sampled owner-level declarations:
  `(C ⥤ D)`,
  `CategoryTheory.Functor`,
  `CategoryTheory.Functor.obj`,
  `CategoryTheory.Functor.map`,
  `CategoryTheory.Functor.map_comp`;
- best owner abstraction: `CategoryTheory.Functor`, with source-facing surface notation `C ⥤ D`;
- primitive data: the object map `Functor.obj`, the morphism map `Functor.map`, and the
  functoriality axioms `Functor.map_id` and `Functor.map_comp`;
- derived API: composition of functors, identity functors, faithfulness/fullness, and the later
  structure built on top of `Functor`.

Source/core/bridge triage:
- `source-facing`: the standard notation `C ⥤ D` for functors from `C` to `D`;
- `core/canonical`: the mathlib owner structure `Functor`;
- `bridge/view`: the primitive field projections `Functor.obj`, `Functor.map`, `Functor.map_id`,
  and `Functor.map_comp`. -/

/- Definition 4.2.8: the canonical owner notion of a functor from `C` to `D` is the structure
`CategoryTheory.Functor`, written `C ⥤ D`. Its primitive data are the object map, morphism map,
and the two functoriality axioms recalled below. -/
recall Functor

/- Companion source-facing notation: the type of functors from `C` to `D` is written `C ⥤ D`. -/
#check (C ⥤ D)

/- Primitive owner field: for a functor `F : C ⥤ D`, the induced map on objects is the canonical
field `Functor.obj`. -/
recall Functor.obj

/- Primitive owner field: for a functor `F : C ⥤ D`, the induced map on morphisms is the
canonical field `Functor.map`. -/
recall Functor.map

/- Primitive functoriality field: the identity preservation axiom in the source definition is the
canonical field `Functor.map_id`. -/
recall Functor.map_id

/- Primitive functoriality field: the composition preservation axiom in the source definition is
the canonical field `Functor.map_comp`. -/
recall Functor.map_comp

end CategoryTheory

/-! ### Definition_4_2_9 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-
Domain-style sampling for Definition 4.2.9:
- primary domain: categorical functor properties detected on hom-sets and essential image;
- sampled owner-level declarations:
  `Functor.Faithful`,
  `Functor.FullyFaithful`,
  `Functor.FullyFaithful.nonempty_iff_map_bijective`,
  `Functor.EssSurj`;
- best owner abstraction: a functor `F : C ⥤ D` equipped with the canonical owner predicates
  `F.Faithful` and `F.EssSurj`, together with the canonical owner structure `F.FullyFaithful`
  whose nonemptiness expresses the source-level fully faithful condition;
- primitive data: none locally, since these notions are already owned by mathlib;
- derived API: the field-level formulation `Faithful.map_injective`, the essential-image accessor
  `EssSurj.mem_essImage`, and the source-facing fully faithful criterion
  `Functor.FullyFaithful.nonempty_iff_map_bijective`.

Source/core/bridge triage:
- `source-facing`: faithful functors, the hom-set-bijective fully faithful condition, and
  essentially surjective functors;
- `core/canonical`: `Faithful`, `FullyFaithful`, `EssSurj`;
- `bridge/view`: `Faithful.map_injective`, `FullyFaithful.nonempty_iff_map_bijective`, and
  `EssSurj.mem_essImage`. -/

/- Definition 4.2.9: the Stacks notions of faithful, fully faithful, and essentially surjective
functors are the canonical mathlib owner predicates/structures `Functor.Faithful`,
`Functor.FullyFaithful`, and `Functor.EssSurj`; the source-level hom-set bijectivity criterion for
full faithfulness is expressed by `Functor.FullyFaithful.nonempty_iff_map_bijective`. -/
recall Faithful

/- Companion recall: the source fully faithful condition is bijectivity of each induced map on
hom-sets, and mathlib expresses that exact source-facing criterion by the canonical theorem
`Functor.FullyFaithful.nonempty_iff_map_bijective`. -/
recall FullyFaithful.nonempty_iff_map_bijective

/- Companion owner recall: mathlib packages chosen inverse maps on hom-sets in the canonical
structure `Functor.FullyFaithful`; its `Nonempty` is exactly the source-level fully faithful
property by the preceding recall. -/
recall FullyFaithful

/- Companion recall: the Stacks notion of essentially surjective functor is the canonical mathlib
class
`Functor.EssSurj`; its field `mem_essImage` says every target object lies in the essential image,
and `Functor.essImage` is defined by `∃ X : C, Nonempty (F.obj X ≅ Y)`. -/
recall EssSurj

end Functor
end CategoryTheory

/-! ### Definition_4_2_10 (from Chap04) -/
universe v u

namespace CategoryTheory

open ObjectProperty

variable (C : Type u) [Category.{v} C]

/-
Domain-style sampling for Definition 4.2.10:
- primary domain: subcategories of a category, organized by chosen objects and chosen morphisms;
- sampled owner-level declarations:
  `WideSubcategory`,
  `wideSubcategoryInclusion`,
  `ObjectProperty.FullSubcategory`,
  `Functor.Full`,
  `ObjectProperty.IsClosedUnderIsomorphisms`;
- best owner abstraction: a wide subcategory of the canonical full subcategory cut out by the
  chosen objects;
- primitive data: an object property `obj : ObjectProperty C` and a multiplicative morphism
  property `hom : MorphismProperty obj.FullSubcategory`;
- derived API: the canonical inclusion functor `S.inclusion`, the owner predicate
  `S.inclusion.Full`, and the strict-fullness predicate `S.IsStrictlyFull`.

Source/core/bridge triage:
- `source-facing`: `Subcategory`, `Subcategory.IsStrictlyFull`;
- `core/canonical`: `WideSubcategory`, `wideSubcategoryInclusion`, `ObjectProperty.FullSubcategory`,
  `Functor.Full`;
- `bridge/view`: `Subcategory.inclusion`.
-/

/-- Definition 4.2.10: a subcategory of `C` is given by a class of objects together with, for
every pair of chosen objects, a class of morphisms between them that contains identities and is
closed under composition. Internally this is expressed as a multiplicative morphism property on the
canonical full subcategory cut out by the chosen objects. -/
structure Subcategory where
  obj : ObjectProperty C
  hom : MorphismProperty obj.FullSubcategory
  hom_isMultiplicative : hom.IsMultiplicative

namespace Subcategory

variable {C}

/-- The chosen morphism property of a subcategory is multiplicative. -/
instance homIsMultiplicative (S : Subcategory C) : S.hom.IsMultiplicative :=
  S.hom_isMultiplicative

/-- The chosen objects and morphisms of a subcategory form a category. -/
instance category (S : Subcategory C) : Category (WideSubcategory S.hom) :=
  WideSubcategory.category S.hom

/-- The canonical inclusion of a subcategory into the ambient category. -/
abbrev inclusion (S : Subcategory C) : WideSubcategory S.hom ⥤ C :=
  wideSubcategoryInclusion S.hom ⋙ S.obj.ι

/-
For a subcategory `S`, fullness is expressed by requiring that the canonical inclusion
`S.inclusion : WideSubcategory S.hom ⥤ C` is a full functor, so the owner-level notion is
`[S.inclusion.Full]`.
-/

/-- A subcategory is strictly full if it is full and its chosen objects are
closed under isomorphisms in the ambient category. -/
class IsStrictlyFull (S : Subcategory C) : Prop extends S.inclusion.Full,
    S.obj.IsClosedUnderIsomorphisms

end Subcategory

end CategoryTheory

/-! ### Remark_4_2_11 (from Chap04) -/
universe u v w

namespace CategoryTheory
namespace ObjectProperty

variable {A : Type u} [Category.{v} A]
variable (F : A ⥤ Type w)

/- Domain-style sampling for Remark 4.2.11:
- primary domain: object properties and full subcategories in `Type w`, together with the
  canonical factorization of a functor through such a full subcategory;
- sampled owner declarations:
  `ObjectProperty.ofObj`,
  `ObjectProperty.lift`,
  `ObjectProperty.liftCompιIso`,
  `ObjectProperty.Small`;
- best owner abstraction: the object property `ofObj F.obj` and its canonical owner
  `FullSubcategory`, with `lift` supplying the factorization of `F`;
- primitive data: only the functor `F : A ⥤ Type w`;
- derived API: the lifted functor through `(ofObj F.obj).FullSubcategory`, the comparison
  isomorphism back to `F`, and the induced smallness statements.

Source/core/bridge triage:
- `source-facing`: the objectwise image property `ofObj F.obj`;
- `core/canonical`: `ObjectProperty.lift` and `ObjectProperty.liftCompιIso`;
- `bridge/view`: the smallness consequences for `ofObj F.obj` and its `FullSubcategory`.

The essential-image owner `Functor.essImage` is intentionally not used here: it closes the image
under isomorphism, whereas the source remark is about the literal objectwise image of a
set-valued functor. -/

/- Core/canonical recall for the source-facing image owner used in this remark: the literal
objectwise image of a family of objects is the object property `ofObj`. -/
recall ofObj

/- Remark 4.2.11: a set-valued functor `F` may be regarded as landing in the full subcategory of
`Type w` spanned by its objectwise image. This is the canonical specialization of
`ObjectProperty.lift` to the object property `ofObj F.obj`. -/
#check (ofObj F.obj).lift F (ofObj_apply F.obj)

/- Companion recall: the owner-level factorization through a full subcategory is
`ObjectProperty.lift`; the remark uses this with `P := ofObj F.obj`. -/
recall lift

/- Companion specialization: the factorization through the full subcategory on the objectwise
image comes with the canonical comparison isomorphism furnished by
`ObjectProperty.liftCompιIso`. -/
#check (ofObj F.obj).liftCompιIso F (ofObj_apply F.obj)

/- Companion recall: the objectwise image property of `F` is small by the canonical
`ObjectProperty.Small` instance for `ofObj F.obj`. -/
#synth ObjectProperty.Small (ofObj F.obj)

/- Consequently, the full subcategory of `Type w` cut out by the objectwise image of `F` is
small, via the canonical derived instance on `P.FullSubcategory`. -/
#synth _root_.Small (ofObj F.obj).FullSubcategory

end ObjectProperty
end CategoryTheory

/-! ### Example_4_2_12 (from Chap04) -/
open CategoryTheory

universe u

namespace MonoidHom

variable {M N : Type u} [Monoid M] [Monoid N]

/-
Domain-style sampling for Example 4.2.12:
- primary domain: one-object categories attached to monoids, together with the owner equivalence
  `SingleObj.mapHom` and its user-facing bridge `MonoidHom.toFunctor`; the second statement then
  specializes this monoid-level owner to groups and compares it with `GrpCat.ofHom`;
- sampled owner-level declarations:
  `SingleObj.mapHom`,
  `MonoidHom.toFunctor`,
  `Functor.Faithful.map_injective`,
  `Functor.FullyFaithful.nonempty_iff_map_bijective`,
  `ConcreteCategory.isIso_iff_bijective`;
- best owner abstraction: the owner equivalence `SingleObj.mapHom`; for the source-facing example,
  the relevant specialization is its bridge value `p.toFunctor : SingleObj G ⥤ SingleObj H`;
- primitive data: only the monoid homomorphism `p : M →* N`, since the unique object and unique
  hom-set family in `SingleObj M` are derived from the owner abstraction; the group assumptions
  enter only for the `GrpCat` isomorphism comparison in the second statement;
- derived API: the injective and bijective specializations of the owner functor criteria on the
  unique hom-set, together with the comparison to `IsIso (GrpCat.ofHom p)`.

Source/core/bridge triage:
- `source-facing`: the example-level faithfulness and full-faithfulness criteria for the induced
  one-object-category functor, with a group-level comparison to `GrpCat`;
- `core/canonical`: the owner equivalence `SingleObj.mapHom`, the functor-property predicates
  `p.toFunctor.Faithful` and `Nonempty p.toFunctor.FullyFaithful`, and `IsIso (GrpCat.ofHom p)`;
- `bridge/view`: the specialization of the owner-level functor theorems to the unique object
  `SingleObj.star`. -/

/-- Example 4.2.12 (1): for a monoid homomorphism `p : M →* N`, the induced functor
`p.toFunctor : SingleObj M ⥤ SingleObj N` is faithful exactly when `p` is injective. -/
-- Proof sketch: faithfulness means injectivity on each hom-set; for a single-object category this
-- is exactly injectivity of the underlying monoid homomorphism.
theorem toFunctor_faithful_iff_injective (p : M →* N) :
    p.toFunctor.Faithful ↔ Function.Injective p := by
  constructor
  · intro hp a b hab
    -- Evaluate faithfulness on the unique hom-set of the one-object category.
    exact hp.map_injective (X := SingleObj.star M) (Y := SingleObj.star M) hab
  · intro hp
    refine ⟨?_⟩
    intro X Y f g hfg
    -- After collapsing the objects of `SingleObj`, the map on morphisms is exactly `p`.
    cases X
    cases Y
    exact hp hfg

variable {G H : Type u} [Group G] [Group H]

/-- Helper for Example 4.2.12: the family of hom-set maps induced by `p.toFunctor` is bijective
exactly when the original group homomorphism `p` is bijective. -/
private theorem singleObj_toFunctor_map_bijective_iff (p : G →* H) :
    (∀ X Y : SingleObj G,
      Function.Bijective
        (p.toFunctor.map : (X ⟶ Y) → (p.toFunctor.obj X ⟶ p.toFunctor.obj Y))) ↔
      Function.Bijective p := by
  constructor
  · intro h
    -- Read the universal hom-set criterion on the unique object of `SingleObj G`.
    simpa using h (SingleObj.star G) (SingleObj.star G)
  · intro hp X Y
    -- Every hom-set in `SingleObj G` is the same unique hom-set, so the map is just `p`.
    cases X
    cases Y
    simpa using hp

/-- Example 4.2.12 (2): for a group homomorphism `p : G →* H`, the induced functor
`p.toFunctor : SingleObj G ⥤ SingleObj H` is fully faithful exactly when the corresponding
morphism `GrpCat.ofHom p` is an isomorphism in `GrpCat`. -/
-- Proof sketch: by `Functor.FullyFaithful.nonempty_iff_map_bijective`, full faithfulness of the
-- one-object functor is equivalent to bijectivity of `p`; for group morphisms this is equivalent
-- to `GrpCat.ofHom p` being an isomorphism by `ConcreteCategory.isIso_iff_bijective`.
theorem toFunctor_fullyFaithful_iff_isIso (p : G →* H) :
    Nonempty p.toFunctor.FullyFaithful ↔ IsIso (GrpCat.ofHom p) := by
  -- Reduce full faithfulness to bijectivity on every hom-set of the one-object category.
  rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
  rw [singleObj_toFunctor_map_bijective_iff]
  -- For morphisms in `GrpCat`, being an isomorphism is equivalent to being bijective.
  simpa using (ConcreteCategory.isIso_iff_bijective (GrpCat.ofHom p)).symm

end MonoidHom

/-! ### Example_4_2_13 (from Chap04) -/
universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Example 4.2.13:
- primary domain: slice categories and their canonical forgetful/postcomposition functors.
- inspected owner declarations:
  `CategoryTheory.Over`,
  `CategoryTheory.Over.forget`,
  `CategoryTheory.Over.map`,
  `CategoryTheory.Over.mapForget_eq`.
- best owner abstraction: mathlib's slice-category owner `Over X`; the forgetful functor and
  postcomposition functoriality are derived owner API, not separate local structures or wrappers.
- primitive data: the base object `X : C` and, for the functoriality statements, a morphism
  `f : X' ⟶ X`.
- derived API: `Over.forget X`, `Over.map f`, and the coherence `Over.mapForget_eq f`.

Source/core/bridge triage:
- `source-facing`: the four textbook slice-category constructions recalled in this file.
- `core/canonical`: `Over`, `Over.forget`, `Over.map`, `Over.mapForget_eq`.
- `bridge/view`: none needed here, since the source notions already coincide with the mathlib
  owner declarations. -/

/- Example 4.2.13 (1): for an object `X` of a category `C`, the category of objects over `X` is
the slice category `Over X`, which in mathlib is the canonical owner for the textbook category
`C/X`; its objects are morphisms to `X`, and its morphisms are commutative triangles over `X`. -/
recall Over

/- Example 4.2.13 (2): the forgetful functor from the slice category `C/X` to `C` is
`Over.forget X`. -/
recall Over.forget

/- Example 4.2.13 (3): a morphism `f : X' ⟶ X` induces the postcomposition functor
`Over.map f : Over X' ⥤ Over X`. -/
recall Over.map

/- Example 4.2.13 (4): for a morphism `f : X' ⟶ X`, postcomposition along `f` followed by
forgetting to `C` agrees with the forgetful functor from `C/X'`; the owner-level coherence is
`Over.mapForget_eq f`. -/
recall Over.mapForget_eq

end CategoryTheory

/-! ### Example_4_2_14 (from Chap04) -/
universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Example 4.2.14:
- primary domain: coslice categories and their canonical forgetful/precomposition functors.
- inspected owner declarations:
  `CategoryTheory.Under`,
  `CategoryTheory.Under.forget`,
  `CategoryTheory.Under.map`,
  `CategoryTheory.Under.mapForget_eq`.
- best owner abstraction: mathlib's coslice-category owner `Under X`; the forgetful functor and
  precomposition functoriality are derived owner API, not separate local structures or wrappers.
- primitive data: the base object `X : C` and, for the functoriality statements, a morphism
  `f : X' ⟶ X`.
- derived API: `Under.forget X`, `Under.map f`, and the coherence `Under.mapForget_eq f`.

Source/core/bridge triage:
- `source-facing`: the four textbook coslice-category constructions recalled in this file.
- `core/canonical`: `Under`, `Under.forget`, `Under.map`, `Under.mapForget_eq`.
- `bridge/view`: none needed here, since the source notions already coincide with the mathlib
  owner declarations. -/

/- Example 4.2.14 (1): for an object `X` of a category `C`, the category of objects under `X` is
the coslice category `Under X`, which in mathlib is the canonical owner for the textbook category
`X/C`. By definition this is `StructuredArrow X (𝟭 C)`, so its objects are morphisms with source
`X` and its morphisms are commutative triangles under `X`. -/
recall Under

/- Example 4.2.14 (2): the forgetful functor from the coslice category `X/C` to `C` is
`Under.forget X`. -/
recall Under.forget

/- Example 4.2.14 (3): a morphism `f : X' ⟶ X` induces the precomposition functor
`Under.map f : Under X ⥤ Under X'`. -/
recall Under.map

/- Example 4.2.14 (4): precomposition along `f : X' ⟶ X` followed by forgetting to `C` agrees
with the forgetful functor from `X/C`, namely `Under.mapForget_eq f`. -/
recall Under.mapForget_eq

end CategoryTheory

/-! ### Definition_4_2_15 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {F G : C ⥤ D}

/- Domain-style sampling for Definition 4.2.15:
- primary domain: functor categories and natural transformations in `CategoryTheory`.
- inspected owner declarations: `NatTrans`, `NatTrans.app`, `NatTrans.naturality`, and the chapter's
  based analogue `BasedNatTrans`.
- best owner abstraction: `NatTrans`; the textbook components and naturality square are primitive
  data of this owner, not local wrapper data.
- primitive-vs-derived split:
  primitive data: the component family `t.app` together with `t.naturality`, already owned
    upstream by `NatTrans`.
  derived API kept here: only the source-facing `CommSq` view `NatTrans.commSq` of
    `t.naturality f`. -/

/- Source/core/bridge triage for Definition 4.2.15:
- source-facing: the textbook description of a natural transformation by components and commuting
  squares.
- core/canonical: `NatTrans`.
- bridge/view: `NatTrans.commSq`, the `CommSq` packaging of `t.naturality f`. -/

/-
Definition 4.2.15: a natural transformation, or morphism of functors, between functors
`F G : C ⥤ D` is the canonical mathlib structure `NatTrans`, written `F ⟶ G`.
Its components are the morphisms `t.app X : F.obj X ⟶ G.obj X`.
-/
recall NatTrans

/- Definition 4.2.15: the component of a natural transformation `t : F ⟶ G` at `X`
is the canonical morphism `t.app X : F.obj X ⟶ G.obj X`. -/
recall NatTrans.app

/- For `t : F ⟶ G`, the commutative square in the textbook definition is exactly the built-in
naturality statement `t.naturality f`. -/
recall NatTrans.naturality

namespace NatTrans

/-- Bridge/view companion: the textbook commutative square is the canonical naturality identity
packaged as a `CommSq`. -/
theorem commSq {X Y : C} (t : F ⟶ G) (f : X ⟶ Y) :
    CommSq (F.map f) (t.app X) (t.app Y) (G.map f) :=
  ⟨t.naturality f⟩

end NatTrans

end CategoryTheory

/-! ### Remark_4_2_16 (from Chap04) -/
universe u

namespace CategoryTheory

/-
Domain-style sampling for Remark 4.2.16:
- primary domain: universe-smallness of functor types.
- sampled owner-level declarations:
  `Small`,
  `small_of_surjective`,
  `not_small_type`,
  `evaluation`,
  `Functor.const`;
- best owner abstraction: `Small`.

Source/core/bridge triage:
- `source-facing`: the specific Stacks remark that `Type u ⥤ Type u` is not `u`-small.
- `core/canonical`: the owner predicate `Small` together with the core theorem `not_small_type`.
- `bridge/view`: the owner-level evaluation map at `PUnit`,
  `((evaluation (Type u) (Type u)).obj PUnit).obj : (Type u ⥤ Type u) → Type u`, which is
  surjective because every type is the value at `PUnit` of its constant endofunctor.

Primitive-vs-derived split:
- primitive data: none in this file; the relevant notions already live upstream.
- derived API: the theorem below, deduced from `not_small_type` by applying the canonical
  smallness transfer `small_of_surjective` to evaluation at `PUnit`.
-/

/-- Remark 4.2.16 (Stacks tag `02C2`): when `Sets` is modeled by the big category `Type u`, the
type of endofunctors `Type u ⥤ Type u` is not `u`-small. Equivalently, a functor `Sets → Sets`
is not itself a set-sized mathematical object. -/
theorem type_endofunctor_not_small :
    ¬ Small.{u} (Type u ⥤ Type u) := by
  intro hsmall
  letI := hsmall
  let ev : (Type u ⥤ Type u) → Type u := ((evaluation (Type u) (Type u)).obj PUnit).obj
  have hsurj : Function.Surjective ev := fun X ↦ ⟨(Functor.const (Type u)).obj X, rfl⟩
  exact not_small_type <| small_of_surjective hsurj

end CategoryTheory

/-! ### Definition_4_2_17 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Functor

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]

/- Domain-style sampling for Definition 4.2.17:
- `Functor.IsEquivalence` is the owner predicate for a functor being an equivalence of
  categories.
- `Functor.IsEquivalence.mk'` is the canonical constructor from a quasi-inverse together with the
  unit and counit isomorphisms.
- `Functor.inv` is the derived quasi-inverse attached to the owner predicate.
- `Functor.asEquivalence` upgrades the owner predicate to the canonical equivalence object
  `A ≌ B`.

Primitive-vs-derived split:
- primitive data: none in this file; the notion is already owned upstream by the `Prop`-valued
  class `Functor.IsEquivalence`.
- derived API: the source-facing quasi-inverse characterization below, exposing the quasi-inverse
  functor together with existential unit/counit isomorphism data, recovered from `Functor.inv`,
  `Functor.asEquivalence`, and `Functor.IsEquivalence.mk'`. -/

/- Source/core/bridge triage for Definition 4.2.17:
- `source-facing`: the textbook quasi-inverse formulation of equivalence of categories.
- `core/canonical`: `Functor.IsEquivalence`.
- `bridge/view`: `isEquivalence_iff_exists_quasiInverse`. -/

/- Definition 4.2.17: the canonical owner abstraction for an equivalence of categories carried by a
functor is `Functor.IsEquivalence`. -/
recall Functor.IsEquivalence

/- Bridge/view: this source-facing quasi-inverse formulation is a companion specification of the
owner abstraction `Functor.IsEquivalence`, not a second owner. The `Nonempty` wrappers record the
existence of the unit and counit isomorphisms while keeping the statement in `Prop`. If `F` is an
equivalence, use `F.inv` together with the unit and counit isomorphisms of `F.asEquivalence`;
conversely, chosen such isomorphisms give `F.IsEquivalence` via `Functor.IsEquivalence.mk'`. -/
/-- Companion bridge for Definition 4.2.17: a functor is an equivalence of categories exactly when
it admits a quasi-inverse together with unit and counit isomorphisms. -/
theorem isEquivalence_iff_exists_quasiInverse (F : A ⥤ B) :
    F.IsEquivalence ↔
      ∃ G : B ⥤ A, Nonempty (𝟭 A ≅ F ⋙ G) ∧ Nonempty (G ⋙ F ≅ 𝟭 B) := by
  constructor
  · intro hF
    letI := hF
    exact ⟨F.inv, ⟨F.asEquivalence.unitIso⟩, ⟨F.asEquivalence.counitIso⟩⟩
  · rintro ⟨G, ⟨η⟩, ⟨ε⟩⟩
    exact Functor.IsEquivalence.mk' G η ε

end Functor
end CategoryTheory

/-! ### Lemma_4_2_18 (from Chap04) -/
open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Functor

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]

/-
Domain-style sampling for Lemma 4.2.18:
- `Functor.EssSurj` is the owner abstraction for chosen objectwise preimages up to isomorphism.
- `Functor.essImage.liftFunctor` / `Functor.essImage.liftFunctorCompIso` provide the canonical
  essential-image lift.
- `Functor.fullyFaithfulCancelRight` is the canonical uniqueness tool for lifts through a fully
  faithful functor.
- `Functor.IsEquivalence` is the owner predicate for equivalences of categories.

Primitive-vs-derived split:
- primitive source-facing data: a chosen object assignment `jObj : B → A` and isomorphisms
  `i X : X ≅ F.obj (jObj X)`.
- derived API: the induced lift functor, the canonical `EssSurj` witness, and hence
  `IsEquivalence` when `F` is also full and faithful.
-/

/- Source/core/bridge triage for Lemma 4.2.18:
- `source-facing`: `fully_faithful_objwise_iso_existsUnique_lift`.
- `core/canonical`: `Functor.EssSurj` and `Functor.IsEquivalence`.
- `bridge/view`: `essSurj_of_objwise_iso` and the resulting equivalence criterion below.

The source-facing theorem keeps an explicit lift construction because the textbook data prescribes
the object assignment `jObj` on the nose. Mathlib's owner-level `essImage.liftFunctor` only
produces a chosen preimage object from essential-image membership, so it does not preserve that
specified object assignment definitionally. -/

variable (F : A ⥤ B)

/-- Lemma 4.2.18 (1): the chosen object assignment and isomorphisms determine a unique extension
functor. -/
theorem fully_faithful_objwise_iso_existsUnique_lift
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) :
    ∃! j : B ⥤ A,
      ∃ hjObj : ∀ X : B, j.obj X = jObj X,
        ∃ α : 𝟭 B ≅ j ⋙ F,
          ∀ X : B,
            α.hom.app X =
              (i X).hom ≫
                eqToHom
                  (show F.obj (jObj X) = (j ⋙ F).obj X from by
                    simpa using congrArg (fun Z ↦ F.obj Z) (hjObj X).symm) := by
  let j : B ⥤ A :=
    { obj := jObj
      map := fun f ↦ F.preimage ((i _).inv ≫ f ≫ (i _).hom)
      map_id := by
        intro X
        apply F.map_injective
        simp
      map_comp := by
        intro X Y Z f g
        apply F.map_injective
        simp [Category.assoc] }
  let α : 𝟭 B ≅ j ⋙ F :=
    NatIso.ofComponents i <| by
      intro X Y f
      change f ≫ (i Y).hom = (i X).hom ≫ F.map (F.preimage ((i X).inv ≫ f ≫ (i Y).hom))
      simp
  have hj : ∀ X : B, j.obj X = jObj X := fun _ ↦ rfl
  have hα :
      ∀ X : B,
        α.hom.app X =
          (i X).hom ≫
            eqToHom
              (show F.obj (jObj X) = (j ⋙ F).obj X from by
                simpa using congrArg (fun Z ↦ F.obj Z) (hj X).symm) := by
    intro X
    simp [α, j]
  refine ⟨j, ?_, ?_⟩
  · exact ⟨hj, α, hα⟩
  · intro j' hj'
    rcases hj' with ⟨hjObj, α', hα'⟩
    let compIso : j' ⋙ F ≅ j ⋙ F := α'.symm ≪≫ α
    let e : j' ≅ j := fullyFaithfulCancelRight F compIso
    refine ext_of_iso e (fun X ↦ (hjObj X).trans (hj X).symm) ?_
    intro X
    let hobjX : j'.obj X = j.obj X := (hjObj X).trans (hj X).symm
    change F.preimage (compIso.hom.app X) = eqToHom hobjX
    apply F.map_injective
    let p : (j' ⋙ F).obj X = F.obj (jObj X) := by
      simpa using congrArg (fun Z ↦ F.obj Z) (hjObj X)
    have h1 : α'.inv.app X ≫ (i X).hom = eqToHom p := by
      apply (cancel_mono (eqToHom p.symm)).1
      simpa [p, hα' X, Category.assoc] using α'.inv_hom_id_app X
    have h2 : F.map (eqToHom hobjX) = eqToHom p := by
      simp [eqToHom_map]
    have hcomp : compIso.hom.app X = α'.inv.app X ≫ (i X).hom := by
      simp [compIso, α]
    exact (F.map_preimage _).trans (hcomp.trans (h1.trans (by simpa using h2.symm)))

/-- Chosen objectwise preimages exhibit `F` as essentially
surjective. -/
theorem essSurj_of_objwise_iso
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) :
    F.EssSurj :=
  ⟨fun X ↦ ⟨jObj X, ⟨(i X).symm⟩⟩⟩

/-- Lemma 4.2.18 (2): chosen objectwise preimages under a fully faithful functor make the functor an
equivalence. -/
theorem fully_faithful_isEquivalence_of_objwise_iso
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) : F.IsEquivalence := by
  exact
    { faithful := inferInstance
      full := inferInstance
      essSurj := F.essSurj_of_objwise_iso jObj i }

end Functor
end CategoryTheory

/-! ### Lemma_4_2_19 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Functor

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]

/- Domain-style sampling for Lemma 4.2.19:
- `Functor.IsEquivalence` is the owner predicate for a functor being an equivalence of categories.
- `Functor.IsEquivalence.faithful`, `Functor.IsEquivalence.full`, and
  `Functor.IsEquivalence.essSurj` are the derived canonical accessors.
- `Functor.Full` and `Functor.Faithful` are the owner predicates for the two halves of the
  full-faithful criterion.
- `Functor.FullyFaithful` is a derived bundled witness, obtained canonically from
  `Functor.Full` and `Functor.Faithful` when needed.
- `Functor.asEquivalence` upgrades the owner predicate to the canonical equivalence object.

Primitive-vs-derived split:
- primitive data: none in this file; the notion is already owned upstream by the `Prop`-valued
  class `Functor.IsEquivalence`.
- derived API: fullness, faithfulness, essential surjectivity, and the bridge from
  `Functor.IsEquivalence` to the textbook full-faithful-essentially-surjective criterion
  below. -/

/- Source/core/bridge triage for Lemma 4.2.19:
- `source-facing`: the textbook criterion "full, faithful, essentially surjective".
- `core/canonical`: `Functor.IsEquivalence`.
- `bridge/view`: `isEquivalence_iff_full_faithful_essSurj`, phrased through hom-set
  bijectivity to package "full and faithful" into one atomic clause. -/

/- Canonical owner data for this item live in mathlib's predicates `Functor.IsEquivalence`,
`Functor.Full`, `Functor.Faithful`, and `Functor.EssSurj`. -/

-- Proof sketch: `Functor.IsEquivalence` has fields giving `F.Full`, `F.Faithful`, and
-- `F.EssSurj`; the first two are equivalent to bijectivity of `F.map` on every hom-set, so this
-- is the textbook full-faithful-essentially-surjective criterion in one atomic conjunction.
/-- Lemma 4.2.19: a functor is an equivalence of categories exactly when it is fully faithful,
together with essential surjectivity; here full and faithful are packaged as bijectivity on every
hom-set so the statement remains atomic while matching the textbook criterion. -/
theorem isEquivalence_iff_full_faithful_essSurj (F : A ⥤ B) :
    F.IsEquivalence ↔
      (∀ X Y : A, Function.Bijective
        (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y))) ∧
        F.EssSurj := by
  constructor
  · intro hEq
    -- Extract the canonical full-faithful-essentially-surjective data from the equivalence witness.
    letI : F.IsEquivalence := hEq
    refine ⟨?_, inferInstance⟩
    -- Convert full and faithful into bijectivity on each hom-set.
    intro X Y
    exact (Functor.FullyFaithful.ofFullyFaithful F).map_bijective X Y
  · rintro ⟨hbij, hEss⟩
    -- Route correction: follow the source proof by choosing objectwise preimages from essential
    -- surjectivity and then invoking Lemma 4.2.18.
    letI : F.Faithful := ⟨fun {X Y} ↦ (hbij X Y).injective⟩
    letI : F.Full := ⟨fun {X Y} ↦ (hbij X Y).surjective⟩
    letI : F.EssSurj := hEss
    -- The chosen preimages are the canonical `objPreimage`s supplied by essential surjectivity.
    exact
      F.fully_faithful_isEquivalence_of_objwise_iso
        (fun X ↦ F.objPreimage X)
        (fun X ↦ (F.objObjPreimageIso X).symm)

end Functor
end CategoryTheory

/-! ### Definition_4_2_20 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Prod

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {X₁ X₂ X₃ : C} {Y₁ Y₂ Y₃ : D}

/- Domain-style sampling for Definition 4.2.20:
- primary domain: product categories in `CategoryTheory`;
- inspected owner declarations: `CategoryStruct.prod`, `prod'`, `Prod.mkHom`, `prod_comp`;
- best owner abstraction: the canonical category instance `prod'` on `C × D`; `CategoryStruct.prod`
  is only the lower structural precursor, not a second public owner.

Primitive-vs-derived split:
- primitive data inherited by the owner stack: the hom-types, identities, and composition on
  `C × D`, implemented upstream by `CategoryStruct.prod` and promoted to a category by `prod'`;
- derived API: the standard product-morphism constructor `Prod.mkHom` together with the pointwise
  identity and composition formulas `prod_id'` and `prod_comp`. -/

/- Source/core/bridge triage for Definition 4.2.20:
- `source-facing`: the textbook description of the product category with pair objects, pair
  morphisms, and componentwise composition.
- `core/canonical`: the mathlib owner instance `CategoryTheory.prod'`.
- `bridge/view`: `Prod.mkHom`, `prod_id'`, and `prod_comp` as the direct source-facing formulas for
  morphisms, identities, and composition. -/

/- Definition 4.2.20 is a `core/canonical` recall: the product category of `C` and `D` is the
canonical mathlib category instance `CategoryTheory.prod'` on `C × D`. -/
recall prod'

/- Definition 4.2.20, source object form: an object of the product category is simply a pair
`(X₁, Y₁) : C × D`. -/
#check ((X₁, Y₁) : C × D)

/- Definition 4.2.20, source hom-set form: a morphism in the product category from `(X₁, Y₁)` to
`(X₂, Y₂)` is the canonical hom-type `((X₁, Y₁) ⟶ (X₂, Y₂))`, definitionally a pair of component
morphisms. -/
#check (((X₁, Y₁) : C × D) ⟶ (X₂, Y₂))

/- Companion recall: `Prod.mkHom` is the canonical constructor for morphisms in the product
category from their two components. -/
recall Prod.mkHom

/- Definition 4.2.20, source morphism constructor: a pair of component morphisms determines the
canonical product-category morphism `f ×ₘ g`. -/
#check fun (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) ↦ f ×ₘ g

/- Definition 4.2.20, source identity formula: the identity of `(X₁, Y₁)` is `(𝟙 X₁, 𝟙 Y₁)`,
packaged canonically by `prod_id'`. -/
recall prod_id'

/- Companion recall: `prod_comp` is derived API for the owner instance `prod'`, giving the
canonical componentwise composition rule in the product category. -/
recall prod_comp

end CategoryTheory
