import Mathlib
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.Strict.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_29_1 (from Chap04) -/
universe u

namespace CategoryTheory

open Bicategory

/- Domain-style sampling for Definition 4.29.1:
- primary domain: bicategory theory, specializing the textbook notion of a strict `2`-category;
- sampled owner-level declarations:
  `Bicategory`,
  `Bicategory.Strict`,
  `postcomposing`,
  `associatorNatIsoMiddle`;
- best owner abstraction: `Bicategory` is the ambient owner carrying objects, hom-categories,
  `2`-morphisms, whiskering, associator/unitors, and the exchange law, while `Strict` is the
  extra source-facing predicate expressing that this bicategory is a strict `2`-category;
- primitive-vs-derived split:
  primitive data: the ambient bicategory structure `Bicategory B`, together with the strictness
    predicate `Strict B`;
  derived API: the curried composition functor, the associator/unitor natural isomorphisms, the
    exchange law, and the induced ordinary category structure on objects and `1`-morphisms.

Source/core/bridge triage:
- `source-facing`: the textbook notion of a strict `2`-category, namely a bicategory with the
  extra strictness condition, and its horizontal composition data;
- `core/canonical`: `Bicategory`, `Strict`, `postcomposing`, `associatorNatIsoMiddle`,
  `leftUnitorNatIso`, `rightUnitorNatIso`, `whisker_exchange`, `StrictBicategory.category`;
- `bridge/view`: none; the source notions are already owned by the ambient bicategory API. -/

/- Definition 4.29.1: the ambient owner of the objects, `1`-morphisms, `2`-morphisms, whiskering,
associator/unitors, and exchange law of a `2`-category is the canonical mathlib class
`CategoryTheory.Bicategory B`. -/
recall Bicategory

/- Definition 4.29.1: the extra condition making a bicategory into a strict `2`-category is the
canonical strictness predicate `Strict B`. Thus the Stacks notion is expressed by the pair of
assumptions `[Bicategory B] [Strict B]`. -/
recall Strict

variable {B : Type u} [Bicategory B]

/- Definition 4.29.1: for each triple of objects, the textbook composition functor
`Mor(y, z) × Mor(x, y) ⥤ Mor(x, z)` is the canonical curried functor
`postcomposing x y z`. Its action on `2`-morphisms is horizontal composition. -/
recall postcomposing

/- Definition 4.29.1: associativity of horizontal composition of `2`-morphisms is the canonical
middle associator natural isomorphism of the bicategory composition functors. -/
recall associatorNatIsoMiddle

/- Definition 4.29.1: the identity `2`-morphism of an identity `1`-morphism acts as a left unit
for horizontal composition via the canonical left unitor natural isomorphism. -/
recall leftUnitorNatIso

/- Definition 4.29.1: the identity `2`-morphism of an identity `1`-morphism acts as a right unit
for horizontal composition via the canonical right unitor natural isomorphism. -/
recall rightUnitorNatIso

/- Definition 4.29.1: the two standard whiskering formulas for horizontal composition of
`2`-morphisms agree by the canonical bicategorical exchange law. -/
recall whisker_exchange

variable [Strict B]

/- In a strict `2`-category, the objects and `1`-morphisms form the canonical ordinary category
given by `StrictBicategory.category`. -/
recall StrictBicategory.category

end CategoryTheory

/-! ### Definition_4_29_2 (from Chap04) -/
namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

universe w v u

/- Domain-style sampling for Definition 4.29.2:
- primary domain: strict bicategories and source-facing sub-`2`-categories cut out by chosen
  objects, `1`-morphisms, and `2`-morphisms;
- inspected owner-level declarations:
  `Subcategory`,
  `Subcategory.inclusion`,
  `ObjectProperty.FullSubcategory`,
  `WideSubcategory`,
  `wideSubcategoryInclusion`,
  `Bicategory.InducedBicategory.forget`.
- best owner abstraction: `SubTwoCategory C`, with each chosen hom-category expressed by the
  earlier chapter owner `Subcategory (X.obj ⟶ Y.obj)`;
- primitive data: an object property `obj`, a chosen hom-subcategory `hom X Y` for each pair of
  selected objects, and the closure of the selected `1`-morphisms and `2`-morphisms under
  identities, composition, and whiskering;
- derived API: the bundled object type `Obj`, the derived `1`- and `2`-morphism properties
  `hom₁` and `hom₂`, the hom-categories `Hom`, the induced strict bicategory structure on `Obj`,
  and the canonical inclusion `StrictPseudofunctor`.

Source/core/bridge triage:
- `source-facing`: `SubTwoCategory`;
- `core/canonical`: `Subcategory`, `ObjectProperty.FullSubcategory`, `WideSubcategory`, and
  `StrictPseudofunctor`;
- `bridge/view`: the short owner projections `Obj`, `hom₁`, `hom₂`, `Hom`, `Hom.toHom`, and
  `inclusion`. -/

/-- Definition 4.29.2: a sub 2-category of a strict 2-category `C` consists of a subset of
objects, for each chosen pair of objects a subcategory of the corresponding hom category, and
closure of these chosen cells under composition of `1`-morphisms and horizontal whiskering, so
that the chosen data again form a strict `2`-category. -/
structure SubTwoCategory (C : Type u) [Bicategory.{w, v} C] [Strict C] where
  obj : ObjectProperty C
  hom (X Y : obj.FullSubcategory) : Subcategory (X.obj ⟶ Y.obj)
  id_mem (X : obj.FullSubcategory) : (hom X X).obj (𝟙 X.obj)
  comp_mem {X Y Z : obj.FullSubcategory} {f : X.obj ⟶ Y.obj} {g : Y.obj ⟶ Z.obj}
      (hf : (hom X Y).obj f) (hg : (hom Y Z).obj g) : (hom X Z).obj (f ≫ g)
  whiskerLeft_mem {W X Y : obj.FullSubcategory} {k : W.obj ⟶ X.obj} {f g : X.obj ⟶ Y.obj}
      (hk : (hom W X).obj k) (hf : (hom X Y).obj f) (hg : (hom X Y).obj g)
      {η : (⟨f, hf⟩ : (hom X Y).obj.FullSubcategory) ⟶ ⟨g, hg⟩} :
      (hom W Y).hom
        ((homMk (k ◁ η.hom) :
          (⟨k ≫ f, comp_mem hk hf⟩ : (hom W Y).obj.FullSubcategory) ⟶
            ⟨k ≫ g, comp_mem hk hg⟩))
  whiskerRight_mem {X Y Z : obj.FullSubcategory} {f g : X.obj ⟶ Y.obj} {h : Y.obj ⟶ Z.obj}
      (hf : (hom X Y).obj f) (hg : (hom X Y).obj g)
      {η : (⟨f, hf⟩ : (hom X Y).obj.FullSubcategory) ⟶ ⟨g, hg⟩}
      (hh : (hom Y Z).obj h) :
      (hom X Z).hom
        ((homMk (η.hom ▷ h) :
          (⟨f ≫ h, comp_mem hf hh⟩ : (hom X Z).obj.FullSubcategory) ⟶
            ⟨g ≫ h, comp_mem hg hh⟩))

namespace SubTwoCategory

variable {C : Type u} [Bicategory.{w, v} C] [Strict C]

/-- The chosen object type attached to a sub `2`-category `S`. -/
abbrev Obj (S : SubTwoCategory C) :=
  S.obj.FullSubcategory

/-- The chosen `1`-morphism property on each ambient hom-category. -/
abbrev hom₁ (S : SubTwoCategory C) (X Y : S.Obj) : ObjectProperty (X.obj ⟶ Y.obj) :=
  (S.hom X Y).obj

/-- The chosen `2`-morphism property on each selected hom-category. -/
abbrev hom₂ (S : SubTwoCategory C) (X Y : S.Obj) : MorphismProperty ((S.hom₁ X Y).FullSubcategory) :=
  (S.hom X Y).hom

/-- The chosen hom category `Mor_{C'}(X, Y)` attached to a sub `2`-category `S`. -/
abbrev Hom (S : SubTwoCategory C) (X Y : S.Obj) :=
  @WideSubcategory
    ((S.hom₁ X Y).FullSubcategory)
    inferInstance
    (S.hom₂ X Y)
    (S.hom X Y).hom_isMultiplicative

namespace Hom

variable (S : SubTwoCategory C) (X Y : S.Obj)

variable {S X Y}

/-- Build a selected hom from an ambient `1`-morphism satisfying the selected hom property. -/
abbrev mk (f : X.obj ⟶ Y.obj) (hf : (S.hom X Y).obj f) : S.Hom X Y :=
  { obj := { obj := f, property := hf } }

/-- The ambient `1`-morphism underlying an object of a chosen hom category. -/
abbrev toHom (f : S.Hom X Y) : X.obj ⟶ Y.obj :=
  f.obj.obj

@[simp]
theorem toHom_obj (f : S.Hom X Y) :
    f.toHom = f.obj.obj :=
  rfl

/-- Lift an isomorphism of ambient `1`-morphisms to an isomorphism in a chosen hom category,
provided the two `2`-morphisms lie in the selected wide subcategory. -/
noncomputable def isoMk {f g : S.Hom X Y}
    (e : f.toHom ≅ g.toHom)
    (he : (S.hom X Y).hom (ObjectProperty.homMk e.hom))
    (he_inv : (S.hom X Y).hom (ObjectProperty.homMk e.inv)) :
    f ≅ g :=
  { hom := ⟨ObjectProperty.homMk e.hom, he⟩
    inv := ⟨ObjectProperty.homMk e.inv, he_inv⟩ }

@[simp]
theorem eqToHom_hom {f g : S.Hom X Y} (h : f = g) :
    (eqToHom h).hom.hom = eqToHom (congrArg (fun k : S.Hom X Y ↦ k.toHom) h) := by
  subst h
  simp

end Hom

private theorem id_comp_eq {S : SubTwoCategory C} {X Y : S.Obj} (f : S.Hom X Y) :
    (⟨⟨𝟙 X.obj ≫ f.toHom, S.comp_mem (S.id_mem X) f.obj.property⟩⟩ : S.Hom X Y) = f := by
  ext
  exact Strict.id_comp f.toHom

private theorem comp_id_eq {S : SubTwoCategory C} {X Y : S.Obj} (f : S.Hom X Y) :
    (⟨⟨f.toHom ≫ 𝟙 Y.obj, S.comp_mem f.obj.property (S.id_mem Y)⟩⟩ : S.Hom X Y) = f := by
  ext
  exact Strict.comp_id f.toHom

private theorem assoc_eq {S : SubTwoCategory C} {W X Y Z : S.Obj}
    (f : S.Hom W X) (g : S.Hom X Y) (h : S.Hom Y Z) :
    (⟨⟨(f.toHom ≫ g.toHom) ≫ h.toHom,
        S.comp_mem (S.comp_mem f.obj.property g.obj.property) h.obj.property⟩⟩ : S.Hom W Z) =
      ⟨⟨f.toHom ≫ g.toHom ≫ h.toHom,
        S.comp_mem f.obj.property (S.comp_mem g.obj.property h.obj.property)⟩⟩ := by
  ext
  exact Strict.assoc f.toHom g.toHom h.toHom

instance bicategoryObj (S : SubTwoCategory C) : Bicategory S.Obj where
  Hom X Y := S.Hom X Y
  homCategory X Y :=
    @WideSubcategory.category
      ((S.hom₁ X Y).FullSubcategory)
      inferInstance
      (S.hom₂ X Y)
      (S.hom X Y).hom_isMultiplicative
  id X := ⟨⟨𝟙 X.obj, S.id_mem X⟩⟩
  comp f g := ⟨⟨f.toHom ≫ g.toHom, S.comp_mem f.obj.property g.obj.property⟩⟩
  whiskerLeft := by
    intro X Y Z f g h η
    exact {
      hom := homMk (f.toHom ◁ η.hom.hom)
      property := S.whiskerLeft_mem f.obj.property g.obj.property h.obj.property
    }
  whiskerRight := by
    intro X Y Z f g η h
    exact {
      hom := homMk (η.hom.hom ▷ h.toHom)
      property := S.whiskerRight_mem f.obj.property g.obj.property h.obj.property
    }
  associator f g h := eqToIso (assoc_eq f g h)
  leftUnitor f := eqToIso (id_comp_eq f)
  rightUnitor f := eqToIso (comp_id_eq f)
  whiskerLeft_id := by
    intro a b c f g
    ext
    simp
  whiskerLeft_comp := by
    intro a b c f g h i η θ
    ext
    simp
  id_whiskerRight := by
    intro a b c f g
    ext
    simp
  comp_whiskerRight := by
    intro a b c f g h η θ i
    ext
    simp
  id_whiskerLeft := by
    intro a b f g η
    ext
    simp [Strict.leftUnitor_eqToIso]
  comp_whiskerLeft := by
    intro a b c d f g h h' η
    ext
    simp [Strict.associator_eqToIso]
  whiskerRight_id := by
    intro a b f g η
    ext
    simp [Strict.rightUnitor_eqToIso]
  whiskerRight_comp := by
    intro a b c d f f' η g h
    ext
    simp [Strict.associator_eqToIso]
  whisker_assoc := by
    intro a b c d f g g' η h
    ext
    simp [Strict.associator_eqToIso]
  whisker_exchange := by
    intro a b c f g h i η θ
    ext
    simpa using CategoryTheory.Bicategory.whisker_exchange η.hom.hom θ.hom.hom
  pentagon := by
    intro a b c d e f g h i
    ext
    simp
  triangle := by
    intro a b c f g
    ext
    simp

instance strictObj (S : SubTwoCategory C) : Strict S.Obj where
  id_comp := id_comp_eq
  comp_id := comp_id_eq
  assoc := assoc_eq
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso _ _ _ := rfl

/-- The canonical inclusion of a sub `2`-category into the ambient strict `2`-category. -/
@[simps!]
def inclusion (S : SubTwoCategory C) : StrictPseudofunctor S.Obj C :=
  StrictPseudofunctor.mk' {
    obj := fun X ↦ X.obj
    map := fun f ↦ f.toHom
    map_id := by
      intro X
      rfl
    map_comp := by
      intro a b c f g
      rfl
    map₂ := fun η ↦ η.hom.hom
    map₂_whisker_left := by
      intro a b c f g g' η
      change f.toHom ◁ η.hom.hom = eqToHom rfl ≫ (f.toHom ◁ η.hom.hom) ≫ eqToHom rfl
      simp
    map₂_whisker_right := by
      intro a b c f f' η g
      change η.hom.hom ▷ g.toHom = eqToHom rfl ≫ (η.hom.hom ▷ g.toHom) ≫ eqToHom rfl
      simp
    map₂_left_unitor := by
      intro a b f
      rw [Strict.leftUnitor_eqToIso, eqToIso.hom, Hom.eqToHom_hom (id_comp_eq f)]
      simp [Strict.leftUnitor_eqToIso]
    map₂_right_unitor := by
      intro a b f
      rw [Strict.rightUnitor_eqToIso, eqToIso.hom, Hom.eqToHom_hom (comp_id_eq f)]
      simp [Strict.rightUnitor_eqToIso]
    map₂_associator := by
      intro a b c d f g h
      rw [Strict.associator_eqToIso, eqToIso.hom, Hom.eqToHom_hom (assoc_eq f g h)]
      simp [Strict.associator_eqToIso]
  }

end SubTwoCategory

end CategoryTheory

/-! ### Remark_4_29_3 (from Chap04) -/
universe u v w

namespace CategoryTheory

open AlgebraicGeometry
open Bicategory
open Bicategory.InducedBicategory
open FibredInGroupoidsOver
open FibredInGroupoidsMor
open ObjectProperty
open scoped Bicategory

/- Domain-style sampling for Remark 4.29.3:
- primary domain: canonical owner-level examples of strict `2`-categories;
- sampled declarations:
  `InducedBicategory Cat Grpd.forgetToCat.obj`,
  `fibredInGroupoidsOverSubTwoCategory`,
  `stackInGroupoidsOverSubTwoCategory`,
  `StackInGroupoidsOver.ofProjection`;
- best owner abstraction: each example should be stated through its ambient owner `2`-category
  rather than through parallel local wrappers. For groupoids this owner is the induced
  bicategory inside `Cat`; for fibred categories and stacks it is the relevant chapter-level full
  sub-`2`-category owner.
- primitive data: the ambient owner objects themselves;
- derived API: the inherited object types, owner homs, the diagonal representability predicate,
  the atlas predicate `p.LocallyEssentiallySurjectiveOnObjects`, and the representable stack
  bridge `StackInGroupoidsOver.ofProjection J_fppf (Over.forget U)`.

Source/core/bridge triage:
- `source-facing`: the textbook list of strict `2`-category examples;
- `core/canonical`: `Cat`, `InducedBicategory Cat Grpd.forgetToCat.obj`,
  `fibredCategoryOverSubTwoCategory C`, `fibredInGroupoidsOverSubTwoCategory C`,
  `stackOverSubTwoCategory J`, `stackInGroupoidsOverSubTwoCategory J`,
  `stackInSetoidsOverSubTwoCategory J`, and `StackInGroupoidsOver J_fppf`;
- `bridge/view`: the inherited object types together with
  `StackInGroupoidsOver.ofProjection J_fppf (Over.forget U)` and
  `representable_diagonal_iff_all_slice_morphisms_representable`. -/

variable {A B : Cat}

/- Remark 4.29.3 (Stacks tag `003J`): the ambient strict `2`-category of categories is the
canonical large category `Cat`, and its hom-categories are the ordinary functor categories. -/
recall Cat
#check (A ⥤ B)

variable {G₁ G₂ : Grpd}

/- Another listed example is the full sub-`2`-category of groupoids inside `Cat`. Its
owner-level strict `2`-category surface is the induced bicategory on `Grpd` through
`Grpd.forgetToCat.obj`, while the bundled category `Grpd` remains the companion object/
`1`-morphism view. -/
#check InducedBicategory Cat Grpd.forgetToCat.obj
#check (inferInstance : Strict (InducedBicategory Cat Grpd.forgetToCat.obj))
recall Grpd
#check (G₁ ⥤ G₂)
#check Grpd.forgetToCat

variable {C : Type u} [Category.{v} C]
variable {X Y : FibredCategoryOver C}

/- Over a fixed base `C`, categories fibred over `C` are formalized by the full sub-`2`-category
owner `fibredCategoryOverSubTwoCategory C`; its object type is `FibredCategoryOver C`, with
ambient hom-categories `X ⟶ Y`. -/
#check fibredCategoryOverSubTwoCategory C
#check FibredCategoryOver C
#check (X ⟶ Y)

variable {Xg Yg : FibredInGroupoidsOver C}

/- Categories fibred in groupoids over `C` are formalized by the full sub-`2`-category owner
`fibredInGroupoidsOverSubTwoCategory C`; its object type is `FibredInGroupoidsOver C`, and the
ambient owner homs are `Xg ⟶ Yg`. -/
#check fibredInGroupoidsOverSubTwoCategory C
#check FibredInGroupoidsOver C
#check (Xg ⟶ Yg)

variable (J : GrothendieckTopology C)
variable {S T : StackOver J}

/- Over a fixed site `(C, J)`, stacks are formalized by the full sub-`2`-category owner
`stackOverSubTwoCategory J`; its object type is `StackOver J`, with ambient hom-categories
`S ⟶ T`. -/
#check stackOverSubTwoCategory J
#check StackOver J
#check (S ⟶ T)

variable {Sg Tg : StackInGroupoidsOver J}

/- Stacks in groupoids over `(C, J)` are already packaged by the canonical owner
`stackInGroupoidsOverSubTwoCategory J`; their object type is `StackInGroupoidsOver J`. -/
#check stackInGroupoidsOverSubTwoCategory J
#check StackInGroupoidsOver J
#check (Sg ⟶ Tg)

variable {Ss Ts : StackInSetoidsOver J}

/- Likewise, stacks in setoids over `(C, J)` are the canonical full sub-`2`-category
`stackInSetoidsOverSubTwoCategory J` of stacks in groupoids, with object type
`StackInSetoidsOver J`. -/
#check stackInSetoidsOverSubTwoCategory J
#check StackInSetoidsOver J
#check (Ss ⟶ Ts)

section AlgebraicStacks

open StackInGroupoidsOver.Hom

variable (Xscheme : Scheme.{w})
variable {U : Over Xscheme}
local notation "J_fppf" => Scheme.fppfTopology.over Xscheme
variable (𝒳 : StackInGroupoidsOver J_fppf)

local instance overForget_isStackInGroupoids (U : Over Xscheme) :
    IsStackInGroupoids J_fppf (Over.forget U) := by
  refine
    { toIsStackOnSite := by
        rw [over_forget_isStackOnSite_iff_representable_isSheaf]
        exact
          (isSheaf_iff_isSheaf_of_type J_fppf (yoneda.obj U)).2
            (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj U))
      toIsFibredInGroupoids := inferInstance }

/- The fixed-site ambient owner for the algebraic-stack example is the `2`-category of stacks in
groupoids on the fppf site over `Xscheme`. Representable objects in this owner are the canonical
stacks `X/U` obtained from the slice projections `Over.forget U`. -/
#check J_fppf
#check StackInGroupoidsOver J_fppf

/- The slice projection over an object of `Over Xscheme` is a stack in groupoids for the induced
fppf topology on `Over Xscheme`, so the canonical representable stack `X/U` is obtained directly
from `StackInGroupoidsOver.ofProjection`; no extra named instance is part of the public API. -/
#check StackInGroupoidsOver.ofProjection J_fppf (Over.forget U)

/- For a stack in groupoids `𝒳` on the fppf site over `Xscheme`, the source-facing algebraic-stack
conditions live directly on the owner surface: the base projection has representable diagonal,
and some representable stack `X/U` admits an atlas morphism that is locally essentially
surjective on objects. -/
#check 𝒳.toFibredInGroupoidsOver.baseProjection.diagonalMor.IsRepresentable
#check ∃ (U : Over Xscheme)
    (p : StackInGroupoidsOver.ofProjection J_fppf (Over.forget U) ⟶ 𝒳),
      p.LocallyEssentiallySurjectiveOnObjects

/- The slice criterion from Lemma 4.42.6 remains the companion reformulation of the diagonal
condition, rather than the main owner-level algebraic-stack surface. -/
#check representable_diagonal_iff_all_slice_morphisms_representable

end AlgebraicStacks

end CategoryTheory

/-! ### Definition_4_29_4 (from Chap04) -/
universe w v u

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B]
variable (x y : B)

/- Domain-style sampling for Definition 4.29.4:
- `Bicategory.Equivalence` is the canonical owner object for equivalences in a
  bicategory, with notation `x ≌ y`.
- `Bicategory.Equivalence.mkOfAdjointifyCounit` is the canonical constructor from a pair of
  quasi-inverse `1`-morphisms and unit/counit `2`-isomorphisms.
- `Bicategory.Equivalence.id` is the canonical identity example of that owner object.
- `Bicategory.Adjunction` is the surrounding owner-level API from which bicategorical
  equivalences inherit their triangle data.
- The fields `hom`, `inv`, `unit`, and `counit` are the primitive bicategorical data; any
  existential “there exist morphisms with invertible `2`-morphisms” formulation is derived API.

Primitive-vs-derived split:
- primitive data: none in this file; the notion is already owned upstream by
  `Bicategory.Equivalence`.
- derived API: the canonical constructor `Equivalence.mkOfAdjointifyCounit`, which assembles the
  textbook quasi-inverse data into the owner object. -/

/- Source/core/bridge triage for Definition 4.29.4:
- `source-facing`: the textbook quasi-inverse formulation of equivalence in a `2`-category.
- `core/canonical`: the owner object `x ≌ y`.
- `bridge/view`: the canonical constructor `Equivalence.mkOfAdjointifyCounit`. -/

/- Definition 4.29.4: for objects `x` and `y` of a `2`-category, the assertion that `x` and `y`
are equivalent is the canonical bicategorical notion `Bicategory.Equivalence x y`, written
`x ≌ y`. This packages `1`-morphisms `x ⟶ y` and `y ⟶ x` together with the required
invertible `2`-morphisms exhibiting the two composites as identities. -/
#check (x ≌ y)

/- Companion bridge: the textbook quasi-inverse data are assembled directly into the canonical
owner object by `Equivalence.mkOfAdjointifyCounit`; no parallel local existence wrapper is
needed. -/
recall Equivalence.mkOfAdjointifyCounit

end CategoryTheory

/-! ### Definition_4_29_5 (from Chap04) -/
universe w v u₁ u₂

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {A : Type u₁} [Category.{v} A]

/- Domain-style sampling for Definition 4.29.5:
- `LocallyDiscrete.mkPseudofunctor` is the canonical constructor from the textbook object map,
  morphism map, and invertible unit/composition comparison data.
- `Functor.toPseudofunctor'` is the canonical bridge from an ordinary functor into a strict
  `2`-category to the corresponding weak functor.
- `PullbackChoice.fiberPseudofunctor` is the chapter's downstream project use of that same owner
  abstraction `LocallyDiscrete _ ⥤ᵖ _`.
- `Functor.IsSplitFibredCategory` later reuses `Functor.toPseudofunctor'` rather than introducing
  a parallel weak-functor wrapper.

Primitive-vs-derived split:
- primitive data: a weak functor is a pseudofunctor `LocallyDiscrete A ⥤ᵖ C`; its primitive fields
  are the object map, `1`-morphism map, `mapId`, `mapComp`, and the three coherence axioms.
- derived API: `LocallyDiscrete.mkPseudofunctor` packages the textbook data into that owner, while
  `Functor.toPseudofunctor'` is the additional bridge that requires strictness of the target. -/

/- Source/core/bridge triage for Definition 4.29.5:
- `source-facing`: the textbook notions of ordinary and weak functors from `A` to the strict
  `2`-category `C`.
- `core/canonical`: ordinary functors `A ⥤ C` and pseudofunctors `LocallyDiscrete A ⥤ᵖ C`.
- `bridge/view`: `LocallyDiscrete.mkPseudofunctor` and, under the extra strictness hypothesis,
  `Functor.toPseudofunctor'`. -/

section Core

variable {C : Type u₂} [Category.{v} C] [Bicategory.{w, v} C]

/- Definition 4.29.5 (1): a functor from an ordinary category `A` into a strict `2`-category `C`
is just an ordinary functor into the underlying category of `C`, i.e. an element of `A ⥤ C`. -/
#check (A ⥤ C)

/- Definition 4.29.5 (2): the canonical Lean notion of a weak functor from an ordinary category
`A` to a strict `2`-category `C` is a pseudofunctor `LocallyDiscrete A ⥤ᵖ C`. -/
#check (LocallyDiscrete A ⥤ᵖ C)

/- The textbook object map, morphism map, invertible unit and composition `2`-morphisms, and
coherence axioms are assembled by the existing constructor `LocallyDiscrete.mkPseudofunctor`. Its
field `mapId` uses mathlib's standard pseudofunctor orientation `φ (𝟙 a) ≅ 𝟙 (φ a)`, so the
Stacks-project unit comparison `αₐ : 𝟙 (φ a) ⟶ φ (𝟙 a)` is the inverse isomorphism. No parallel
local wrapper API is needed: the source-facing coherence equalities are already exactly the
constructor arguments of `LocallyDiscrete.mkPseudofunctor`. -/
recall LocallyDiscrete.mkPseudofunctor

end Core

section StrictBridge

variable {C : Type u₂} [Bicategory.{w, v} C] [Strict C]

/- Under the strictness hypothesis from the source text, any ordinary functor into `C`
canonically promotes to the corresponding weak functor from `LocallyDiscrete A`. This is a
derived bridge, not the owner of the notion. -/
recall Functor.toPseudofunctor'

end StrictBridge

end CategoryTheory

/-! ### Definition_4_29_6 (from Chap04) -/
universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace StrictPseudofunctor

/-- Two strict `2`-functors are inverse when they are mutually inverse on objects,
`1`-morphisms, and `2`-morphisms. The morphism identities are expressed using heterogeneous
equality because the inverse-object equalities need not be definitional. -/
structure IsInverse
    {B : Type u₁} [Bicategory.{w₁, v₁} B] [Bicategory.Strict B]
    {C : Type u₂} [Bicategory.{w₂, v₂} C] [Bicategory.Strict C]
    (F : StrictPseudofunctor B C) (G : StrictPseudofunctor C B) : Prop where
  left_obj : ∀ X : B, G.obj (F.obj X) = X
  left_map : ∀ ⦃X Y : B⦄ (f : X ⟶ Y), G.map (F.map f) ≍ f
  left_map₂ : ∀ ⦃X Y : B⦄ {f g : X ⟶ Y} (η : f ⟶ g), G.map₂ (F.map₂ η) ≍ η
  right_obj : ∀ X : C, F.obj (G.obj X) = X
  right_map : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), F.map (G.map f) ≍ f
  right_map₂ : ∀ ⦃X Y : C⦄ {f g : X ⟶ Y} (η : f ⟶ g), F.map₂ (G.map₂ η) ≍ η

end StrictPseudofunctor

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] [Bicategory.Strict B]

/-- The underlying objects of Definition 4.29.6 are the arrows into a fixed object `X` of the
ambient strict `2`-category `B`. -/
@[ext]
structure SliceTwoCategory (X : B) where
  obj : B
  hom : obj ⟶ X

namespace SliceTwoCategory

variable {X : B}

/-- A `1`-morphism in the slice strict `2`-category over `X`. -/
@[ext]
structure Hom (S T : SliceTwoCategory X) where
  hom : S.obj ⟶ T.obj
  comm : hom ≫ T.hom = S.hom

/-- A `2`-morphism in the slice strict `2`-category over `X`. -/
@[ext]
structure TwoHom {S T : SliceTwoCategory X} (F G : Hom S T) where
  hom : F.hom ⟶ G.hom
  comm : hom ▷ T.hom ≫ eqToHom G.comm = eqToHom F.comm

private def idHom (S : SliceTwoCategory X) : Hom S S where
  hom := 𝟙 S.obj
  comm := by simp

private def compHom {S T U : SliceTwoCategory X} (F : Hom S T) (G : Hom T U) : Hom S U where
  hom := F.hom ≫ G.hom
  comm := by
    simp [Category.assoc, F.comm, G.comm]

private def idTwoHom {S T : SliceTwoCategory X} (F : Hom S T) : TwoHom F F where
  hom := 𝟙 F.hom
  comm := by
    simpa using congrArg (fun α ↦ α ≫ eqToHom F.comm) (id_whiskerRight F.hom T.hom)

/-- Helper for Definition 4.29.6: vertical composition of slice `2`-cells still lies over the
identity on the base object. -/
private theorem compTwoHom_comm {S T : SliceTwoCategory X} {F G H : Hom S T}
    (η : TwoHom F G) (θ : TwoHom G H) :
    (η.hom ≫ θ.hom) ▷ T.hom ≫ eqToHom H.comm = eqToHom F.comm := by
  -- Vertical composition in the slice is the ambient vertical composition followed by the two
  -- already-known commutativity squares.
  rw [Bicategory.comp_whiskerRight]
  simp [Category.assoc, θ.comm, η.comm]

private def compTwoHom {S T : SliceTwoCategory X} {F G H : Hom S T}
    (η : TwoHom F G) (θ : TwoHom G H) : TwoHom F H where
  hom := η.hom ≫ θ.hom
  comm := compTwoHom_comm η θ

instance (S T : SliceTwoCategory X) : Category (Hom S T) where
  Hom F G := TwoHom F G
  id := idTwoHom
  comp := compTwoHom
  id_comp := by
    intro F G η
    -- Equality of slice `2`-cells is detected on the ambient `2`-cell component.
    ext
    simp [compTwoHom, idTwoHom]
  comp_id := by
    intro F G η
    -- The right identity law is the same ambient categorical identity law.
    ext
    simp [compTwoHom, idTwoHom]
  assoc := by
    intro F G H I η θ μ
    -- Associativity is inherited verbatim from the ambient hom-category.
    ext
    simp [compTwoHom, Category.assoc]

/-- Helper for Definition 4.29.6: left whiskering preserves the slice-over-`X` compatibility
condition for `2`-morphisms. -/
private theorem whiskerLeftTwoHom_comm {S T U : SliceTwoCategory X} (F : Hom S T) {G H : Hom T U}
    (η : TwoHom G H) :
    (F.hom ◁ η.hom) ▷ U.hom ≫ eqToHom (compHom F H).comm = eqToHom (compHom F G).comm := by
  -- First rewrite right whiskering of a left whisker using the ambient associator, then transport
  -- the defining relation of `η` through left whiskering by `F.hom`.
  calc
    (F.hom ◁ η.hom) ▷ U.hom ≫ eqToHom (compHom F H).comm
        = (α_ F.hom G.hom U.hom).hom ≫ F.hom ◁ (η.hom ▷ U.hom) ≫
            (α_ F.hom H.hom U.hom).inv ≫ eqToHom (compHom F H).comm := by
              simpa [Category.assoc] using Bicategory.whisker_assoc F.hom η.hom U.hom
    _ = (α_ F.hom G.hom U.hom).hom ≫ (F.hom ◁ (η.hom ▷ U.hom) ≫ F.hom ◁ eqToHom H.comm) ≫
          eqToHom F.comm := by
            simp [Category.assoc, Strict.associator_eqToIso]
    _ = (α_ F.hom G.hom U.hom).hom ≫ F.hom ◁ (η.hom ▷ U.hom ≫ eqToHom H.comm) ≫
          eqToHom F.comm := by
            rw [← Bicategory.whiskerLeft_comp]
    _ = (α_ F.hom G.hom U.hom).hom ≫ F.hom ◁ eqToHom G.comm ≫ eqToHom F.comm := by
          exact congrArg (fun β ↦ (α_ F.hom G.hom U.hom).hom ≫ F.hom ◁ β ≫ eqToHom F.comm) η.comm
    _ = eqToHom (compHom F G).comm := by
          simp [compHom, Strict.associator_eqToIso]

private def whiskerLeftTwoHom {S T U : SliceTwoCategory X} (F : Hom S T) {G H : Hom T U}
    (η : TwoHom G H) : TwoHom (compHom F G) (compHom F H) where
  hom := F.hom ◁ η.hom
  comm := whiskerLeftTwoHom_comm F η

/-- Helper for Definition 4.29.6: right whiskering preserves the slice-over-`X` compatibility
condition for `2`-morphisms. -/
private theorem whiskerRightTwoHom_comm {S T U : SliceTwoCategory X} {F G : Hom S T}
    (η : TwoHom F G) (H : Hom T U) :
    η.hom ▷ H.hom ▷ U.hom ≫ eqToHom (compHom G H).comm = eqToHom (compHom F H).comm := by
  -- Reassociate to the right-whiskered normal form, use the slice relation for `η`, and then
  -- collapse the ambient associators back to the target slice equality.
  calc
    η.hom ▷ H.hom ▷ U.hom ≫ eqToHom (compHom G H).comm
        = η.hom ▷ H.hom ▷ U.hom ≫ (α_ G.hom H.hom U.hom).hom ≫
            G.hom ◁ eqToHom H.comm ≫ eqToHom G.comm := by
              simp [Strict.associator_eqToIso]
    _ = (α_ F.hom H.hom U.hom).hom ≫ η.hom ▷ (H.hom ≫ U.hom) ≫
          G.hom ◁ eqToHom H.comm ≫ eqToHom G.comm := by
            rw [associator_naturality_left_assoc]
    _ = (α_ F.hom H.hom U.hom).hom ≫ (F.hom ◁ eqToHom H.comm ≫ η.hom ▷ T.hom) ≫
          eqToHom G.comm := by
            rw [← whisker_exchange_assoc]
            simp [Category.assoc]
    _ = (α_ F.hom H.hom U.hom).hom ≫ F.hom ◁ eqToHom H.comm ≫ eqToHom F.comm := by
          simpa [Category.assoc] using
            congrArg (fun α ↦ (α_ F.hom H.hom U.hom).hom ≫ F.hom ◁ eqToHom H.comm ≫ α) η.comm
    _ = eqToHom (compHom F H).comm := by
          simp [compHom, Strict.associator_eqToIso]

private def whiskerRightTwoHom {S T U : SliceTwoCategory X} {F G : Hom S T}
    (η : TwoHom F G) (H : Hom T U) : TwoHom (compHom F H) (compHom G H) where
  hom := η.hom ▷ H.hom
  comm := whiskerRightTwoHom_comm η H

/-- Helper for Definition 4.29.6: the ambient associator `2`-cell is compatible with the slice
triangle over `X`. -/
private theorem associatorIso_hom_comm {R S T U : SliceTwoCategory X}
    (F : Hom R S) (G : Hom S T) (H : Hom T U) :
    (α_ F.hom G.hom H.hom).hom ▷ U.hom ≫ eqToHom (compHom F (compHom G H)).comm =
      eqToHom (compHom (compHom F G) H).comm := by
  -- The slice associator is exactly the ambient associator on the underlying arrows.
  simp [compHom, Strict.associator_eqToIso]

/-- Helper for Definition 4.29.6: the inverse ambient associator `2`-cell is compatible with the
slice triangle over `X`. -/
private theorem associatorIso_inv_comm {R S T U : SliceTwoCategory X}
    (F : Hom R S) (G : Hom S T) (H : Hom T U) :
    (α_ F.hom G.hom H.hom).inv ▷ U.hom ≫ eqToHom (compHom (compHom F G) H).comm =
      eqToHom (compHom F (compHom G H)).comm := by
  -- The inverse associator satisfies the same compatibility relation.
  simp [compHom, Strict.associator_eqToIso]

/-- Helper for Definition 4.29.6: the forward slice associator `2`-cell. -/
private def associatorTwoHom {R S T U : SliceTwoCategory X}
    (F : Hom R S) (G : Hom S T) (H : Hom T U) :
    TwoHom (compHom (compHom F G) H) (compHom F (compHom G H)) :=
  { hom := (α_ F.hom G.hom H.hom).hom
    comm := associatorIso_hom_comm F G H }

/-- Helper for Definition 4.29.6: the inverse slice associator `2`-cell. -/
private def associatorInvTwoHom {R S T U : SliceTwoCategory X}
    (F : Hom R S) (G : Hom S T) (H : Hom T U) :
    TwoHom (compHom F (compHom G H)) (compHom (compHom F G) H) :=
  { hom := (α_ F.hom G.hom H.hom).inv
    comm := associatorIso_inv_comm F G H }

/-- Helper for Definition 4.29.6: the slice associator has the expected ambient inverse law on
its `hom` component. -/
private theorem associatorIso_hom_inv_id {R S T U : SliceTwoCategory X}
    (F : Hom R S) (G : Hom S T) (H : Hom T U) :
    associatorTwoHom F G H ≫ associatorInvTwoHom F G H =
      𝟙 (compHom (compHom F G) H) := by
  -- Equality of slice `2`-cells is detected on the ambient `2`-cell component.
  apply TwoHom.ext
  change (α_ F.hom G.hom H.hom).hom ≫ (α_ F.hom G.hom H.hom).inv =
      𝟙 ((compHom (compHom F G) H).hom)
  simpa [compHom] using Iso.hom_inv_id (α_ F.hom G.hom H.hom)

/-- Helper for Definition 4.29.6: the slice associator has the expected ambient inverse law on
its `inv` component. -/
private theorem associatorIso_inv_hom_id {R S T U : SliceTwoCategory X}
    (F : Hom R S) (G : Hom S T) (H : Hom T U) :
    associatorInvTwoHom F G H ≫ associatorTwoHom F G H =
      𝟙 (compHom F (compHom G H)) := by
  -- The opposite inverse law is the same ambient inverse identity.
  apply TwoHom.ext
  change (α_ F.hom G.hom H.hom).inv ≫ (α_ F.hom G.hom H.hom).hom =
      𝟙 ((compHom F (compHom G H)).hom)
  simpa [compHom] using Iso.inv_hom_id (α_ F.hom G.hom H.hom)

private def associatorIso {R S T U : SliceTwoCategory X}
    (F : Hom R S) (G : Hom S T) (H : Hom T U) :
    compHom (compHom F G) H ≅ compHom F (compHom G H) where
  hom := associatorTwoHom F G H
  inv := associatorInvTwoHom F G H
  hom_inv_id := associatorIso_hom_inv_id F G H
  inv_hom_id := associatorIso_inv_hom_id F G H

/-- Helper for Definition 4.29.6: the ambient left unitor is compatible with the slice triangle
over `X`. -/
private theorem leftUnitorIso_hom_comm {S T : SliceTwoCategory X} (F : Hom S T) :
    (λ_ F.hom).hom ▷ T.hom ≫ eqToHom F.comm = eqToHom (compHom (idHom S) F).comm := by
  -- The slice left unitor is inherited from the ambient left unitor.
  simp [idHom, compHom, Strict.leftUnitor_eqToIso]

/-- Helper for Definition 4.29.6: the inverse ambient left unitor is compatible with the slice
triangle over `X`. -/
private theorem leftUnitorIso_inv_comm {S T : SliceTwoCategory X} (F : Hom S T) :
    (λ_ F.hom).inv ▷ T.hom ≫ eqToHom (compHom (idHom S) F).comm = eqToHom F.comm := by
  -- The inverse left unitor satisfies the same compatibility relation.
  simp [Strict.leftUnitor_eqToIso]

/-- Helper for Definition 4.29.6: the forward slice left unitor `2`-cell. -/
private def leftUnitorTwoHom {S T : SliceTwoCategory X} (F : Hom S T) :
    TwoHom (compHom (idHom S) F) F :=
  { hom := (λ_ F.hom).hom
    comm := leftUnitorIso_hom_comm F }

/-- Helper for Definition 4.29.6: the inverse slice left unitor `2`-cell. -/
private def leftUnitorInvTwoHom {S T : SliceTwoCategory X} (F : Hom S T) :
    TwoHom F (compHom (idHom S) F) :=
  { hom := (λ_ F.hom).inv
    comm := leftUnitorIso_inv_comm F }

/-- Helper for Definition 4.29.6: the slice left unitor satisfies the ambient inverse law on its
`hom` component. -/
private theorem leftUnitorIso_hom_inv_id {S T : SliceTwoCategory X} (F : Hom S T) :
    leftUnitorTwoHom F ≫ leftUnitorInvTwoHom F =
      𝟙 (compHom (idHom S) F) := by
  -- Equality of slice `2`-cells is detected on the ambient `2`-cell component.
  apply TwoHom.ext
  change (λ_ F.hom).hom ≫ (λ_ F.hom).inv = 𝟙 ((compHom (idHom S) F).hom)
  simpa [idHom, compHom] using Iso.hom_inv_id (λ_ F.hom)

/-- Helper for Definition 4.29.6: the slice left unitor satisfies the ambient inverse law on its
`inv` component. -/
private theorem leftUnitorIso_inv_hom_id {S T : SliceTwoCategory X} (F : Hom S T) :
    leftUnitorInvTwoHom F ≫ leftUnitorTwoHom F =
      𝟙 F := by
  -- The opposite inverse law is the same ambient inverse identity.
  apply TwoHom.ext
  change (λ_ F.hom).inv ≫ (λ_ F.hom).hom = 𝟙 F.hom
  simpa [Strict.leftUnitor_eqToIso] using Iso.inv_hom_id (λ_ F.hom)

private def leftUnitorIso {S T : SliceTwoCategory X} (F : Hom S T) :
    compHom (idHom S) F ≅ F where
  hom := leftUnitorTwoHom F
  inv := leftUnitorInvTwoHom F
  hom_inv_id := leftUnitorIso_hom_inv_id F
  inv_hom_id := leftUnitorIso_inv_hom_id F

/-- Helper for Definition 4.29.6: the ambient right unitor is compatible with the slice triangle
over `X`. -/
private theorem rightUnitorIso_hom_comm {S T : SliceTwoCategory X} (F : Hom S T) :
    (ρ_ F.hom).hom ▷ T.hom ≫ eqToHom F.comm = eqToHom (compHom F (idHom T)).comm := by
  -- The slice right unitor is inherited from the ambient right unitor.
  simp [idHom, compHom, Strict.rightUnitor_eqToIso]

/-- Helper for Definition 4.29.6: the inverse ambient right unitor is compatible with the slice
triangle over `X`. -/
private theorem rightUnitorIso_inv_comm {S T : SliceTwoCategory X} (F : Hom S T) :
    (ρ_ F.hom).inv ▷ T.hom ≫ eqToHom (compHom F (idHom T)).comm = eqToHom F.comm := by
  -- The inverse right unitor satisfies the same compatibility relation.
  simp [Strict.rightUnitor_eqToIso]

/-- Helper for Definition 4.29.6: the forward slice right unitor `2`-cell. -/
private def rightUnitorTwoHom {S T : SliceTwoCategory X} (F : Hom S T) :
    TwoHom (compHom F (idHom T)) F :=
  { hom := (ρ_ F.hom).hom
    comm := rightUnitorIso_hom_comm F }

/-- Helper for Definition 4.29.6: the inverse slice right unitor `2`-cell. -/
private def rightUnitorInvTwoHom {S T : SliceTwoCategory X} (F : Hom S T) :
    TwoHom F (compHom F (idHom T)) :=
  { hom := (ρ_ F.hom).inv
    comm := rightUnitorIso_inv_comm F }

/-- Helper for Definition 4.29.6: the slice right unitor satisfies the ambient inverse law on its
`hom` component. -/
private theorem rightUnitorIso_hom_inv_id {S T : SliceTwoCategory X} (F : Hom S T) :
    rightUnitorTwoHom F ≫ rightUnitorInvTwoHom F =
      𝟙 (compHom F (idHom T)) := by
  -- Equality of slice `2`-cells is detected on the ambient `2`-cell component.
  apply TwoHom.ext
  change (ρ_ F.hom).hom ≫ (ρ_ F.hom).inv = 𝟙 ((compHom F (idHom T)).hom)
  simpa [idHom, compHom] using Iso.hom_inv_id (ρ_ F.hom)

/-- Helper for Definition 4.29.6: the slice right unitor satisfies the ambient inverse law on its
`inv` component. -/
private theorem rightUnitorIso_inv_hom_id {S T : SliceTwoCategory X} (F : Hom S T) :
    rightUnitorInvTwoHom F ≫ rightUnitorTwoHom F =
      𝟙 F := by
  -- The opposite inverse law is the same ambient inverse identity.
  apply TwoHom.ext
  change (ρ_ F.hom).inv ≫ (ρ_ F.hom).hom = 𝟙 F.hom
  simpa [Strict.rightUnitor_eqToIso] using Iso.inv_hom_id (ρ_ F.hom)

private def rightUnitorIso {S T : SliceTwoCategory X} (F : Hom S T) :
    compHom F (idHom T) ≅ F where
  hom := rightUnitorTwoHom F
  inv := rightUnitorInvTwoHom F
  hom_inv_id := rightUnitorIso_hom_inv_id F
  inv_hom_id := rightUnitorIso_inv_hom_id F

instance instBicategory : Bicategory (SliceTwoCategory X) where
  Hom S T := Hom S T
  homCategory S T := inferInstance
  id := idHom
  comp := compHom
  whiskerLeft := whiskerLeftTwoHom
  whiskerRight := whiskerRightTwoHom
  associator := associatorIso
  leftUnitor := leftUnitorIso
  rightUnitor := rightUnitorIso
  whisker_exchange := by
    intro R S T F G H I η θ
    -- The exchange law is inherited verbatim from the ambient bicategory on underlying arrows.
    apply TwoHom.ext
    change F.hom ◁ θ.hom ≫ η.hom ▷ I.hom = η.hom ▷ H.hom ≫ G.hom ◁ θ.hom
    simpa using CategoryTheory.Bicategory.whisker_exchange η.hom θ.hom
  whiskerLeft_id := by
    intro R S T F G
    -- Left whiskering preserves identity `2`-cells componentwise.
    apply TwoHom.ext
    change F.hom ◁ 𝟙 G.hom = 𝟙 ((compHom F G).hom)
    simpa [whiskerLeftTwoHom, compHom, idTwoHom] using Bicategory.whiskerLeft_id F.hom G.hom
  whiskerLeft_comp := by
    intro R S T F G H I η θ
    -- Left whiskering preserves vertical composition on the underlying ambient `2`-cell.
    apply TwoHom.ext
    change F.hom ◁ (η.hom ≫ θ.hom) = (F.hom ◁ η.hom) ≫ F.hom ◁ θ.hom
    simpa [whiskerLeftTwoHom, compTwoHom] using Bicategory.whiskerLeft_comp F.hom η.hom θ.hom
  id_whiskerLeft := by
    intro S T F G η
    -- The slice left whiskering by an identity reduces to the ambient left-unitor law.
    apply TwoHom.ext
    change (𝟙 S.obj ◁ η.hom) = (λ_ F.hom).hom ≫ η.hom ≫ (λ_ G.hom).inv
    simpa [whiskerLeftTwoHom, idHom, compHom] using Bicategory.id_whiskerLeft η.hom
  comp_whiskerLeft := by
    intro R S T U F G H H' η
    -- Left whiskering by a composite is inherited componentwise from the ambient bicategory.
    apply TwoHom.ext
    change (F.hom ≫ G.hom) ◁ η.hom =
      (α_ F.hom G.hom H.hom).hom ≫ F.hom ◁ (G.hom ◁ η.hom) ≫
        (α_ F.hom G.hom H'.hom).inv
    simpa [whiskerLeftTwoHom, compHom] using Bicategory.comp_whiskerLeft F.hom G.hom η.hom
  id_whiskerRight := by
    intro R S T F G
    -- Right whiskering preserves identity `2`-cells componentwise.
    apply TwoHom.ext
    change 𝟙 F.hom ▷ G.hom = 𝟙 ((compHom F G).hom)
    simpa [whiskerRightTwoHom, compHom, idTwoHom] using Bicategory.id_whiskerRight F.hom G.hom
  comp_whiskerRight := by
    intro R S T F G H η θ I
    -- Right whiskering preserves vertical composition on the underlying ambient `2`-cell.
    apply TwoHom.ext
    change (η.hom ≫ θ.hom) ▷ I.hom = η.hom ▷ I.hom ≫ θ.hom ▷ I.hom
    simpa [whiskerRightTwoHom, compTwoHom] using Bicategory.comp_whiskerRight η.hom θ.hom I.hom
  whiskerRight_id := by
    intro S T F G η
    -- The slice right whiskering by an identity reduces to the ambient right-unitor law.
    apply TwoHom.ext
    change η.hom ▷ 𝟙 T.obj = (ρ_ F.hom).hom ≫ η.hom ≫ (ρ_ G.hom).inv
    simpa [whiskerRightTwoHom, idHom, compHom] using Bicategory.whiskerRight_id η.hom
  whiskerRight_comp := by
    intro R S T U F F' η G H
    -- Right whiskering by a composite is inherited componentwise from the ambient bicategory.
    apply TwoHom.ext
    change η.hom ▷ (G.hom ≫ H.hom) =
      (α_ F.hom G.hom H.hom).inv ≫ (η.hom ▷ G.hom) ▷ H.hom ≫
        (α_ F'.hom G.hom H.hom).hom
    simpa [whiskerRightTwoHom, compHom] using Bicategory.whiskerRight_comp η.hom G.hom H.hom
  whisker_assoc := by
    intro R S T U F G G' η H
    -- Compatibility of left and right whiskering is inherited from the ambient bicategory.
    apply TwoHom.ext
    change (F.hom ◁ η.hom) ▷ H.hom =
      (α_ F.hom G.hom H.hom).hom ≫ F.hom ◁ (η.hom ▷ H.hom) ≫
        (α_ F.hom G'.hom H.hom).inv
    simpa [whiskerLeftTwoHom, whiskerRightTwoHom, compHom] using
      Bicategory.whisker_assoc F.hom η.hom H.hom
  pentagon := by
    intro Q R S T U F G H I
    -- The pentagon coherence law reduces to the ambient one on underlying arrows.
    apply TwoHom.ext
    change (α_ F.hom G.hom H.hom).hom ▷ I.hom ≫
        (α_ F.hom (G.hom ≫ H.hom) I.hom).hom ≫ F.hom ◁ (α_ G.hom H.hom I.hom).hom =
      (α_ (F.hom ≫ G.hom) H.hom I.hom).hom ≫ (α_ F.hom G.hom (H.hom ≫ I.hom)).hom
    simpa [compHom] using Bicategory.pentagon F.hom G.hom H.hom I.hom
  triangle := by
    intro R S T F G
    -- The triangle coherence law is likewise inherited from the ambient bicategory.
    apply TwoHom.ext
    change (α_ F.hom (𝟙 S.obj) G.hom).hom ≫ F.hom ◁ (λ_ G.hom).hom =
      (ρ_ F.hom).hom ▷ G.hom
    simpa [whiskerLeftTwoHom, whiskerRightTwoHom, idHom, compHom] using
      Bicategory.triangle F.hom G.hom

/-- Helper for Definition 4.29.6: the ambient `2`-cell component of `eqToHom` between slice
`1`-morphisms is the `eqToHom` of the induced equality on underlying arrows. -/
private theorem eqToHom_hom_component {S T : SliceTwoCategory X} {F G : Hom S T} (h : F = G) :
    (eqToHom h).hom = eqToHom (congrArg Hom.hom h) := by
  cases h
  rfl

/-- Helper for Definition 4.29.6: slice composition with an identity on the left is strictly
unital. -/
private theorem strict_id_comp_hom {S T : SliceTwoCategory X} (F : Hom S T) :
    𝟙 S ≫ F = F := by
  -- Equality of slice `1`-morphisms is detected on the underlying ambient arrow.
  apply Hom.ext
  change 𝟙 S.obj ≫ F.hom = F.hom
  exact Strict.id_comp F.hom

/-- Helper for Definition 4.29.6: slice composition with an identity on the right is strictly
unital. -/
private theorem strict_comp_id_hom {S T : SliceTwoCategory X} (F : Hom S T) :
    F ≫ 𝟙 T = F := by
  -- Equality of slice `1`-morphisms is detected on the underlying ambient arrow.
  apply Hom.ext
  change F.hom ≫ 𝟙 T.obj = F.hom
  exact Strict.comp_id F.hom

/-- Helper for Definition 4.29.6: slice composition is strictly associative on underlying
arrows. -/
private theorem strict_assoc_hom {R S T U : SliceTwoCategory X}
    (F : Hom R S) (G : Hom S T) (H : Hom T U) :
    compHom (compHom F G) H = compHom F (compHom G H) := by
  -- Equality of slice `1`-morphisms is detected on the underlying ambient arrow.
  apply Hom.ext
  change (F.hom ≫ G.hom) ≫ H.hom = F.hom ≫ G.hom ≫ H.hom
  exact Strict.assoc F.hom G.hom H.hom

/-- Definition 4.29.6: the slice over `X` inherits a canonical strict `2`-category structure
from the ambient strict `2`-category `B`. -/
instance instStrict : Bicategory.Strict (SliceTwoCategory X) where
  id_comp := by
    intro S T F
    -- Reuse the strict left-unital slice equality proved just above.
    exact strict_id_comp_hom F
  comp_id := by
    intro S T F
    -- Reuse the strict right-unital slice equality proved just above.
    exact strict_comp_id_hom F
  assoc := by
    intro R S T U F G H
    -- Reuse the strict associativity equality proved just above.
    change compHom (compHom F G) H = compHom F (compHom G H)
    exact strict_assoc_hom F G H
  leftUnitor_eqToIso := by
    intro S T F
    -- Compare the slice isomorphisms on the underlying ambient `2`-cell component.
    apply Iso.ext
    apply TwoHom.ext
    have hhom : congrArg Hom.hom (strict_id_comp_hom F) = Strict.id_comp F.hom := by
      exact Subsingleton.elim _ _
    rw [eqToIso.hom, eqToHom_hom_component, hhom]
    simpa using congrArg Iso.hom (Strict.leftUnitor_eqToIso F.hom)
  rightUnitor_eqToIso := by
    intro S T F
    -- Compare the slice isomorphisms on the underlying ambient `2`-cell component.
    apply Iso.ext
    apply TwoHom.ext
    have hhom : congrArg Hom.hom (strict_comp_id_hom F) = Strict.comp_id F.hom := by
      exact Subsingleton.elim _ _
    rw [eqToIso.hom, eqToHom_hom_component, hhom]
    simpa using congrArg Iso.hom (Strict.rightUnitor_eqToIso F.hom)
  associator_eqToIso := by
    intro Q R S T F G H
    -- Compare the slice isomorphisms on the underlying ambient `2`-cell component.
    apply Iso.ext
    apply TwoHom.ext
    have hhom :
        congrArg Hom.hom (strict_assoc_hom F G H) = Strict.assoc F.hom G.hom H.hom := by
      exact Subsingleton.elim _ _
    rw [eqToIso.hom, eqToHom_hom_component]
    change (α_ F G H).hom.hom = eqToHom (congrArg Hom.hom (strict_assoc_hom F G H))
    rw [hhom]
    simpa using congrArg Iso.hom (Strict.associator_eqToIso F.hom G.hom H.hom)

end SliceTwoCategory

end CategoryTheory
