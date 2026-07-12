import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ w uInv uPush

namespace CategoryTheory

section

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)

/- Companion recall: a topos presented by a site with Grothendieck topology `J` is the category
`Sheaf J (Type w)` of set-valued sheaves on that site. -/
#check (Sheaf J (Type w))

end

/- Domain-style sampling for Definition 7.15.1:
- primary domain: geometric morphisms of topoi, presented here by set-valued sheaf categories on
  sites;
- sampled owner API:
  `LeftExactFunctor.of`,
  `Adjunction.id`,
  `Adjunction.comp`,
  `Functor.sheafAdjunctionContinuous`;
- source/core/bridge triage:
  `source-facing`: `MorphismOfTopoiIn J K`, i.e. a morphism `Sh(K) ⟶ Sh(J)` presented by sites;
  `core/canonical`: the neutral owner `LeftExactAdjunction C D`, packaging a left-exact functor
    `D ⥤ C` together with a chosen right adjoint and adjunction data;
  `bridge/view`: `MorphismOfTopoiIn J K` is the specialization
    `LeftExactAdjunction (Sheaf K (Type w)) (Sheaf J (Type w))`, together with the source-facing
    inverse-image notation `f⁻¹`.

Primitive data are the bundled left-exact inverse-image functor, the direct-image functor, and
their adjunction. The generic owner is kept because it has genuine downstream use beyond the
site-presented case, while the site-specific owner remains the public source-facing API for this
chapter. -/
/-- A chosen right-adjoint package for a left-exact functor `D ⥤ C`. -/
structure LeftExactAdjunction
    (C : Type u₁) [Category.{v₁} C]
    (D : Type u₂) [Category.{v₂} D] where
  /-- The bundled left-exact inverse image functor `f⁻¹ : D ⥤ C`. -/
  inverseImageFunctor : D ⥤ₗ C
  /-- The direct image functor `f_* : C ⥤ D`. -/
  pushforward : C ⥤ D
  /-- The adjunction `f⁻¹ ⊣ f_*`. -/
  adjunction : inverseImageFunctor.obj ⊣ pushforward

/-- A value carrying a canonical inverse-image functor. -/
class HasInverseImage {α : Sort _} (x : α) where
  Inv : outParam (Sort uInv)
  inverseImage : Inv

/-- A value carrying a canonical direct-image functor. -/
class HasPushforward {α : Sort _} (x : α) where
  Push : outParam (Sort uPush)
  pushforward : Push

/-- The inverse-image functor attached to a value with a canonical inverse image. -/
abbrev inverseImage {α : Sort _} (x : α) [h : HasInverseImage x] : h.Inv :=
  h.inverseImage

/-- The direct-image functor attached to a value with a canonical pushforward. -/
abbrev pushforward {α : Sort _} (x : α) [h : HasPushforward x] : h.Push :=
  h.pushforward

namespace LeftExactAdjunction

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]

/-- The underlying left-exact functor. -/
abbrev inverseImage (f : LeftExactAdjunction A B) : B ⥤ A :=
  f.inverseImageFunctor.obj

/-- A left-exact adjunction is canonically viewed as its left-exact functor. -/
instance : CoeOut (LeftExactAdjunction A B) (B ⥤ A) where
  coe f := f.inverseImage

/-- The inverse-image functor in a left-exact adjunction is a left adjoint. -/
instance (f : LeftExactAdjunction A B) : (f : B ⥤ A).IsLeftAdjoint :=
  f.adjunction.isLeftAdjoint

/-- The inverse-image functor in a left-exact adjunction preserves finite limits. -/
instance (f : LeftExactAdjunction A B) : PreservesFiniteLimits (f : B ⥤ A) :=
  inferInstance

instance (f : LeftExactAdjunction A B) : HasInverseImage f where
  Inv := B ⥤ A
  inverseImage := f.inverseImage

instance (f : LeftExactAdjunction A B) : HasPushforward f where
  Push := A ⥤ B
  pushforward := f.pushforward

/-- The identity left-exact adjunction on a category. -/
def id (C : Type u₁) [Category.{v₁} C] : LeftExactAdjunction C C where
  inverseImageFunctor := LeftExactFunctor.of (𝟭 _)
  pushforward := 𝟭 _
  adjunction := Adjunction.id

/-- Composition of left-exact adjunctions, with direct image `f_* ∘ g_*` and inverse image
`g⁻¹ ∘ f⁻¹`. -/
def comp (f : LeftExactAdjunction B C) (g : LeftExactAdjunction A B) : LeftExactAdjunction A C where
  inverseImageFunctor := LeftExactFunctor.of (f.inverseImage ⋙ g.inverseImage)
  pushforward := g.pushforward ⋙ f.pushforward
  adjunction := f.adjunction.comp g.adjunction

end LeftExactAdjunction

/-- Definition 7.15.1 specialized to the topoi of set-valued sheaves on two sites. -/
abbrev MorphismOfTopoiIn
    {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) :=
  LeftExactAdjunction (Sheaf K (Type w)) (Sheaf J (Type w))

namespace MorphismOfTopoiIn

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]
variable {J : GrothendieckTopology C}
variable {K : GrothendieckTopology D}
variable {L : GrothendieckTopology E}

/- Textbook notation for the inverse-image functor of a morphism of topoi. -/
scoped notation:100 f "⁻¹" => CategoryTheory.inverseImage f

/- Lean notation for the direct-image functor of a morphism of topoi, corresponding to textbook
`f_*`. Because `_` is part of identifiers, the parser surface is `f _*` or `(f)_*`. -/
scoped notation:100 f "_*" => CategoryTheory.pushforward f

end MorphismOfTopoiIn

open scoped MorphismOfTopoiIn

namespace Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

section

variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [u.IsContinuous J K]
variable [HasWeakSheafify K (Type w)]
variable [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
variable [PreservesFiniteLimits (u.sheafPullback (Type w) J K)]

/-- A continuous functor of sites whose induced pullback on set-valued sheaves preserves finite
limits determines a morphism of topoi. -/
noncomputable def morphismOfTopoiInOfContinuous
    : MorphismOfTopoiIn J K where
  inverseImageFunctor := LeftExactFunctor.of (u.sheafPullback (Type w) J K)
  pushforward := u.sheafPushforwardContinuous (Type w) J K
  adjunction := u.sheafAdjunctionContinuous (Type w) J K

/-- The inverse-image functor of `morphismOfTopoiInOfContinuous` is the usual continuous sheaf
pullback functor. -/
@[simp] theorem morphismOfTopoiInOfContinuous_inverseImage
    : (u.morphismOfTopoiInOfContinuous J K)⁻¹ =
      u.sheafPullback (Type w) J K := rfl

/-- The direct-image functor of `morphismOfTopoiInOfContinuous` is the usual continuous sheaf
pushforward functor. -/
@[simp] theorem morphismOfTopoiInOfContinuous_pushforward
    : (u.morphismOfTopoiInOfContinuous J K) _* =
      u.sheafPushforwardContinuous (Type w) J K := rfl

end

end Functor

namespace MorphismOfTopoiIn

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]
variable {J : GrothendieckTopology C}
variable {K : GrothendieckTopology D}
variable {L : GrothendieckTopology E}

/-- The identity morphism of the topos `Sh(J)`. -/
abbrev id (J : GrothendieckTopology C) : MorphismOfTopoiIn J J :=
  LeftExactAdjunction.id (Sheaf J (Type w))

/-- Composition of morphisms of topoi, with direct image `f_* ∘ g_*` and inverse image
`g⁻¹ ∘ f⁻¹`. -/
abbrev comp (f : MorphismOfTopoiIn J K) (g : MorphismOfTopoiIn K L) :
    MorphismOfTopoiIn J L :=
  LeftExactAdjunction.comp f g

/-- The base change morphism attached to a commutative inverse-image square of morphisms of
topoi. In Lean's left-to-right functor composition notation, its source is `f_* ⋙ g⁻¹` and its
target is `(g')⁻¹ ⋙ f'_*`. -/
abbrev baseChange
    {B' : Type u₁} [Category.{v₁} B']
    {B : Type u₂} [Category.{v₂} B]
    {C' : Type u₃} [Category.{v₃} C']
    {C : Type u₄} [Category.{v₄} C]
    {JB' : GrothendieckTopology B'}
    {JB : GrothendieckTopology B}
    {JC' : GrothendieckTopology C'}
    {JC : GrothendieckTopology C}
    (right : MorphismOfTopoiIn JC JC')
    (bottom : MorphismOfTopoiIn JB' JC')
    (top : MorphismOfTopoiIn JB JC)
    (left : MorphismOfTopoiIn JB JB')
    (sq : TwoSquare (left⁻¹) (top⁻¹) (bottom⁻¹) (right⁻¹)) :
    (top _*) ⋙ left⁻¹ ⟶ right⁻¹ ⋙ (bottom _*) :=
  (mateEquiv top.adjunction bottom.adjunction sq).natTrans

end MorphismOfTopoiIn

end CategoryTheory
